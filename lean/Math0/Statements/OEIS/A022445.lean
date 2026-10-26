/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A022445: self-avoiding closed walks in the strip `{0, 1, 2} × ℤ`

Source: https://oeis.org/A022445, _Ralf Stephan_, Apr 28 2004 (FORMULA section; the entry is by
Jacques Labelle, more terms by _Sean A. Irvine_, May 16 2019). Verbatim:
> G.f.: (-6*x^7+10*x^6-18*x^5+27*x^4-14*x^3+10*x^2-4*x+1) / ((1+x^2)^2*(1-2*x)^2)
> (conjectured). - _Ralf Stephan_, Apr 28 2004

The entry's name: "Number of self-avoiding closed walks (from 0 to 0) of length 2n in the strip
{0, 1, 2} X Z of the square lattice Z X Z." Offset `0`; data `1, 0, 4, 10, 34, 94, 222, …`
(29 terms, `a(0), …, a(28)`).

## Encoding

* *Walks.* A walk of length `m` in the square lattice `ℤ × ℤ` starting at the origin
  `0 = (0, 0)` is given by its sequence of unit steps `t : Fin m → Fin 4`, step `j` being
  `step (t j)` (right, left, up or down). Its vertices are
  `vertex t i = step (t 0) + ⋯ + step (t (i - 1))` for `0 ≤ i ≤ m`. This is a bijection between
  step sequences and lattice walks of length `m` from `0`.
* *The strip* `{0, 1, 2} × ℤ` is `InStrip v ↔ 0 ≤ v.1 ≤ 2`. The walks go "from 0 to 0", and the
  origin lies on the boundary column `0` of the strip. (The data confirm this reading: there are
  `a(2) = 4` walks of length `4`, two unit squares at `0` with two directions each; from a vertex
  of the middle column there would be `8`.)
* *Self-avoiding closed walks* (`IsClosedSAW t`, `m = 2n`), with vertices `w i = vertex t i`:
  - all vertices `w 0, …, w m` lie in the strip;
  - the walk is closed, `w m = 0`;
  - the vertices `w 0, …, w (m - 1)` are pairwise distinct (the only repeated vertex is
    `w m = w 0`);
  - the `m` edges `{w i, w (i + 1)}` are pairwise distinct (no edge is traversed twice).
  For `m ≠ 2` the edge condition follows from the vertex condition (`closed_iff_ext`). Its only
  effect is to exclude the degenerate walks `0 → v → 0` of length `2`, which retrace their edge;
  this agrees with the listed `a(1) = 0`. For `m ≥ 4`, each cycle of length `m` through `0` in
  the strip gives exactly two such walks, one for each direction. For `m = 0` the empty walk is
  counted, so `a(0) = 1`.
* `a n` is the number of such walks of length `2n`, a `Fintype.card` of a decidable subtype of
  `Fin (2n) → Fin 4`.
* *Fast evaluation (proved equal).* The kernel cannot enumerate `4^(2n)` step sequences, so the
  data are checked through a depth-first search `aFast`, with `a_eq_aFast : a n = aFast n` for
  every `n`. The search extends the walk one step at a time, never revisiting a vertex (except
  for the final return to `0`). It prunes a branch when the `ℓ¹`-distance to the origin exceeds
  the number of remaining steps (`G_succ`, `G_eq_zero`). The vertex `(c, r - R)` of the strip is
  encoded by the natural numbers `(c, r)` (offset `R = 2n`), and the set of visited vertices by a
  bitmask (bit `3r + c`). `dfs_eq` proves that the search computes the numbers `G` of
  completions of a partial walk.
* *Data.* `a_data` checks the first 10 listed terms `a(0), …, a(9)` in the kernel (about 45 s).
  The search visits about `6 · 10⁴` nodes for these, and each further term costs about 2.5 times
  as much as the previous one.
* *The conjecture* (`statement`): the generating function `∑_{n ≥ 0} a(n) xⁿ` equals
  `(-6x⁷ + 10x⁶ - 18x⁵ + 27x⁴ - 14x³ + 10x² - 4x + 1) / ((1 + x²)² (1 - 2x)²)`. It is stated
  over `ℤ` after clearing the denominator. The denominator has constant term `1`, so it is a unit
  in `ℤ⟦X⟧` and this is equivalent to the stated quotient. As a sanity check of the transcription
  (not a proof), `listed_satisfy_gf` checks that the 29 listed terms agree with the coefficients
  of the conjectured rational function.
-/

namespace Math0.Statements.A022445

/-! ### The definition -/

/-- The four unit steps of the square lattice `ℤ × ℤ`: right, left, up, down. -/
def step : Fin 4 → ℤ × ℤ := ![(1, 0), (-1, 0), (0, 1), (0, -1)]

/-- The vertex reached after the first `i` steps of the walk that starts at the origin and whose
`j`-th step (`j < m`) is `step (t j)`, i.e. the sum of the first `i` steps (for `i ≥ m`, the
endpoint of the walk). -/
def vertex {m : ℕ} (t : Fin m → Fin 4) (i : ℕ) : ℤ × ℤ :=
  ∑ j : Fin m, if (j : ℕ) < i then step (t j) else 0

/-- The strip `{0, 1, 2} × ℤ` of the square lattice. -/
def InStrip (v : ℤ × ℤ) : Prop := 0 ≤ v.1 ∧ v.1 ≤ 2

instance : DecidablePred InStrip := fun v => by unfold InStrip; infer_instance

/-- The walk from the origin with steps `t` (vertices `w i = vertex t i`, `0 ≤ i ≤ m`) is a
self-avoiding closed walk from `0` to `0` in the strip: all its vertices lie in the strip, it
returns to `0`, the vertices `w 0, …, w (m - 1)` are pairwise distinct, and its edges
`{w i, w (i + 1)}` (`i < m`) are pairwise distinct. -/
def IsClosedSAW {m : ℕ} (t : Fin m → Fin 4) : Prop :=
  (∀ i < m + 1, InStrip (vertex t i)) ∧ vertex t m = 0 ∧
    (∀ j < m, ∀ i < j, vertex t i ≠ vertex t j) ∧
    (∀ j < m, ∀ i < j, s(vertex t i, vertex t (i + 1)) ≠ s(vertex t j, vertex t (j + 1)))

instance {m : ℕ} : DecidablePred (@IsClosedSAW m) := fun t => by
  unfold IsClosedSAW; infer_instance

/-- A022445: the number of self-avoiding closed walks (from `0` to `0`) of length `2n` in the strip
`{0, 1, 2} × ℤ` of the square lattice. -/
def a (n : ℕ) : ℕ := Fintype.card {t : Fin (2 * n) → Fin 4 // IsClosedSAW t}

/-! ### Counting extensions of a partial walk step by step -/

theorem vertex_zero {m : ℕ} (t : Fin m → Fin 4) : vertex t 0 = 0 := by
  simp [vertex]

theorem vertex_fin_zero (t : Fin 0 → Fin 4) (i : ℕ) : vertex t i = 0 := by
  simp [vertex]

theorem vertex_cons_succ {k : ℕ} (d : Fin 4) (t : Fin k → Fin 4) (i : ℕ) :
    vertex (Fin.cons d t : Fin (k + 1) → Fin 4) (i + 1) = step d + vertex t i := by
  simp [vertex, Fin.sum_univ_succ]

/-- `Ext vis p t`: the walk that starts at `p` and makes the steps `t` (vertices
`p + vertex t i`, `0 ≤ i ≤ k`) has its vertices `1, …, k` in the strip, ends at `0`, and its
vertices `1, …, k - 1` are pairwise distinct and not in `vis`. -/
def Ext (vis : List (ℤ × ℤ)) (p : ℤ × ℤ) {k : ℕ} (t : Fin k → Fin 4) : Prop :=
  (∀ i, 1 ≤ i → i ≤ k → InStrip (p + vertex t i)) ∧ p + vertex t k = 0 ∧
    (∀ i, 1 ≤ i → i < k → p + vertex t i ∉ vis) ∧
    (∀ i j, 1 ≤ i → i < j → j < k → p + vertex t i ≠ p + vertex t j)

/-- The number of ways to complete a partial walk at `p` with visited vertices `vis` by `k` more
steps. -/
noncomputable def G (vis : List (ℤ × ℤ)) (p : ℤ × ℤ) (k : ℕ) : ℕ :=
  Nat.card {t : Fin k → Fin 4 // Ext vis p t}

theorem ext_cons (vis : List (ℤ × ℤ)) (p : ℤ × ℤ) {k : ℕ} (d : Fin 4) (t : Fin k → Fin 4) :
    Ext vis p (Fin.cons d t : Fin (k + 1) → Fin 4) ↔
      InStrip (p + step d) ∧ (k ≠ 0 → p + step d ∉ vis) ∧
        Ext ((p + step d) :: vis) (p + step d) t := by
  have hv : ∀ i, p + vertex (Fin.cons d t : Fin (k + 1) → Fin 4) (i + 1) =
      p + step d + vertex t i := by
    intro i; rw [vertex_cons_succ, add_assoc]
  have hv0 : vertex t 0 = 0 := vertex_zero t
  unfold Ext
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, fun hk => ?_, fun i hi1 hik => ?_, ?_, fun i hi1 hik hmem => ?_,
      fun i j hi hij hjk => ?_⟩
    · have := h1 (0 + 1) (by omega) (by omega); rwa [hv, hv0, add_zero] at this
    · have := h3 (0 + 1) (by omega) (by omega); rwa [hv, hv0, add_zero] at this
    · have := h1 (i + 1) (by omega) (by omega); rwa [hv] at this
    · have := h2; rwa [hv] at this
    · rcases List.mem_cons.1 hmem with h | h
      · have := h4 (0 + 1) (i + 1) (by omega) (by omega) (by omega)
        rw [hv, hv, hv0, add_zero] at this
        exact this h.symm
      · have := h3 (i + 1) (by omega) (by omega); rw [hv] at this; exact this h
    · have := h4 (i + 1) (j + 1) (by omega) (by omega) (by omega)
      rwa [hv, hv] at this
  · rintro ⟨hq, hqv, g1, g2, g3, g4⟩
    refine ⟨fun i hi1 hik => ?_, ?_, fun i hi1 hik => ?_, fun i j hi1 hij hjk => ?_⟩
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [hv]
      rcases Nat.eq_zero_or_pos i' with rfl | hi
      · rwa [hv0, add_zero]
      · exact g1 i' hi (by omega)
    · rw [hv]; exact g2
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [hv]
      rcases Nat.eq_zero_or_pos i' with rfl | hi
      · rw [hv0, add_zero]; exact hqv (by omega)
      · exact fun h => g3 i' hi (by omega) (List.mem_cons_of_mem _ h)
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [hv, hv]
      rcases Nat.eq_zero_or_pos i' with rfl | hi
      · rw [hv0, add_zero]
        intro h
        apply g3 j' (by omega) (by omega)
        rw [← h]
        exact List.mem_cons_self
      · exact g4 i' j' hi (by omega) (by omega)

theorem G_zero (vis : List (ℤ × ℤ)) (p : ℤ × ℤ) : G vis p 0 = if p = 0 then 1 else 0 := by
  unfold G
  have hE : ∀ t : Fin 0 → Fin 4, Ext vis p t ↔ p = 0 := by
    intro t
    simp only [Ext, vertex_fin_zero, add_zero]
    constructor
    · exact fun h => h.2.1
    · intro h
      exact ⟨fun i h1 h2 => by omega, h, fun i h1 h2 => by omega, fun i j h1 h2 h3 => by omega⟩
  split_ifs with hp
  · rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩, ⟨⟨Fin.elim0, (hE _).2 hp⟩⟩⟩
  · rw [Nat.card_eq_zero]
    left
    exact ⟨fun ⟨t, ht⟩ => hp ((hE t).1 ht)⟩

theorem G_succ (vis : List (ℤ × ℤ)) (p : ℤ × ℤ) (k : ℕ) :
    G vis p (k + 1) = ∑ d : Fin 4,
      if InStrip (p + step d) ∧ (k ≠ 0 → p + step d ∉ vis) then
        G ((p + step d) :: vis) (p + step d) k else 0 := by
  unfold G
  let e : {t : Fin (k + 1) → Fin 4 // Ext vis p t} ≃
      Σ d : Fin 4, {t : Fin k → Fin 4 // Ext vis p (Fin.cons d t : Fin (k + 1) → Fin 4)} :=
    ((Fin.consEquiv fun _ => Fin 4).symm.subtypeEquiv
      (q := fun x : Fin 4 × (Fin k → Fin 4) => Ext vis p (Fin.cons x.1 x.2 : Fin (k + 1) → Fin 4))
      (fun t => by simp)).trans
      (Equiv.subtypeProdEquivSigmaSubtype fun d t => Ext vis p (Fin.cons d t : Fin (k + 1) → Fin 4))
  rw [Nat.card_congr e, Nat.card_sigma]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs with h
  · exact Nat.card_congr (Equiv.subtypeEquivRight fun t => by rw [ext_cons]; tauto)
  · rw [Nat.card_eq_zero]
    left
    exact ⟨fun ⟨t, ht⟩ => h (by rw [ext_cons] at ht; exact ⟨ht.1, ht.2.1⟩)⟩

/-- The `ℓ¹`-distance from the origin. -/
def dist (v : ℤ × ℤ) : ℕ := v.1.natAbs + v.2.natAbs

theorem dist_le_step (p : ℤ × ℤ) (d : Fin 4) : dist p ≤ dist (p + step d) + 1 := by
  fin_cases d <;> simp [dist, step] <;> omega

theorem dist_le_of_ext (vis : List (ℤ × ℤ)) (p : ℤ × ℤ) {k : ℕ} (t : Fin k → Fin 4)
    (h : Ext vis p t) : dist p ≤ k := by
  induction k generalizing vis p with
  | zero =>
    have h2 := h.2.1
    rw [vertex_zero, add_zero] at h2
    simp [h2, dist]
  | succ k ih =>
    rw [← Fin.cons_self_tail t, ext_cons] at h
    have := ih _ _ _ h.2.2
    have := dist_le_step p (t 0)
    omega

theorem G_eq_zero (vis : List (ℤ × ℤ)) (p : ℤ × ℤ) (k : ℕ) (h : k < dist p) : G vis p k = 0 := by
  unfold G
  rw [Nat.card_eq_zero]
  left
  exact ⟨fun ⟨t, ht⟩ => absurd (dist_le_of_ext vis p t ht) (by omega)⟩

/-! ### Self-avoiding closed walks are the complete extensions of the empty walk -/

theorem closed_iff_ext {m : ℕ} (hm : m ≠ 2) (t : Fin m → Fin 4) :
    IsClosedSAW t ↔ Ext [0] 0 t := by
  simp only [IsClosedSAW, Ext, zero_add, List.mem_singleton]
  have h0 : vertex t 0 = 0 := vertex_zero t
  constructor
  · rintro ⟨h1, h2, h3, -⟩
    refine ⟨fun i _ hi => h1 i (by omega), h2, fun i hi1 hi => ?_,
      fun i j hi hij hj => h3 j hj i hij⟩
    have := h3 i hi 0 (by omega)
    rw [h0] at this
    exact fun h => this h.symm
  · rintro ⟨h1, h2, h3, h4⟩
    have hd : ∀ j < m, ∀ i < j, vertex t i ≠ vertex t j := by
      intro j hj i hij
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · rw [h0]; exact fun h => h3 j (by omega) hj h.symm
      · exact h4 i j hi hij hj
    refine ⟨fun i hi => ?_, h2, hd, fun j hj i hij he => ?_⟩
    · rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [h0]; exact ⟨le_rfl, by norm_num⟩
      · exact h1 i hi0 (by omega)
    · rw [Sym2.eq_iff] at he
      rcases he with ⟨he1, -⟩ | ⟨he1, he2⟩
      · exact hd j hj i hij he1
      · have hj' : j = i + 1 := by
          by_contra hne
          exact hd j hj (i + 1) (by omega) he2
        subst hj'
        by_cases hlt : i + 1 + 1 < m
        · exact hd (i + 1 + 1) hlt i (by omega) he1
        · have hm2 : i + 1 + 1 = m := by omega
          rw [hm2, h2] at he1
          rcases Nat.eq_zero_or_pos i with rfl | hi0
          · omega
          · exact hd i (by omega) 0 hi0 (by rw [h0, he1])

theorem a_one : a 1 = 0 := by
  unfold a
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun ⟨t, ht⟩ => ?_⟩
  obtain ⟨-, h2, -, h4⟩ := ht
  apply h4 1 (by norm_num) 0 (by norm_num)
  have h2' : vertex t (1 + 1) = 0 := h2
  rw [vertex_zero, h2']
  exact Sym2.eq_swap

theorem a_eq_G (n : ℕ) (hn : n ≠ 1) : a n = G [0] 0 (2 * n) := by
  unfold a G
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun t => closed_iff_ext (by omega) t)

/-! ### Fast evaluation: depth-first search with a bitmask -/

/-- One move of the depth-first search, to the strip vertex `(c, r - R)` (column `c`, row `r - R`),
with `k` steps left after the move. The visited vertices form the bitmask `vis` (vertex
`(c, r - R)` ↦ bit `3 r + c`). The branch is pruned if the vertex is farther than `k` from the
origin, or if it was already visited (unless it is the final step). -/
def move (R k : ℕ) (ih : ℕ → ℕ → ℕ → ℕ) (vis c r : ℕ) : ℕ :=
  cond (Nat.ble (Nat.add (Nat.add c (Nat.sub r R)) (Nat.sub R r)) k &&
      (Nat.beq k 0 || !(Nat.testBit vis (Nat.add (Nat.mul 3 r) c))))
    (ih c r (Nat.lor vis (Nat.pow 2 (Nat.add (Nat.mul 3 r) c)))) 0

/-- One level of the depth-first search from `(c, r - R)`: the moves right, left, up, down
(staying in the strip and in `r ≥ 0`). -/
def dfsStep (R k : ℕ) (ih : ℕ → ℕ → ℕ → ℕ) (c r vis : ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.add
    (cond (Nat.blt c 2) (move R k ih vis (Nat.add c 1) r) 0)
    (cond (Nat.blt 0 c) (move R k ih vis (Nat.sub c 1) r) 0))
    (move R k ih vis c (Nat.add r 1)))
    (cond (Nat.blt 0 r) (move R k ih vis c (Nat.sub r 1)) 0)

/-- `dfs R k c r vis`: the number of ways to complete the partial walk at `(c, r - R)` with
visited set `vis` by `k` more steps (`dfs_eq`). -/
def dfs (R k : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ)
    (fun c r _ => cond (Nat.beq c 0 && Nat.beq r R) 1 0) (fun k ih => dfsStep R k ih) k

/-- Fast evaluation of `a` (`a_eq_aFast`). -/
def aFast (n : ℕ) : ℕ :=
  if n = 1 then 0 else dfs (2 * n) (2 * n) 0 (2 * n) (2 ^ (3 * (2 * n)))

/-- Decoding of the bit index `v = 3 r + c` as the lattice point `(c, r - R)`. -/
def dec (R v : ℕ) : ℤ × ℤ := (((v % 3 : ℕ) : ℤ), ((v / 3 : ℕ) : ℤ) - R)

theorem dec_inj (R : ℕ) {v w : ℕ} (h : dec R v = dec R w) : v = w := by
  simp only [dec, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have h1' : v % 3 = w % 3 := by exact_mod_cast h1
  have h2' : v / 3 = w / 3 := by omega
  omega

theorem dec_code (R c r : ℕ) (hc : c < 3) : dec R (3 * r + c) = ((c : ℤ), (r : ℤ) - R) := by
  have h1 : (3 * r + c) % 3 = c := by omega
  have h2 : (3 * r + c) / 3 = r := by omega
  simp [dec, h1, h2]

theorem ble_eq_decide (a b : ℕ) : Nat.ble a b = decide (a ≤ b) :=
  Bool.eq_iff_iff.2 (by rw [Nat.ble_eq, decide_eq_true_iff])

theorem beq_eq_decide (a b : ℕ) : Nat.beq a b = decide (a = b) :=
  Bool.eq_iff_iff.2 (by rw [Nat.beq_eq, decide_eq_true_iff])

theorem blt_eq_decide (a b : ℕ) : Nat.blt a b = decide (a < b) :=
  Bool.eq_iff_iff.2 (by rw [Nat.blt_eq, decide_eq_true_iff])

theorem dfs_eq (R : ℕ) : ∀ k c r visN (visZ : List (ℤ × ℤ)), c ≤ 2 → k ≤ R →
    (∀ v, Nat.testBit visN v = true ↔ dec R v ∈ visZ) →
    dfs R k c r visN = G visZ ((c : ℤ), (r : ℤ) - R) k := by
  intro k
  induction k with
  | zero =>
    intro c r visN visZ hc hk hrel
    rw [G_zero]
    show cond (Nat.beq c 0 && Nat.beq r R) 1 0 = _
    rw [beq_eq_decide, beq_eq_decide, ← Bool.decide_and, Bool.cond_decide]
    have : (c = 0 ∧ r = R) ↔ ((c : ℤ), (r : ℤ) - R) = 0 := by
      rw [Prod.ext_iff]; simp only [Prod.fst_zero, Prod.snd_zero]; omega
    exact if_congr this rfl rfl
  | succ k ih =>
    intro c r visN visZ hc hk hrel
    have hmove : ∀ c' r' : ℕ, c' ≤ 2 → ∀ q : ℤ × ℤ, q = ((c' : ℤ), (r' : ℤ) - R) →
        move R k (dfs R k) visN c' r' =
          if InStrip q ∧ (k ≠ 0 → q ∉ visZ) then G (q :: visZ) q k else 0 := by
      intro c' r' hc' q hq
      have hstrip : InStrip q := by rw [hq]; exact ⟨by simp, by simp; omega⟩
      have hdist : c' + (r' - R) + (R - r') = dist q := by rw [hq]; simp [dist]; omega
      have hcq : dec R (3 * r' + c') = q := by rw [dec_code R c' r' (by omega), hq]
      have htb : Nat.testBit visN (3 * r' + c') = decide (q ∈ visZ) :=
        Bool.eq_iff_iff.2 (by rw [hrel, hcq, decide_eq_true_iff])
      have hrel' : ∀ v, Nat.testBit (visN ||| 2 ^ (3 * r' + c')) v = true ↔
          dec R v ∈ q :: visZ := by
        intro v
        rw [Nat.testBit_or, Bool.or_eq_true, hrel, Nat.testBit_two_pow, decide_eq_true_iff,
          List.mem_cons]
        constructor
        · rintro (h | rfl)
          · exact Or.inr h
          · exact Or.inl hcq
        · rintro (h | h)
          · exact Or.inr (dec_inj R (h.trans hcq.symm)).symm
          · exact Or.inl h
      have hih := ih c' r' _ (q :: visZ) hc' (by omega) hrel'
      rw [← hq] at hih
      unfold move
      simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.pow_eq, Nat.lor_eq]
      rw [ble_eq_decide, beq_eq_decide, htb, hdist]
      simp only [← decide_not, ← Bool.decide_or, ← Bool.decide_and, Bool.cond_decide]
      split_ifs with h1 h2 h2
      · exact hih
      · exfalso
        exact h2 ⟨hstrip, fun hk0 => h1.2.resolve_left hk0⟩
      · by_cases hd : dist q ≤ k
        · exfalso
          apply h1
          refine ⟨hd, ?_⟩
          by_cases hk0 : k = 0
          · exact Or.inl hk0
          · exact Or.inr (h2.2 hk0)
        · rw [G_eq_zero _ _ _ (by omega)]
      · rfl
    show dfsStep R k (dfs R k) c r visN = _
    rw [G_succ, Fin.sum_univ_four]
    unfold dfsStep
    simp only [Nat.add_eq, Nat.sub_eq]
    have hs0 : step 0 = (1, 0) := rfl
    have hs1 : step 1 = (-1, 0) := rfl
    have hs2 : step 2 = (0, 1) := rfl
    have hs3 : step 3 = (0, -1) := rfl
    simp only [hs0, hs1, hs2, hs3, Prod.mk_add_mk, add_zero]
    congr 1
    congr 1
    congr 1
    · -- right
      by_cases h : c < 2
      · rw [show Nat.blt c 2 = true by rw [blt_eq_decide]; simpa using h, cond_true]
        exact hmove (c + 1) r (by omega) _ (by rw [Prod.mk.injEq]; omega)
      · rw [show Nat.blt c 2 = false by rw [blt_eq_decide]; simpa using h, cond_false, if_neg]
        rintro ⟨⟨-, h2⟩, -⟩
        dsimp only at h2
        omega
    · -- left
      by_cases h : 0 < c
      · rw [show Nat.blt 0 c = true by rw [blt_eq_decide]; simpa using h, cond_true]
        exact hmove (c - 1) r (by omega) _ (by rw [Prod.mk.injEq]; omega)
      · rw [show Nat.blt 0 c = false by rw [blt_eq_decide]; simpa using h, cond_false, if_neg]
        rintro ⟨⟨h1, -⟩, -⟩
        dsimp only at h1
        omega
    · -- up
      exact hmove c (r + 1) hc _ (by rw [Prod.mk.injEq]; omega)
    · -- down
      by_cases h : 0 < r
      · rw [show Nat.blt 0 r = true by rw [blt_eq_decide]; simpa using h, cond_true]
        exact hmove c (r - 1) hc _ (by rw [Prod.mk.injEq]; omega)
      · rw [show Nat.blt 0 r = false by rw [blt_eq_decide]; simpa using h, cond_false]
        have hr : r = 0 := by omega
        subst hr
        split_ifs
        · rw [G_eq_zero]
          simp only [dist]
          omega
        · rfl

theorem aFast_eq_G (n : ℕ) (hn : n ≠ 1) : aFast n = G [0] 0 (2 * n) := by
  unfold aFast
  rw [if_neg hn]
  have h := dfs_eq (2 * n) (2 * n) 0 (2 * n) (2 ^ (3 * (2 * n))) [0] (by norm_num) le_rfl ?_
  · rw [h]
    congr 1
    simp
  · intro v
    rw [Nat.testBit_two_pow, List.mem_singleton, decide_eq_true_iff]
    have hc := dec_code (2 * n) 0 (2 * n) (by norm_num)
    simp only [add_zero, Nat.cast_zero, sub_self] at hc
    constructor
    · rintro rfl
      rw [hc]; rfl
    · intro h
      apply dec_inj (2 * n)
      rw [hc, h]; rfl

theorem a_eq_aFast (n : ℕ) : a n = aFast n := by
  by_cases hn : n = 1
  · subst hn; rw [a_one]; rfl
  · rw [a_eq_G n hn, aFast_eq_G n hn]

/-- The definition reproduces the first 10 listed terms `a(0), …, a(9)` (kernel-checked). -/
theorem a_data : (List.range 10).map a = [1, 0, 4, 10, 34, 94, 222, 516, 1202, 2738] := by
  rw [show a = aFast from funext a_eq_aFast]
  decide +kernel

/-! ### The conjecture -/

open PowerSeries in
/-- Ralf Stephan's conjecture: the generating function of A022445 is
`∑_{n ≥ 0} a(n) xⁿ = (-6x⁷ + 10x⁶ - 18x⁵ + 27x⁴ - 14x³ + 10x² - 4x + 1) / ((1 + x²)² (1 - 2x)²)`,
stated as an identity of formal power series over `ℤ` after clearing the denominator (which has
constant term `1`, hence is a unit in `ℤ⟦X⟧`). -/
def statement : Prop :=
  PowerSeries.mk (fun n => (a n : ℤ)) * ((1 + X ^ 2) ^ 2 * (1 - 2 * X) ^ 2) =
    -6 * X ^ 7 + 10 * X ^ 6 - 18 * X ^ 5 + 27 * X ^ 4 - 14 * X ^ 3 + 10 * X ^ 2 - 4 * X + 1

/-! ### Sanity check of the transcription (not a proof) -/

open PowerSeries in
/-- The expanded denominator. -/
theorem denominator_expand :
    ((1 + X ^ 2) ^ 2 * (1 - 2 * X) ^ 2 : PowerSeries ℤ) =
      1 - 4 * X + 6 * X ^ 2 - 8 * X ^ 3 + 9 * X ^ 4 - 4 * X ^ 5 + 4 * X ^ 6 := by
  ring

/-- The 29 terms listed in the entry, `a(0), …, a(28)`. -/
def listed : List ℤ :=
  [1, 0, 4, 10, 34, 94, 222, 516, 1202, 2738, 6110, 13496, 29586, 64350, 139006, 298636, 638578,
    1359754, 2884638, 6099552, 12859730, 27040694, 56723774, 118732340, 248034354, 517208034,
    1076694622, 2237946376, 4645007122]

/-- Coefficients of the expanded denominator (`denominator_expand`). -/
def denC : List ℤ := [1, -4, 6, -8, 9, -4, 4]

/-- Coefficients of the conjectured numerator, `1 - 4x + 10x² - 14x³ + 27x⁴ - 18x⁵ + 10x⁶ - 6x⁷`. -/
def numC : List ℤ := [1, -4, 10, -14, 27, -18, 10, -6]

/-- The listed terms agree with the coefficients of the conjectured rational function: for
`n ≤ 28`, the coefficient of `xⁿ` in `(∑ listed(i) xⁱ) · (1 + x²)² (1 - 2x)²` is that of the
numerator. -/
theorem listed_satisfy_gf : ∀ n < 29,
    ((List.range (n + 1)).map fun i => denC.getD i 0 * listed.getD (n - i) 0).sum =
      numC.getD n 0 := by
  decide +kernel

end Math0.Statements.A022445
