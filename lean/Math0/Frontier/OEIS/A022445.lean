/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A022445
import Math0.Audit

/-!
# The generating function of A022445 (closed self-avoiding walks in the strip `{0,1,2} × ℤ`)

We prove Ralf Stephan's conjecture
`∑ a(n) xⁿ = (1 - 4x + 10x² - 14x³ + 27x⁴ - 18x⁵ + 10x⁶ - 6x⁷) / ((1 + x²)² (1 - 2x)²)`.

**Walks as lists.** `a n` (`n ≠ 1`) counts the lists of vertices `0, w₁, …, w_{2n-1}, 0` of
closed walks in the strip whose inner vertices are distinct and differ from `0` (`a_eq_GLs`).
Dropping the final `0`, these are the self-avoiding walks of `2n - 1` steps from the origin to one
of its three neighbours `(1, 0)`, `(0, 1)`, `(0, -1)` (`GLs_Q`).

**Cuts.** A self-avoiding walk in the strip crosses a horizontal cut (between two adjacent rows)
along vertical edges in distinct columns. If it starts on one side and ends on the other, it
crosses only once as soon as one of the three columns is unavailable (`once`); if it starts and
ends on the same side, it leaves that side at most once (`conv`).

**Excursions.** An *excursion* (`exc σ r S c₁ c₂ ℓ`) is a self-avoiding walk of `ℓ` steps in the
half-strip on side `σ` of row `r`, from column `c₁` to column `c₂` of row `r`, avoiding the
columns `S` of row `r`. By `conv`, it is either a straight horizontal segment, or a segment in
row `r`, an excursion from the next row, and a segment in row `r` (`exc_decomp`). Hence the
numbers of excursions satisfy a finite linear recursion (`exc_card`): their number is `Ef c₁ c₂ ℓ`,
with `p ℓ` excursions between adjacent columns and `q ℓ` between columns `0` and `2`, where
`p (ℓ + 3) = p (ℓ + 1) + q ℓ`, `q (ℓ + 3) = 2 p ℓ + q (ℓ + 1)`.

**Decomposition.** By `once`, a walk from `0` to `(0, ±1)` is an excursion from `0` on the side
of row `0` away from `(0, ±1)`, followed by an excursion beyond row `±1` (`Q1_card`). A walk from
`0` to `(1, 0)` first steps to `(0, ±1)`, makes an excursion beyond row `±1`, and ends with an
excursion on the other side of row `0` that avoids the origin (`Q10_card`).

**Generating functions.** `p` lives on odd and `q` on even lengths; with
`P(x) = ∑ p(2m+1) xᵐ`, `Q(x) = ∑ q(2m) xᵐ` one has `P = 1 + x (P + Q)`, `Q = x (1 + Q + 2xP)`,
so `(1 - 2x)(1 + x²) P = 1 - x + x²` and `(1 - 2x)(1 + x²) Q = x + x²`. The decomposition gives
`∑ a(n) xⁿ = 1 + 2 (x² P² + x Q² + x² P + x² Q + x³ P Q)` (`a_formula`), and clearing
denominators yields the claimed identity (`gf_main`).
-/

namespace Math0.Frontier.A022445
open Math0.Statements.A022445

/-- Adjacency in the square lattice: `v` is one unit step from `u`. -/
private def Adj (u v : ℤ × ℤ) : Prop := ∃ d : Fin 4, v = u + step d

/-- Coordinates of adjacent vertices. -/
private lemma adj_iff {u v : ℤ × ℤ} : Adj u v ↔
    (v.1 = u.1 + 1 ∧ v.2 = u.2) ∨ (v.1 = u.1 - 1 ∧ v.2 = u.2) ∨
      (v.1 = u.1 ∧ v.2 = u.2 + 1) ∨ (v.1 = u.1 ∧ v.2 = u.2 - 1) := by
  constructor
  · rintro ⟨d, rfl⟩
    fin_cases d <;> simp [step] <;> omega
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨0, Prod.ext (by simp [step, h1]) (by simp [step, h2])⟩
    · exact ⟨1, Prod.ext (by simp [step, h1]; ring) (by simp [step, h2])⟩
    · exact ⟨2, Prod.ext (by simp [step, h1]) (by simp [step, h2])⟩
    · exact ⟨3, Prod.ext (by simp [step, h1]) (by simp [step, h2]; ring)⟩

/-- Adjacency is symmetric. -/
private lemma adj_symm {u v : ℤ × ℤ} (h : Adj u v) : Adj v u := by
  rw [adj_iff] at h ⊢; omega

/-- All walks of `k` steps from `p`, as lists of their `k + 1` vertices. -/
private def walksFrom : ℤ × ℤ → ℕ → Finset (List (ℤ × ℤ))
  | p, 0 => {[p]}
  | p, k + 1 => Finset.univ.biUnion fun d : Fin 4 => (walksFrom (p + step d) k).image (List.cons p)

/-- Membership in `walksFrom`. -/
private lemma mem_walksFrom {k : ℕ} {p : ℤ × ℤ} {l : List (ℤ × ℤ)} :
    l ∈ walksFrom p k ↔ l.length = k + 1 ∧ l.head? = some p ∧ l.IsChain Adj := by
  induction k generalizing p l with
  | zero =>
    simp only [walksFrom, Finset.mem_singleton, zero_add]
    constructor
    · rintro rfl; simp
    · rintro ⟨hl, hh, -⟩
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hl
      simp at hh; rw [hh]
  | succ k ih =>
    simp only [walksFrom, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image, ih]
    constructor
    · rintro ⟨d, l', ⟨hlen, hhead, hc⟩, rfl⟩
      refine ⟨by simp [hlen], rfl, hc.cons fun y hy => ⟨d, ?_⟩⟩
      rw [hhead] at hy; cases hy; rfl
    · rintro ⟨hlen, hhead, hc⟩
      match l, hlen, hhead, hc with
      | a :: b :: l'', hlen, hhead, hc =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst hhead
        obtain ⟨d, hd⟩ := (List.isChain_cons_cons.1 hc).1
        exact ⟨d, b :: l'', ⟨by simpa using hlen, by simp [hd], (List.isChain_cons_cons.1 hc).2⟩,
          rfl⟩

/-- List version of `Ext`: the walk `W` (its vertex list, starting at `p`) has its vertices
`1, …, k` in the strip, ends at `0`, and its vertices `1, …, k - 1` are distinct and not in
`vis`. -/
private def ExtL (vis : List (ℤ × ℤ)) (W : List (ℤ × ℤ)) : Prop :=
  (∀ v ∈ W.tail, InStrip v) ∧ W.getLast? = some 0 ∧ (∀ v ∈ W.tail.dropLast, v ∉ vis) ∧
    W.tail.dropLast.Nodup

/-- Decidability of `ExtL`. -/
private instance (vis : List (ℤ × ℤ)) : DecidablePred (ExtL vis) := fun W => by
  unfold ExtL; infer_instance

/-- List version of `G`. -/
private def GLs (vis : List (ℤ × ℤ)) (p : ℤ × ℤ) (k : ℕ) : ℕ :=
  ((walksFrom p k).filter (ExtL vis)).card

/-- `GLs` with no steps left. -/
private lemma GLs_zero (vis : List (ℤ × ℤ)) (p : ℤ × ℤ) : GLs vis p 0 = if p = 0 then 1 else 0 := by
  unfold GLs
  rw [walksFrom, Finset.filter_singleton]
  by_cases hp : p = 0 <;> simp [ExtL, hp]

/-- Unfolding `ExtL` by one step. -/
private lemma extL_cons (vis : List (ℤ × ℤ)) (p q : ℤ × ℤ) (R : List (ℤ × ℤ)) :
    ExtL vis (p :: q :: R) ↔
      InStrip q ∧ (R.length ≠ 0 → q ∉ vis) ∧ ExtL (q :: vis) (q :: R) := by
  cases R with
  | nil => simp [ExtL]
  | cons r R =>
    simp only [ExtL, List.tail_cons, List.mem_cons, List.getLast?_cons_cons,
      List.dropLast_cons_cons, List.nodup_cons, List.length_cons, ne_eq, Nat.add_one_ne_zero,
      not_false_eq_true, forall_const, forall_eq_or_imp, not_or]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, ⟨h4, h5⟩, h6, h7⟩
      exact ⟨h1, h4, h2, h3, fun v hv => ⟨fun e => h6 (e ▸ hv), h5 v hv⟩, h7⟩
    · rintro ⟨h1, h4, h2, h3, h5, h7⟩
      exact ⟨⟨h1, h2⟩, h3, ⟨h4, fun v hv => (h5 v hv).2⟩, fun hm => (h5 q hm).1 rfl, h7⟩

/-- The four unit steps are distinct. -/
private lemma step_inj {d d' : Fin 4} (h : step d = step d') : d = d' := by
  fin_cases d <;> fin_cases d' <;> simp_all [step]

/-- `GLs` satisfies the same one-step recursion as `G`. -/
private lemma GLs_succ (vis : List (ℤ × ℤ)) (p : ℤ × ℤ) (k : ℕ) :
    GLs vis p (k + 1) = ∑ d : Fin 4,
      if InStrip (p + step d) ∧ (k ≠ 0 → p + step d ∉ vis) then
        GLs ((p + step d) :: vis) (p + step d) k else 0 := by
  unfold GLs
  rw [walksFrom, Finset.filter_biUnion, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.filter_image, Finset.card_image_of_injective _ List.cons_injective]
    split_ifs with h
    · congr 1
      apply Finset.filter_congr
      intro W hW
      obtain ⟨hlen, hhead, -⟩ := mem_walksFrom.1 hW
      match W, hlen, hhead with
      | q :: R, hlen, hhead =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst hhead
        simp only [List.length_cons, add_left_inj] at hlen
        rw [extL_cons, hlen]
        exact ⟨fun h' => h'.2.2, fun h' => ⟨h.1, h.2, h'⟩⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro W hW hE
      obtain ⟨hlen, hhead, -⟩ := mem_walksFrom.1 hW
      match W, hlen, hhead with
      | q :: R, hlen, hhead =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst hhead
        simp only [List.length_cons, add_left_inj] at hlen
        rw [extL_cons, hlen] at hE
        exact h ⟨hE.1, hE.2.1⟩
  · intro d _ d' _ hdd'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro l h1 h2
    simp only [Finset.mem_filter, Finset.mem_image] at h1 h2
    obtain ⟨⟨W, hW, rfl⟩, -⟩ := h1
    obtain ⟨⟨W', hW', hWW⟩, -⟩ := h2
    obtain ⟨-, h1, -⟩ := mem_walksFrom.1 hW
    obtain ⟨-, h2, -⟩ := mem_walksFrom.1 hW'
    have : W' = W := List.cons_injective hWW
    subst this
    rw [h1, Option.some.injEq] at h2
    exact hdd' (step_inj (add_left_cancel h2))

/-- `G` agrees with its list version `GLs`. -/
private lemma G_eq_GLs (k : ℕ) : ∀ (vis : List (ℤ × ℤ)) (p : ℤ × ℤ), G vis p k = GLs vis p k := by
  induction k with
  | zero => intro vis p; rw [G_zero, GLs_zero]
  | succ k ih => intro vis p; rw [G_succ, GLs_succ]; simp only [ih]

/-- `a n` counts lists of vertices (`n ≠ 1`). -/
private lemma a_eq_GLs (n : ℕ) (hn : n ≠ 1) : a n = GLs [0] 0 (2 * n) := by
  rw [a_eq_G n hn, G_eq_GLs]


/-! ### Crossing a horizontal cut -/

/-- Elements of the two parts of a duplicate-free concatenation differ. -/
private lemma nodup_ne {L1 L2 : List (ℤ × ℤ)} (hn : (L1 ++ L2).Nodup) {a b : ℤ × ℤ}
    (ha : a ∈ L1) (hb : b ∈ L2) : a ≠ b :=
  (List.nodup_append.1 hn).2.2 a ha b hb

/-- The last vertex of the first part of a walk is adjacent to the first vertex of the second. -/
private lemma adj_junction {L1 L2 : List (ℤ × ℤ)} (hc : (L1 ++ L2).IsChain Adj) (h1 : L1 ≠ [])
    (h2 : L2 ≠ []) : Adj (L1.getLast h1) (L2.head h2) :=
  hc.rel_getLast_head_of_append h1 h2

/-- A self-avoiding walk in the strip that starts on the `q`-side of a horizontal cut and ends on
the other side crosses the cut only once, provided some crossing column `c` is not available
(one of `(c, ρ1)`, `(c, ρ2)` is not on the walk): three crossings would use three distinct
columns, i.e. all of them. -/
private lemma once (q : ℤ × ℤ → Bool) (ρ1 ρ2 : ℤ)
    (hq : ∀ a b, Adj a b → q a = true → q b = false → a.1 = b.1 ∧ a.2 = ρ1 ∧ b.2 = ρ2)
    {l : List (ℤ × ℤ)} (hc : l.IsChain Adj) (hn : l.Nodup) (hs : ∀ v ∈ l, InStrip v)
    (hmiss : ∃ c : ℤ, 0 ≤ c ∧ c ≤ 2 ∧ ((c, ρ1) ∉ l ∨ (c, ρ2) ∉ l))
    (hh : ∀ v ∈ l.head?, q v = true) (hl : ∀ v ∈ l.getLast?, q v = false) :
    ∀ v ∈ l.dropWhile q, q v = false := by
  intro v hv
  by_contra hqv
  rw [Bool.not_eq_false] at hqv
  obtain ⟨A, hA⟩ : ∃ A, A = l.takeWhile q := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = l.dropWhile q := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, X = R.takeWhile (fun v => !q v) := ⟨_, rfl⟩
  obtain ⟨R', hR'⟩ : ∃ R', R' = R.dropWhile (fun v => !q v) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = R'.takeWhile q := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = R'.dropWhile q := ⟨_, rfl⟩
  rw [← hR] at hv
  have hlAR : l = A ++ R := by rw [hA, hR, List.takeWhile_append_dropWhile]
  have hRXR : R = X ++ R' := by rw [hX, hR', List.takeWhile_append_dropWhile]
  have hRYZ : R' = Y ++ Z := by rw [hY, hZ, List.takeWhile_append_dropWhile]
  have hl4 : l = A ++ X ++ Y ++ Z := by rw [hlAR, hRXR, hRYZ]; simp
  have hAq : ∀ w ∈ A, q w = true := fun w hw => by rw [hA] at hw; exact List.mem_takeWhile_imp hw
  have hXq : ∀ w ∈ X, q w = false := fun w hw => by
    rw [hX] at hw; simpa using List.mem_takeWhile_imp hw
  have hYq : ∀ w ∈ Y, q w = true := fun w hw => by rw [hY] at hw; exact List.mem_takeWhile_imp hw
  have hRne : R ≠ [] := List.ne_nil_of_mem hv
  have hlne : l ≠ [] := by rintro rfl; simp [hR] at hRne
  have hAne : A ≠ [] := by
    obtain ⟨a, l', rfl⟩ := List.exists_cons_of_ne_nil hlne
    have : q a = true := hh a (by simp)
    rw [hA, List.takeWhile_cons_of_pos this]; simp
  have hXne : X ≠ [] := by
    have h0 := List.head_dropWhile_not q (hR ▸ hRne)
    obtain ⟨r, R0, hr⟩ := List.exists_cons_of_ne_nil hRne
    have : q r = false := by
      have e : (l.dropWhile q).head (hR ▸ hRne) = r := by simp [← hR, hr]
      rwa [e] at h0
    rw [hX, hr, List.takeWhile_cons_of_pos (by simp [this])]; simp
  have hvR' : v ∈ R' := by
    rw [hRXR, List.mem_append] at hv
    rcases hv with h | h
    · have := hXq v h; rw [hqv] at this; exact absurd this (by simp)
    · exact h
  have hR'ne : R' ≠ [] := List.ne_nil_of_mem hvR'
  have hYne : Y ≠ [] := by
    have h0 := List.head_dropWhile_not (fun v => !q v) (hR' ▸ hR'ne)
    obtain ⟨r, R0, hr⟩ := List.exists_cons_of_ne_nil hR'ne
    have : q r = true := by
      have e : (R.dropWhile (fun v => !q v)).head (hR' ▸ hR'ne) = r := by simp [← hR', hr]
      rw [e] at h0; simpa using h0
    rw [hY, hr, List.takeWhile_cons_of_pos this]; simp
  have hZne : Z ≠ [] := by
    intro hZ0
    have hlast : l.getLast? = Y.getLast? := by
      rw [hl4, hZ0, List.append_nil, List.getLast?_append_of_ne_nil _ hYne]
    obtain ⟨y, hy⟩ : ∃ y, Y.getLast? = some y := Option.isSome_iff_exists.1 (by simpa using hYne)
    have h1 := hl y (by rw [hlast, hy]; rfl)
    have h2 := hYq y (List.mem_of_getLast? hy)
    rw [h1] at h2; exact absurd h2 (by simp)
  have hZq : q (Z.head hZne) = false := by
    have h0 := List.head_dropWhile_not q (hZ ▸ hZne)
    have e : (R'.dropWhile q).head (hZ ▸ hZne) = Z.head hZne := by simp [hZ]
    rwa [e] at h0
  -- the three crossings
  have hc1 : Adj (A.getLast hAne) (X.head hXne) := by
    have h := adj_junction (L1 := A) (L2 := X ++ Y ++ Z) (by rw [hl4] at hc; simpa using hc)
      hAne (by simp [hXne])
    rwa [List.head_append_of_ne_nil (by simp [hXne]), List.head_append_of_ne_nil hXne] at h
  have hc2 : Adj (X.getLast hXne) (Y.head hYne) := by
    have h := adj_junction (L1 := A ++ X) (L2 := Y ++ Z) (by rw [hl4] at hc; simpa using hc)
      (by simp [hXne]) (by simp [hYne])
    rwa [List.head_append_of_ne_nil hYne, List.getLast_append_of_ne_nil _ hXne] at h
  have hc3 : Adj (Y.getLast hYne) (Z.head hZne) := by
    have h := adj_junction (L1 := A ++ X ++ Y) (L2 := Z) (by rw [hl4] at hc; simpa using hc)
      (by simp [hYne]) hZne
    rwa [List.getLast_append_of_ne_nil _ hYne] at h
  obtain ⟨e1, e1a, e1b⟩ := hq _ _ hc1 (hAq _ (List.getLast_mem _)) (hXq _ (List.head_mem _))
  obtain ⟨e2, e2a, e2b⟩ := hq _ _ (adj_symm hc2) (hYq _ (List.head_mem _))
    (hXq _ (List.getLast_mem _))
  obtain ⟨e3, e3a, e3b⟩ := hq _ _ hc3 (hYq _ (List.getLast_mem _)) hZq
  -- distinctness
  have hn1 : (A ++ (X ++ Y ++ Z)).Nodup := by rw [hl4] at hn; simpa using hn
  have hn2 : ((A ++ X) ++ (Y ++ Z)).Nodup := by rw [hl4] at hn; simpa using hn
  have d1 : A.getLast hAne ≠ Y.head hYne :=
    nodup_ne hn1 (List.getLast_mem _) (by simp [List.head_mem])
  have d2 : A.getLast hAne ≠ Y.getLast hYne :=
    nodup_ne hn1 (List.getLast_mem _) (by simp [List.getLast_mem])
  have d3 : X.getLast hXne ≠ Z.head hZne :=
    nodup_ne hn2 (by simp [List.getLast_mem]) (by simp [List.head_mem])
  have memA : ∀ w ∈ A, w ∈ l := fun w hw => by rw [hl4]; simp [hw]
  have memX : ∀ w ∈ X, w ∈ l := fun w hw => by rw [hl4]; simp [hw]
  have memY : ∀ w ∈ Y, w ∈ l := fun w hw => by rw [hl4]; simp [hw]
  have memZ : ∀ w ∈ Z, w ∈ l := fun w hw => by rw [hl4]; simp [hw]
  have s1 := hs _ (memA _ (List.getLast_mem hAne))
  have s2 := hs _ (memY _ (List.head_mem hYne))
  have s3 := hs _ (memY _ (List.getLast_mem hYne))
  unfold InStrip at s1 s2 s3
  have n12 : (A.getLast hAne).1 ≠ (Y.head hYne).1 := fun h => d1 (Prod.ext h (by rw [e1a, e2a]))
  have n13 : (A.getLast hAne).1 ≠ (Y.getLast hYne).1 := fun h => d2 (Prod.ext h (by rw [e1a, e3a]))
  have n23 : (Y.head hYne).1 ≠ (Y.getLast hYne).1 := fun h =>
    d3 (Prod.ext (by rw [← e2, h, e3]) (by rw [e2b, e3b]))
  obtain ⟨c, hc0, hc2', hcm⟩ := hmiss
  have key : c = (A.getLast hAne).1 ∨ c = (Y.head hYne).1 ∨ c = (Y.getLast hYne).1 := by omega
  rcases key with h | h | h
  · rcases hcm with hm | hm
    · exact hm (by rw [h, ← e1a]; exact memA _ (List.getLast_mem _))
    · exact hm (by rw [h, e1, ← e1b]; exact memX _ (List.head_mem _))
  · rcases hcm with hm | hm
    · exact hm (by rw [h, ← e2a]; exact memY _ (List.head_mem _))
    · exact hm (by rw [h, e2, ← e2b]; exact memX _ (List.getLast_mem _))
  · rcases hcm with hm | hm
    · exact hm (by rw [h, ← e3a]; exact memY _ (List.getLast_mem _))
    · exact hm (by rw [h, e3, ← e3b]; exact memZ _ (List.head_mem _))


/-- A self-avoiding walk in the strip that starts and ends on the `q`-side of a horizontal cut
leaves that side at most once. -/
private lemma conv (q : ℤ × ℤ → Bool) (ρ1 ρ2 : ℤ)
    (hq : ∀ a b, Adj a b → q a = true → q b = false → a.1 = b.1 ∧ a.2 = ρ1 ∧ b.2 = ρ2)
    {l : List (ℤ × ℤ)} (hc : l.IsChain Adj) (hn : l.Nodup) (hs : ∀ v ∈ l, InStrip v)
    (hh : ∀ v ∈ l.head?, q v = true) (hl : ∀ v ∈ l.getLast?, q v = true) :
    ∀ v ∈ (l.dropWhile q).dropWhile (fun v => !q v), q v = true := by
  intro v hv
  obtain ⟨A, hA⟩ : ∃ A, A = l.takeWhile q := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = l.dropWhile q := ⟨_, rfl⟩
  rw [← hR] at hv
  have hlAR : l = A ++ R := by rw [hA, hR, List.takeWhile_append_dropWhile]
  have hAq : ∀ w ∈ A, q w = true := fun w hw => by rw [hA] at hw; exact List.mem_takeWhile_imp hw
  have hRne : R ≠ [] := by rintro rfl; simp at hv
  have hlne : l ≠ [] := by rintro rfl; simp [hR] at hRne
  have hAne : A ≠ [] := by
    obtain ⟨a, l', rfl⟩ := List.exists_cons_of_ne_nil hlne
    have : q a = true := hh a (by simp)
    rw [hA, List.takeWhile_cons_of_pos this]; simp
  have hRq : q (R.head hRne) = false := by
    have h0 := List.head_dropWhile_not q (hR ▸ hRne)
    have e : (l.dropWhile q).head (hR ▸ hRne) = R.head hRne := by simp [hR]
    rwa [e] at h0
  have hc' : (A ++ R).IsChain Adj := hlAR ▸ hc
  have hn' : (A ++ R).Nodup := hlAR ▸ hn
  have hc1 : Adj (A.getLast hAne) (R.head hRne) := adj_junction hc' hAne hRne
  obtain ⟨-, e1a, -⟩ := hq _ _ hc1 (hAq _ (List.getLast_mem _)) hRq
  have hmissR : ((A.getLast hAne).1, ρ1) ∉ R := by
    intro hm
    exact nodup_ne hn' (List.getLast_mem hAne) hm (Prod.ext rfl e1a)
  have s1 := hs _ (by rw [hlAR]; exact List.mem_append_left _ (List.getLast_mem hAne))
  unfold InStrip at s1
  have key := once (fun v => !q v) ρ2 ρ1
    (fun a b hab ha hb => by
      obtain ⟨h1, h2, h3⟩ := hq b a (adj_symm hab) (by simpa using hb) (by simpa using ha)
      exact ⟨h1.symm, h3, h2⟩)
    hc'.right_of_append (List.nodup_append.1 hn').2.1
    (fun w hw => hs w (by rw [hlAR]; exact List.mem_append_right _ hw))
    ⟨_, s1.1, s1.2, Or.inr hmissR⟩
    (fun w hw => by
      rw [List.head?_eq_some_head hRne, Option.mem_def, Option.some.injEq] at hw
      subst hw; simp [hRq])
    (fun w hw => by
      have : w ∈ l.getLast? := by rw [hlAR, List.getLast?_append_of_ne_nil _ hRne]; exact hw
      simp [hl w this])
    v hv
  simpa using key

/-- Decomposition form of `once`. -/
private lemma once_split (q : ℤ × ℤ → Bool) (ρ1 ρ2 : ℤ)
    (hq : ∀ a b, Adj a b → q a = true → q b = false → a.1 = b.1 ∧ a.2 = ρ1 ∧ b.2 = ρ2)
    {l : List (ℤ × ℤ)} (hc : l.IsChain Adj) (hn : l.Nodup) (hs : ∀ v ∈ l, InStrip v)
    (hmiss : ∃ c : ℤ, 0 ≤ c ∧ c ≤ 2 ∧ ((c, ρ1) ∉ l ∨ (c, ρ2) ∉ l))
    (hh : ∀ v ∈ l.head?, q v = true) (hl : ∀ v ∈ l.getLast?, q v = false) :
    ∃ A B, l = A ++ B ∧ (∀ v ∈ A, q v = true) ∧ (∀ v ∈ B, q v = false) :=
  ⟨l.takeWhile q, l.dropWhile q, List.takeWhile_append_dropWhile.symm,
    fun _ hv => List.mem_takeWhile_imp hv, once q ρ1 ρ2 hq hc hn hs hmiss hh hl⟩

/-- Decomposition form of `conv`. -/
private lemma conv_split (q : ℤ × ℤ → Bool) (ρ1 ρ2 : ℤ)
    (hq : ∀ a b, Adj a b → q a = true → q b = false → a.1 = b.1 ∧ a.2 = ρ1 ∧ b.2 = ρ2)
    {l : List (ℤ × ℤ)} (hc : l.IsChain Adj) (hn : l.Nodup) (hs : ∀ v ∈ l, InStrip v)
    (hh : ∀ v ∈ l.head?, q v = true) (hl : ∀ v ∈ l.getLast?, q v = true) :
    ∃ A X B, l = A ++ X ++ B ∧ (∀ v ∈ A, q v = true) ∧ (∀ v ∈ X, q v = false) ∧
      (∀ v ∈ B, q v = true) :=
  ⟨l.takeWhile q, (l.dropWhile q).takeWhile (fun v => !q v),
    (l.dropWhile q).dropWhile (fun v => !q v),
    by rw [List.append_assoc, List.takeWhile_append_dropWhile, List.takeWhile_append_dropWhile],
    fun _ hv => List.mem_takeWhile_imp hv,
    fun _ hv => by simpa using List.mem_takeWhile_imp hv,
    conv q ρ1 ρ2 hq hc hn hs hh hl⟩

/-! ### Half-strips and horizontal segments -/

/-- `+1` (up) or `-1` (down). -/
private def dir : Bool → ℤ
  | true => 1
  | false => -1

/-- `v` lies on side `σ` of row `r` (row `r` included): above it for `σ = true`. -/
private def onSide (σ : Bool) (r : ℤ) (v : ℤ × ℤ) : Prop := if σ then r ≤ v.2 else v.2 ≤ r

/-- Decidability of `onSide`. -/
private instance (σ : Bool) (r : ℤ) (v : ℤ × ℤ) : Decidable (onSide σ r v) := by
  unfold onSide; split <;> infer_instance

/-- `v` is not strictly beyond row `r` on side `σ`. -/
private def near (σ : Bool) (r : ℤ) (v : ℤ × ℤ) : Bool :=
  if σ then decide (v.2 ≤ r) else decide (r ≤ v.2)

/-- A unit step from `near` to not `near` crosses between rows `r` and `r + dir σ` vertically. -/
private lemma near_hq (σ : Bool) (r : ℤ) (a b : ℤ × ℤ) (hab : Adj a b) (ha : near σ r a = true)
    (hb : near σ r b = false) : a.1 = b.1 ∧ a.2 = r ∧ b.2 = r + dir σ := by
  rw [adj_iff] at hab
  cases σ <;> simp [near, dir] at ha hb ⊢ <;> omega

/-- The decomposition of a self-avoiding walk in a half-strip from row `r` to row `r`: a piece in
row `r`, an excursion strictly beyond row `r` (possibly empty), and a piece in row `r`. -/
private lemma half_split (σ : Bool) (r : ℤ) {l : List (ℤ × ℤ)} (hc : l.IsChain Adj)
    (hn : l.Nodup) (hs : ∀ v ∈ l, InStrip v ∧ onSide σ r v) (hh : ∀ v ∈ l.head?, v.2 = r)
    (hl : ∀ v ∈ l.getLast?, v.2 = r) :
    ∃ A X B, l = A ++ X ++ B ∧ (∀ v ∈ A, v.2 = r) ∧
      (∀ v ∈ X, v.2 ≠ r ∧ onSide σ (r + dir σ) v) ∧ (∀ v ∈ B, v.2 = r) := by
  have hnear : ∀ v, onSide σ r v → (near σ r v = true ↔ v.2 = r) := by
    intro v hv; cases σ <;> simp [near, onSide] at hv ⊢ <;> omega
  have hfar : ∀ v, onSide σ r v → near σ r v = false → v.2 ≠ r ∧ onSide σ (r + dir σ) v := by
    intro v hv hf; cases σ <;> simp [near, onSide, dir] at hv hf ⊢ <;> omega
  obtain ⟨A, X, B, hl3, hA, hX, hB⟩ := conv_split (near σ r) r (r + dir σ) (near_hq σ r) hc hn
    (fun v hv => (hs v hv).1)
    (fun v hv => (hnear v (hs v (List.mem_of_mem_head? hv)).2).2 (hh v hv))
    (fun v hv => (hnear v (hs v (List.mem_of_getLast? hv)).2).2 (hl v hv))
  have mem : ∀ v, v ∈ A ∨ v ∈ X ∨ v ∈ B → v ∈ l := fun v hv => by
    rw [hl3]; simp only [List.mem_append]; tauto
  exact ⟨A, X, B, hl3, fun v hv => (hnear v (hs v (mem v (Or.inl hv))).2).1 (hA v hv),
    fun v hv => hfar v (hs v (mem v (Or.inr (Or.inl hv)))).2 (hX v hv),
    fun v hv => (hnear v (hs v (mem v (Or.inr (Or.inr hv)))).2).1 (hB v hv)⟩


/-- The columns of the horizontal segment from column `a` to column `b`, in order. -/
private def cols (a b : Fin 3) : List (Fin 3) :=
  ![![[0], [0, 1], [0, 1, 2]], ![[1, 0], [1], [1, 2]], ![[2, 1, 0], [2, 1], [2]]] a b

/-- A column as an integer. -/
private def ci (c : Fin 3) : ℤ := ((c : ℕ) : ℤ)

/-- An integer in `[0, 2]` as a column. -/
private def colOf (z : ℤ) : Fin 3 := ⟨z.toNat % 3, Nat.mod_lt _ (by norm_num)⟩

/-- Columns lie in `[0, 2]`. -/
private lemma ci_bounds (c : Fin 3) : 0 ≤ ci c ∧ ci c ≤ 2 := by
  have := c.isLt; unfold ci; omega

/-- `colOf` inverts `ci`. -/
private lemma colOf_ci (c : Fin 3) : colOf (ci c) = c := by
  apply Fin.ext; simp [colOf, ci]

/-- `ci` inverts `colOf` on `[0, 2]`. -/
private lemma ci_colOf {z : ℤ} (h0 : 0 ≤ z) (h2 : z ≤ 2) : ci (colOf z) = z := by
  simp only [ci, colOf]; omega

/-- `ci` is injective. -/
private lemma ci_inj {a b : Fin 3} (h : ci a = ci b) : a = b := by
  rw [← colOf_ci a, h, colOf_ci]

/-- The horizontal segment in row `r` from column `a` to column `b`. -/
private def hseg (r : ℤ) (a b : Fin 3) : List (ℤ × ℤ) := (cols a b).map fun c => (ci c, r)

/-- Membership in a horizontal segment. -/
private lemma mem_hseg {r : ℤ} {a b : Fin 3} {v : ℤ × ℤ} :
    v ∈ hseg r a b ↔ ∃ c ∈ cols a b, v = (ci c, r) := by
  simp [hseg, eq_comm]

/-- A horizontal segment lies in its row and in the strip. -/
private lemma hseg_row {r : ℤ} {a b : Fin 3} {v : ℤ × ℤ} (hv : v ∈ hseg r a b) :
    v.2 = r ∧ InStrip v := by
  obtain ⟨c, -, rfl⟩ := mem_hseg.1 hv
  exact ⟨rfl, ci_bounds c⟩

/-- A horizontal segment is nonempty. -/
private lemma hseg_ne_nil (r : ℤ) (a b : Fin 3) : hseg r a b ≠ [] := by
  fin_cases a <;> fin_cases b <;> simp [hseg, cols]

/-- The first vertex of a horizontal segment. -/
private lemma hseg_head? (r : ℤ) (a b : Fin 3) : (hseg r a b).head? = some (ci a, r) := by
  fin_cases a <;> fin_cases b <;> simp [hseg, cols]

/-- The last vertex of a horizontal segment. -/
private lemma hseg_getLast? (r : ℤ) (a b : Fin 3) : (hseg r a b).getLast? = some (ci b, r) := by
  fin_cases a <;> fin_cases b <;> simp [hseg, cols]

/-- The length of a horizontal segment. -/
private lemma hseg_length (r : ℤ) (a b : Fin 3) : (hseg r a b).length = (cols a b).length := by
  simp [hseg]

/-- A segment has at least one column. -/
private lemma cols_length_pos (a b : Fin 3) : 1 ≤ (cols a b).length := by
  fin_cases a <;> fin_cases b <;> simp [cols]

/-- A horizontal segment is a walk. -/
private lemma hseg_chain (r : ℤ) (a b : Fin 3) : (hseg r a b).IsChain Adj := by
  fin_cases a <;> fin_cases b <;> simp [hseg, cols, ci, adj_iff]

/-- Placing columns in a row is injective. -/
private lemma hseg_map_inj (r : ℤ) : Function.Injective fun c : Fin 3 => (ci c, r) :=
  fun _ _ h => ci_inj (Prod.mk.inj h).1

/-- Two segments in the same row are disjoint iff their column lists are. -/
private lemma hseg_append_nodup {r : ℤ} {a b c d : Fin 3} :
    (hseg r a b ++ hseg r c d).Nodup ↔ (cols a b ++ cols c d).Nodup := by
  rw [hseg, hseg, ← List.map_append, List.nodup_map_iff (hseg_map_inj r)]

/-- A horizontal segment has no repeated vertex. -/
private lemma hseg_nodup (r : ℤ) (a b : Fin 3) : (hseg r a b).Nodup := by
  rw [hseg, List.nodup_map_iff (hseg_map_inj r)]
  fin_cases a <;> fin_cases b <;> decide

/-- A self-avoiding walk inside a row is the horizontal segment between its ends. -/
private lemma row_unique {r : ℤ} {l : List (ℤ × ℤ)} (hne : l ≠ [])
    (hrow : ∀ v ∈ l, v.2 = r ∧ InStrip v) (hn : l.Nodup) (hc : l.IsChain Adj) :
    l = hseg r (colOf (l.head hne).1) (colOf (l.getLast hne).1) := by
  have key : ∀ v ∈ l, v.2 = r ∧ 0 ≤ v.1 ∧ v.1 ≤ 2 := fun v hv =>
    ⟨(hrow v hv).1, (hrow v hv).2.1, (hrow v hv).2.2⟩
  match l, hne, key, hn, hc with
  | [(a1, a2)], _, key, _, _ =>
    obtain ⟨ha, h0, h2⟩ := key (a1, a2) (by simp)
    simp only at ha h0 h2
    subst ha
    simp only [List.head_cons, List.getLast_singleton]
    obtain h | h | h : a1 = 0 ∨ a1 = 1 ∨ a1 = 2 := by omega
    all_goals subst h; simp [hseg, cols, colOf, ci]
  | [(a1, a2), (b1, b2)], _, key, _, hc =>
    obtain ⟨ha, ha0, ha2⟩ := key (a1, a2) (by simp)
    obtain ⟨hb, hb0, hb2⟩ := key (b1, b2) (by simp)
    have hab := (List.isChain_cons_cons.1 hc).1
    rw [adj_iff] at hab
    simp only at ha hb ha0 ha2 hb0 hb2 hab
    subst ha hb
    simp only [List.head_cons, List.getLast_cons_cons, List.getLast_singleton]
    obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ :
        (a1 = 0 ∧ b1 = 1) ∨ (a1 = 1 ∧ b1 = 0) ∨ (a1 = 1 ∧ b1 = 2) ∨ (a1 = 2 ∧ b1 = 1) := by
      omega
    all_goals subst h1 h2; simp [hseg, cols, colOf, ci]
  | [(a1, a2), (b1, b2), (c1, c2)], _, key, hn, hc =>
    obtain ⟨ha, ha0, ha2⟩ := key (a1, a2) (by simp)
    obtain ⟨hb, hb0, hb2⟩ := key (b1, b2) (by simp)
    obtain ⟨hc', hc0, hc2⟩ := key (c1, c2) (by simp)
    have hab := (List.isChain_cons_cons.1 hc).1
    have hbc := (List.isChain_cons_cons.1 (List.isChain_cons_cons.1 hc).2).1
    have hac : (a1, a2) ≠ (c1, c2) := by simp only [List.nodup_cons] at hn; simp_all
    rw [adj_iff] at hab hbc
    simp only at ha hb hc' ha0 ha2 hb0 hb2 hc0 hc2 hab hbc
    subst ha hb hc'
    have hac' : a1 ≠ c1 := fun h => hac (by rw [h])
    simp only [List.head_cons, List.getLast_cons_cons, List.getLast_singleton]
    obtain ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ :
        (a1 = 0 ∧ b1 = 1 ∧ c1 = 2) ∨ (a1 = 2 ∧ b1 = 1 ∧ c1 = 0) := by omega
    all_goals subst h1 h2 h3; simp [hseg, cols, colOf, ci]
  | a :: b :: c :: d :: t, _, key, hn, _ =>
    exfalso
    obtain ⟨ha, ha0, ha2⟩ := key a (by simp)
    obtain ⟨hb, hb0, hb2⟩ := key b (by simp)
    obtain ⟨hc', hc0, hc2⟩ := key c (by simp)
    obtain ⟨hd, hd0, hd2⟩ := key d (by simp)
    simp only [List.nodup_cons, List.mem_cons, not_or] at hn
    have n1 : a.1 ≠ b.1 := fun h => hn.1.1 (Prod.ext h (by rw [ha, hb]))
    have n2 : a.1 ≠ c.1 := fun h => hn.1.2.1 (Prod.ext h (by rw [ha, hc']))
    have n3 : a.1 ≠ d.1 := fun h => hn.1.2.2.1 (Prod.ext h (by rw [ha, hd]))
    have n4 : b.1 ≠ c.1 := fun h => hn.2.1.1 (Prod.ext h (by rw [hb, hc']))
    have n5 : b.1 ≠ d.1 := fun h => hn.2.1.2.1 (Prod.ext h (by rw [hb, hd]))
    have n6 : c.1 ≠ d.1 := fun h => hn.2.2.1.1 (Prod.ext h (by rw [hc', hd]))
    omega

/-! ### Counting excursions in a half-strip -/

/-- Counting a finset that is a disjoint union of injective images, the pieces being told apart
by a function `g`. -/
private lemma card_eq_sum {α β ι : Type} [DecidableEq α]
    (S : Finset α) (I : Finset ι) (T : ι → Finset β) (F : ι → β → α) (g : α → ι)
    (hinj : ∀ i ∈ I, ∀ x ∈ T i, ∀ y ∈ T i, F i x = F i y → x = y)
    (hg : ∀ i ∈ I, ∀ x ∈ T i, g (F i x) = i)
    (hS : ∀ a, a ∈ S ↔ ∃ i ∈ I, ∃ x ∈ T i, F i x = a) :
    S.card = ∑ i ∈ I, (T i).card := by
  have hS' : S = I.biUnion fun i => (T i).image (F i) := by
    ext a; rw [hS]; simp [Finset.mem_biUnion, Finset.mem_image]
  rw [hS', Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun i hi =>
      Finset.card_image_of_injOn fun x hx y hy h => hinj i hi x hx y hy h
  · intro i hi j hj hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_image] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, hyx⟩ := hb
    exact hij ((hg i hi x hx).symm.trans (hyx ▸ hg j hj y hy))

/-- Self-avoiding walks of `ℓ` steps in the half-strip on side `σ` of row `r`, from column `c1`
to column `c2` of row `r`, whose vertices in row `r` avoid the columns in `S`. -/
private def exc (σ : Bool) (r : ℤ) (S : Finset (Fin 3)) (c1 c2 : Fin 3) (ℓ : ℕ) :
    Finset (List (ℤ × ℤ)) :=
  (walksFrom (ci c1, r) ℓ).filter fun l => l.getLast? = some (ci c2, r) ∧ l.Nodup ∧
    ∀ v ∈ l, InStrip v ∧ onSide σ r v ∧ ∀ c ∈ S, v ≠ (ci c, r)

/-- Membership in `exc`. -/
private lemma mem_exc {σ : Bool} {r : ℤ} {S : Finset (Fin 3)} {c1 c2 : Fin 3} {ℓ : ℕ}
    {l : List (ℤ × ℤ)} : l ∈ exc σ r S c1 c2 ℓ ↔
      l.length = ℓ + 1 ∧ l.head? = some (ci c1, r) ∧ l.IsChain Adj ∧
        l.getLast? = some (ci c2, r) ∧ l.Nodup ∧
          ∀ v ∈ l, InStrip v ∧ onSide σ r v ∧ ∀ c ∈ S, v ≠ (ci c, r) := by
  simp only [exc, Finset.mem_filter, mem_walksFrom, and_assoc]

/-- The two end segments in row `r` are disjoint and avoid `S`. -/
private def okSeg (S : Finset (Fin 3)) (c1 c1' c2' c2 : Fin 3) : Prop :=
  (cols c1 c1' ++ cols c2' c2).Nodup ∧ ∀ c ∈ cols c1 c1' ++ cols c2' c2, c ∉ S

/-- Decidability of `okSeg`. -/
private instance (S : Finset (Fin 3)) (c1 c1' c2' c2 : Fin 3) :
    Decidable (okSeg S c1 c1' c2' c2) := by unfold okSeg; infer_instance

/-- Beyond row `r + dir σ` on side `σ` means on side `σ` of row `r`, off row `r`. -/
private lemma onSide_step {σ : Bool} {r : ℤ} {v : ℤ × ℤ} (h : onSide σ (r + dir σ) v) :
    onSide σ r v ∧ v.2 ≠ r := by
  cases σ <;> simp [onSide, dir] at h ⊢ <;> omega

/-- A vertical unit step towards side `σ`. -/
private lemma adj_vert (σ : Bool) (c r : ℤ) : Adj (c, r) (c, r + dir σ) := by
  rw [adj_iff]; cases σ <;> simp [dir, sub_eq_add_neg]

/-- Leaving row `r` from `(c, r)` to side `σ`. -/
private lemma adj_exit {σ : Bool} {r c : ℤ} {v : ℤ × ℤ} (h : Adj (c, r) v) (hv : v.2 ≠ r)
    (hs : onSide σ (r + dir σ) v) : v = (c, r + dir σ) := by
  rw [adj_iff] at h
  apply Prod.ext <;> cases σ <;> simp [onSide, dir] at h hs ⊢ <;> omega

/-- An excursion with its end segments is an excursion. -/
private lemma exc_build2 {σ : Bool} {r : ℤ} {S : Finset (Fin 3)} {c1 c2 c1' c2' : Fin 3} {ℓ : ℕ}
    (hok : okSeg S c1 c1' c2' c2) (hlen : (cols c1 c1').length + (cols c2' c2).length ≤ ℓ)
    {X : List (ℤ × ℤ)}
    (hX : X ∈ exc σ (r + dir σ) ∅ c1' c2' (ℓ - (cols c1 c1').length - (cols c2' c2).length)) :
    hseg r c1 c1' ++ X ++ hseg r c2' c2 ∈ exc σ r S c1 c2 ℓ := by
  obtain ⟨hXl, hXh, hXc, hXt, hXn, hXp⟩ := mem_exc.1 hX
  have hXne : X ≠ [] := by rintro rfl; simp at hXl
  rw [mem_exc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, hseg_length]; omega
  · rw [List.append_assoc, List.head?_append_of_ne_nil _ (hseg_ne_nil _ _ _), hseg_head?]
  · refine List.IsChain.append (List.IsChain.append (hseg_chain _ _ _) hXc ?_) (hseg_chain _ _ _) ?_
    · intro x hx y hy
      rw [hseg_getLast?, Option.mem_def, Option.some.injEq] at hx
      rw [hXh, Option.mem_def, Option.some.injEq] at hy
      subst hx hy; exact adj_vert σ _ _
    · intro x hx y hy
      rw [List.getLast?_append_of_ne_nil _ hXne, hXt, Option.mem_def, Option.some.injEq] at hx
      rw [hseg_head?, Option.mem_def, Option.some.injEq] at hy
      subst hx hy; exact adj_symm (adj_vert σ _ _)
  · rw [List.getLast?_append_of_ne_nil _ (hseg_ne_nil _ _ _), hseg_getLast?]
  · have h12 := (hseg_append_nodup (r := r)).2 hok.1
    rw [List.nodup_append] at h12 ⊢
    rw [List.nodup_append]
    refine ⟨⟨h12.1, hXn, fun a ha b hb hab => ?_⟩, h12.2.1, fun a ha b hb hab => ?_⟩
    · subst hab; exact (onSide_step (hXp a hb).2.1).2 (hseg_row ha).1
    · rw [List.mem_append] at ha
      rcases ha with ha | ha
      · exact h12.2.2 a ha b hb hab
      · subst hab; exact (onSide_step (hXp a ha).2.1).2 (hseg_row hb).1
  · intro v hv
    simp only [List.mem_append] at hv
    have hseg_case : ∀ a b, v ∈ hseg r a b → (∀ c ∈ cols a b, c ∉ S) →
        InStrip v ∧ onSide σ r v ∧ ∀ c ∈ S, v ≠ (ci c, r) := by
      intro a b hv' hS
      obtain ⟨c, hc, rfl⟩ := mem_hseg.1 hv'
      refine ⟨ci_bounds c, by cases σ <;> simp [onSide], fun c' hc' he => ?_⟩
      have := ci_inj (Prod.mk.inj he).1
      subst this; exact hS c hc hc'
    rcases hv with (hv | hv) | hv
    · exact hseg_case _ _ hv fun c hc => hok.2 c (List.mem_append_left _ hc)
    · obtain ⟨h1, h2, -⟩ := hXp v hv
      exact ⟨h1, (onSide_step h2).1, fun c _ he => (onSide_step h2).2 (by rw [he])⟩
    · exact hseg_case _ _ hv fun c hc => hok.2 c (List.mem_append_right _ hc)

/-- The straight segment is an excursion. -/
private lemma exc_build1 {σ : Bool} {r : ℤ} {S : Finset (Fin 3)} {c1 c2 : Fin 3} {ℓ : ℕ}
    (hlen : ℓ + 1 = (cols c1 c2).length) (hS : ∀ c ∈ cols c1 c2, c ∉ S) :
    hseg r c1 c2 ∈ exc σ r S c1 c2 ℓ := by
  rw [mem_exc]
  refine ⟨by rw [hseg_length, hlen], hseg_head? _ _ _, hseg_chain _ _ _, hseg_getLast? _ _ _,
    hseg_nodup _ _ _, fun v hv => ?_⟩
  obtain ⟨c, hc, rfl⟩ := mem_hseg.1 hv
  refine ⟨ci_bounds c, by cases σ <;> simp [onSide], fun c' hc' he => ?_⟩
  have := ci_inj (Prod.mk.inj he).1
  subst this; exact hS c hc hc'

/-- The structure of an excursion: straight, or two end segments around an excursion from the
next row. -/
private lemma exc_decomp {σ : Bool} {r : ℤ} {S : Finset (Fin 3)} {c1 c2 : Fin 3} {ℓ : ℕ}
    {l : List (ℤ × ℤ)} (hl : l ∈ exc σ r S c1 c2 ℓ) :
    (l = hseg r c1 c2 ∧ ℓ + 1 = (cols c1 c2).length ∧ ∀ c ∈ cols c1 c2, c ∉ S) ∨
      ∃ c1' c2' X, okSeg S c1 c1' c2' c2 ∧ (cols c1 c1').length + (cols c2' c2).length ≤ ℓ ∧
        X ∈ exc σ (r + dir σ) ∅ c1' c2' (ℓ - (cols c1 c1').length - (cols c2' c2).length) ∧
          l = hseg r c1 c1' ++ X ++ hseg r c2' c2 := by
  obtain ⟨hlen, hhead, hc, hlast, hn, hp⟩ := mem_exc.1 hl
  have hlne : l ≠ [] := by rintro rfl; simp at hlen
  obtain ⟨A, X, B, rfl, hA, hX, hB⟩ := half_split σ r hc hn (fun v hv => ⟨(hp v hv).1, (hp v hv).2.1⟩)
    (fun v hv => by rw [hhead, Option.mem_def, Option.some.injEq] at hv; rw [← hv])
    (fun v hv => by rw [hlast, Option.mem_def, Option.some.injEq] at hv; rw [← hv])
  have hheadv : (A ++ X ++ B).head hlne = (ci c1, r) := by
    rw [List.head?_eq_some_head hlne, Option.some.injEq] at hhead; exact hhead
  have hlastv : (A ++ X ++ B).getLast hlne = (ci c2, r) := by
    rw [List.getLast?_eq_some_getLast hlne, Option.some.injEq] at hlast; exact hlast
  have memS : ∀ v ∈ A ++ X ++ B, ∀ c ∈ S, v ≠ (ci c, r) := fun v hv => (hp v hv).2.2
  by_cases hXe : X = []
  · -- straight
    subst hXe
    left
    have hrow : ∀ v ∈ A ++ [] ++ B, v.2 = r ∧ InStrip v := by
      intro v hv
      simp only [List.append_nil, List.mem_append] at hv
      rcases hv with hv | hv
      · exact ⟨hA v hv, (hp v (by simp [hv])).1⟩
      · exact ⟨hB v hv, (hp v (by simp [hv])).1⟩
    have hu := row_unique hlne hrow hn hc
    rw [hheadv, hlastv, colOf_ci, colOf_ci] at hu
    refine ⟨hu, by rw [← hlen, hu, hseg_length], fun c hc' hcS => ?_⟩
    have hmem : (ci c, r) ∈ A ++ [] ++ B := by rw [hu]; exact mem_hseg.2 ⟨c, hc', rfl⟩
    exact memS _ hmem c hcS rfl
  · right
    have hAne : A ≠ [] := by
      rintro rfl
      have : (X ++ B).head (by simpa using hlne) = X.head hXe := List.head_append_of_ne_nil hXe
      have h1 : X.head hXe = (ci c1, r) := by rw [← this]; simpa using hheadv
      exact (hX _ (List.head_mem hXe)).1 (by rw [h1])
    have hBne : B ≠ [] := by
      rintro rfl
      have h1 : X.getLast hXe = (ci c2, r) := by
        rw [← hlastv]; simp [List.getLast_append_of_ne_nil _ hXe]
      exact (hX _ (List.getLast_mem hXe)).1 (by rw [h1])
    have hcA : A.IsChain Adj := hc.left_of_append.left_of_append
    have hcX : X.IsChain Adj := hc.left_of_append.right_of_append
    have hcB : B.IsChain Adj := hc.right_of_append
    have hnA : A.Nodup := (List.nodup_append.1 (List.nodup_append.1 hn).1).1
    have hnX : X.Nodup := (List.nodup_append.1 (List.nodup_append.1 hn).1).2.1
    have hnB : B.Nodup := (List.nodup_append.1 hn).2.1
    have hrowA : ∀ v ∈ A, v.2 = r ∧ InStrip v := fun v hv => ⟨hA v hv, (hp v (by simp [hv])).1⟩
    have hrowB : ∀ v ∈ B, v.2 = r ∧ InStrip v := fun v hv => ⟨hB v hv, (hp v (by simp [hv])).1⟩
    have huA := row_unique hAne hrowA hnA hcA
    have huB := row_unique hBne hrowB hnB hcB
    have hAh : A.head hAne = (ci c1, r) := by
      rw [← hheadv, List.head_append_of_ne_nil (by simp [hAne]), List.head_append_of_ne_nil hAne]
    have hBl : B.getLast hBne = (ci c2, r) := by
      rw [← hlastv, List.getLast_append_of_ne_nil _ hBne]
    rw [hAh, colOf_ci] at huA
    rw [hBl, colOf_ci] at huB
    set c1' := colOf (A.getLast hAne).1 with hc1'
    set c2' := colOf (B.head hBne).1 with hc2'
    -- the ends of `X`
    have j1 : Adj (A.getLast hAne) (X.head hXe) := by
      have := adj_junction (L1 := A) (L2 := X ++ B) (by simpa using hc) hAne (by simp [hXe])
      rwa [List.head_append_of_ne_nil hXe] at this
    have j2 : Adj (X.getLast hXe) (B.head hBne) := by
      have := adj_junction (L1 := A ++ X) (L2 := B) hc (by simp [hXe]) hBne
      rwa [List.getLast_append_of_ne_nil _ hXe] at this
    have hAl : A.getLast hAne = (ci c1', r) := by
      have h1 := hrowA _ (List.getLast_mem hAne)
      exact Prod.ext (by rw [hc1', ci_colOf h1.2.1 h1.2.2]) h1.1
    have hBh : B.head hBne = (ci c2', r) := by
      have h1 := hrowB _ (List.head_mem hBne)
      exact Prod.ext (by rw [hc2', ci_colOf h1.2.1 h1.2.2]) h1.1
    have hXh : X.head hXe = (ci c1', r + dir σ) := by
      rw [hAl] at j1
      exact adj_exit j1 (hX _ (List.head_mem hXe)).1 (hX _ (List.head_mem hXe)).2
    have hXl : X.getLast hXe = (ci c2', r + dir σ) := by
      rw [hBh] at j2
      exact adj_exit (adj_symm j2) (hX _ (List.getLast_mem hXe)).1
        (hX _ (List.getLast_mem hXe)).2
    have hlenA : A.length = (cols c1 c1').length := by rw [huA, hseg_length]
    have hlenB : B.length = (cols c2' c2).length := by rw [huB, hseg_length]
    have hlenX : 1 ≤ X.length := List.length_pos_iff.2 hXe
    simp only [List.length_append] at hlen
    have hnAB : (A ++ B).Nodup := by
      have hsub : List.Sublist (A ++ B) (A ++ X ++ B) := by
        rw [List.append_assoc]; exact (List.sublist_append_right X B).append_left A
      exact hn.sublist hsub
    refine ⟨c1', c2', X, ⟨?_, ?_⟩, by omega, ?_, by rw [← huA, ← huB]⟩
    · rw [← hseg_append_nodup (r := r), ← huA, ← huB]; exact hnAB
    · intro c hc' hcS
      have hmem : (ci c, r) ∈ A ++ B := by
        rw [huA, huB, List.mem_append]
        rw [List.mem_append] at hc'
        rcases hc' with h | h
        · exact Or.inl (mem_hseg.2 ⟨c, h, rfl⟩)
        · exact Or.inr (mem_hseg.2 ⟨c, h, rfl⟩)
      exact memS _ (by simp only [List.mem_append] at hmem ⊢; tauto) c hcS rfl
    · rw [mem_exc]
      refine ⟨by omega, by rw [List.head?_eq_some_head hXe, hXh], hcX,
        by rw [List.getLast?_eq_some_getLast hXe, hXl], hnX, fun v hv => ⟨(hp v (by simp [hv])).1,
          (hX v hv).2, by simp⟩⟩

/-- Recovering the columns where an excursion leaves and re-enters row `r`. -/
private def gEx (r : ℤ) (l : List (ℤ × ℤ)) : Option (Fin 3 × Fin 3) :=
  match l.filter (fun v => decide (v.2 ≠ r)) with
  | [] => none
  | x :: xs => some (colOf x.1, colOf ((x :: xs).getLast (List.cons_ne_nil _ _)).1)

/-- A horizontal segment has no vertex off its row. -/
private lemma filter_hseg (r : ℤ) (a b : Fin 3) :
    (hseg r a b).filter (fun v => decide (v.2 ≠ r)) = [] := by
  rw [List.filter_eq_nil_iff]; intro v hv; simp [(hseg_row hv).1]

/-- `gEx` of a straight excursion. -/
private lemma gEx_hseg (r : ℤ) (a b : Fin 3) : gEx r (hseg r a b) = none := by
  unfold gEx; rw [filter_hseg]

/-- `gEx` recovers the columns where the inner excursion starts and ends. -/
private lemma gEx_mid (r : ℤ) (a b c d : Fin 3) (X : List (ℤ × ℤ)) (hXne : X ≠ [])
    (hX : ∀ v ∈ X, v.2 ≠ r) :
    gEx r (hseg r a b ++ X ++ hseg r c d) =
      some (colOf (X.head hXne).1, colOf (X.getLast hXne).1) := by
  have : (hseg r a b ++ X ++ hseg r c d).filter (fun v => decide (v.2 ≠ r)) = X := by
    rw [List.filter_append, List.filter_append, filter_hseg, filter_hseg,
      List.filter_eq_self.2 (fun v hv => by simpa using hX v hv)]
    simp
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hXne
  unfold gEx; rw [this]; rfl

/-- The recursion for excursions in a half-strip. -/
private lemma exc_card (σ : Bool) (r : ℤ) (S : Finset (Fin 3)) (c1 c2 : Fin 3) (ℓ : ℕ) :
    (exc σ r S c1 c2 ℓ).card =
      (if ℓ + 1 = (cols c1 c2).length ∧ ∀ c ∈ cols c1 c2, c ∉ S then 1 else 0) +
      ∑ c1' : Fin 3, ∑ c2' : Fin 3,
        if okSeg S c1 c1' c2' c2 ∧ (cols c1 c1').length + (cols c2' c2).length ≤ ℓ then
          (exc σ (r + dir σ) ∅ c1' c2' (ℓ - (cols c1 c1').length - (cols c2' c2).length)).card
        else 0 := by
  let T : Option (Fin 3 × Fin 3) → Finset (List (ℤ × ℤ)) := fun
    | none => if ℓ + 1 = (cols c1 c2).length ∧ ∀ c ∈ cols c1 c2, c ∉ S then {[]} else ∅
    | some (c1', c2') =>
      if okSeg S c1 c1' c2' c2 ∧ (cols c1 c1').length + (cols c2' c2).length ≤ ℓ then
        exc σ (r + dir σ) ∅ c1' c2' (ℓ - (cols c1 c1').length - (cols c2' c2).length) else ∅
  let F : Option (Fin 3 × Fin 3) → List (ℤ × ℤ) → List (ℤ × ℤ) := fun
    | none, _ => hseg r c1 c2
    | some (c1', c2'), X => hseg r c1 c1' ++ X ++ hseg r c2' c2
  rw [card_eq_sum (exc σ r S c1 c2 ℓ) Finset.univ T F (gEx r) ?_ ?_ ?_]
  · rw [Fintype.sum_option, Fintype.sum_prod_type]
    congr 1
    · simp only [T]; split_ifs <;> simp
    · refine Finset.sum_congr rfl fun c1' _ => Finset.sum_congr rfl fun c2' _ => ?_
      simp only [T]; split_ifs <;> simp
  · rintro (_ | ⟨c1', c2'⟩) - x hx y hy hxy
    · simp only [T] at hx hy; split_ifs at hx hy <;> simp_all
    · simp only [F] at hxy
      exact List.append_cancel_left (List.append_cancel_right hxy)
  · rintro (_ | ⟨c1', c2'⟩) - x hx
    · exact gEx_hseg r c1 c2
    · simp only [T] at hx
      split_ifs at hx with h
      · obtain ⟨hl, hh, -, ht, -, hp⟩ := mem_exc.1 hx
        have hne : x ≠ [] := by rintro rfl; simp at hl
        simp only [F]
        rw [gEx_mid r _ _ _ _ x hne fun v hv => (onSide_step (hp v hv).2.1).2]
        rw [List.head?_eq_some_head hne, Option.some.injEq] at hh
        rw [List.getLast?_eq_some_getLast hne, Option.some.injEq] at ht
        rw [hh, ht, colOf_ci, colOf_ci]
      · simp at hx
  · intro l
    constructor
    · intro hl
      rcases exc_decomp hl with ⟨rfl, h1, h2⟩ | ⟨c1', c2', X, hok, hlen, hX, rfl⟩
      · refine ⟨none, Finset.mem_univ _, [], ?_, rfl⟩
        simp only [T]; rw [if_pos ⟨h1, h2⟩]; exact Finset.mem_singleton_self _
      · refine ⟨some (c1', c2'), Finset.mem_univ _, X, ?_, rfl⟩
        simp only [T]; rw [if_pos ⟨hok, hlen⟩]; exact hX
    · rintro ⟨i, -, x, hx, rfl⟩
      rcases i with _ | ⟨c1', c2'⟩
      · simp only [T] at hx; split_ifs at hx with h
        · exact exc_build1 h.1 h.2
        · simp at hx
      · simp only [T] at hx; split_ifs at hx with h
        · exact exc_build2 h.1 h.2 hx
        · simp at hx

/-! ### The excursion numbers -/

/-- `pq ℓ = (p ℓ, q ℓ)`: the numbers of excursions between adjacent columns, resp. between
the two boundary columns. -/
private def pq : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | 1 => (1, 0)
  | 2 => (0, 1)
  | n + 3 => ((pq (n + 1)).1 + (pq n).2, 2 * (pq n).1 + (pq (n + 1)).2)

/-- The number of excursions of `ℓ` steps from column `c1` to column `c2`. -/
private def Ef (c1 c2 : Fin 3) (ℓ : ℕ) : ℕ :=
  if c1 = c2 then (if ℓ = 0 then 1 else 0)
  else if (c1 = 0 ∧ c2 = 2) ∨ (c1 = 2 ∧ c2 = 0) then (pq ℓ).2 else (pq ℓ).1

/-- `Ef` satisfies the recursion of `exc_card`. -/
private lemma Ef_rec (c1 c2 : Fin 3) (ℓ : ℕ) :
    Ef c1 c2 ℓ =
      (if ℓ + 1 = (cols c1 c2).length ∧ ∀ c ∈ cols c1 c2, c ∉ (∅ : Finset (Fin 3)) then 1 else 0) +
      ∑ c1' : Fin 3, ∑ c2' : Fin 3,
        if okSeg ∅ c1 c1' c2' c2 ∧ (cols c1 c1').length + (cols c2' c2).length ≤ ℓ then
          Ef c1' c2' (ℓ - (cols c1 c1').length - (cols c2' c2).length)
        else 0 := by
  rcases ℓ with _ | _ | _ | n
  all_goals
    fin_cases c1 <;> fin_cases c2 <;>
      simp (config := {decide := true}) [Fin.sum_univ_three, okSeg, cols, Ef, pq]
  all_goals ring

/-- The number of excursions (avoiding nothing) is `Ef`. -/
private lemma exc_Ef (ℓ : ℕ) :
    ∀ (σ : Bool) (r : ℤ) (c1 c2 : Fin 3), (exc σ r ∅ c1 c2 ℓ).card = Ef c1 c2 ℓ := by
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    intro σ r c1 c2
    rw [exc_card, Ef_rec]
    congr 1
    refine Finset.sum_congr rfl fun c1' _ => Finset.sum_congr rfl fun c2' _ => ?_
    split_ifs with h
    · exact ih _ (by have := cols_length_pos c1 c1'; have := cols_length_pos c2' c2; omega) _ _ _ _
    · rfl

/-- The number of excursions ending at column `1` whose vertices in the base row avoid
column `0`. -/
private def E0 (c : Fin 3) (ℓ : ℕ) : ℕ :=
  if c = 1 then (if ℓ = 0 then 1 else 0)
  else if c = 2 then (if ℓ = 1 then 1 else 0) + (if 2 ≤ ℓ then (pq (ℓ - 2)).1 else 0) else 0

/-- The number of excursions ending at column `1` that avoid column `0` of the base row. -/
private lemma exc_E0 (σ : Bool) (r : ℤ) (c : Fin 3) (ℓ : ℕ) :
    (exc σ r {0} c 1 ℓ).card = E0 c ℓ := by
  rw [exc_card]
  simp only [exc_Ef]
  rcases ℓ with _ | _ | n
  all_goals
    fin_cases c <;> simp (config := {decide := true}) [Fin.sum_univ_three, okSeg, cols, Ef, E0]


/-! ### Closed walks as walks from the origin to a neighbour of the origin -/

/-- Column `0`. -/
private lemma ci_zero : ci 0 = 0 := rfl
/-- Column `1`. -/
private lemma ci_one : ci 1 = 1 := rfl
/-- Column `2`. -/
private lemma ci_two : ci 2 = 2 := rfl

/-- Self-avoiding walks of `j` steps in the strip from the origin to `u`. -/
private def Qset (u : ℤ × ℤ) (j : ℕ) : Finset (List (ℤ × ℤ)) :=
  (walksFrom 0 j).filter fun Q => Q.getLast? = some u ∧ Q.Nodup ∧ ∀ v ∈ Q, InStrip v

/-- Membership in `Qset`. -/
private lemma mem_Qset {u : ℤ × ℤ} {j : ℕ} {Q : List (ℤ × ℤ)} :
    Q ∈ Qset u j ↔ Q.length = j + 1 ∧ Q.head? = some 0 ∧ Q.IsChain Adj ∧
      Q.getLast? = some u ∧ Q.Nodup ∧ ∀ v ∈ Q, InStrip v := by
  simp only [Qset, Finset.mem_filter, mem_walksFrom, and_assoc]

/-- The three neighbours of the origin in the strip. -/
private def nb : Fin 3 → ℤ × ℤ := ![(1, 0), (0, 1), (0, -1)]

/-- Every neighbour of the origin in the strip is one of `nb`. -/
private lemma nb_of_adj {u : ℤ × ℤ} (h : Adj u 0) (hs : InStrip u) : ∃ i, u = nb i := by
  rw [adj_iff] at h
  unfold InStrip at hs
  obtain ⟨u1, u2⟩ := u
  simp only [Prod.fst_zero, Prod.snd_zero] at h hs
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · omega
  · exact ⟨0, by simp [nb]; constructor <;> omega⟩
  · exact ⟨2, by simp [nb]; constructor <;> omega⟩
  · exact ⟨1, by simp [nb]; constructor <;> omega⟩

/-- The `nb i` are neighbours of the origin. -/
private lemma adj_nb (i : Fin 3) : Adj (nb i) 0 := by
  fin_cases i <;> simp [nb, adj_iff]

/-- The origin lies in the strip. -/
private lemma instrip_zero : InStrip (0 : ℤ × ℤ) := by simp [InStrip]

/-- A duplicate-free list with at least two entries has distinct ends. -/
private lemma head_ne_getLast {l : List (ℤ × ℤ)} (hn : l.Nodup) (h2 : 2 ≤ l.length) (hne : l ≠ []) :
    l.head hne ≠ l.getLast hne := by
  match l, hn, h2, hne with
  | a :: b :: t, hn, _, _ =>
    simp only [List.head_cons, List.getLast_cons_cons]
    intro h
    have hm : (b :: t).getLast (List.cons_ne_nil _ _) ∈ b :: t := List.getLast_mem _
    rw [← h] at hm
    exact (List.nodup_cons.1 hn).1 hm

/-- `GLs [0] 0 k` counts walks from the origin to one of its neighbours. -/
private lemma GLs_Q (k : ℕ) (hk : 2 ≤ k) :
    GLs [0] 0 k = ∑ i : Fin 3, (Qset (nb i) (k - 1)).card := by
  unfold GLs
  refine card_eq_sum _ Finset.univ (fun i => Qset (nb i) (k - 1)) (fun _ Q => Q ++ [0])
    (fun W => if W.dropLast.getLast? = some (nb 0) then 0
      else if W.dropLast.getLast? = some (nb 1) then 1 else 2) ?_ ?_ ?_
  · intro i _ x _ y _ h
    exact List.append_cancel_right h
  · intro i _ Q hQ
    obtain ⟨-, -, -, hl, -⟩ := mem_Qset.1 hQ
    simp only [List.dropLast_concat, hl]
    fin_cases i <;> simp [nb]
  · intro W
    simp only [Finset.mem_filter, mem_walksFrom, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hlen, hhead, hc⟩, hstrip, hlast, havoid, hnd⟩
      obtain ⟨W', rfl⟩ : ∃ W', W = 0 :: W' := by
        match W, hhead with
        | a :: W', hhead => simp at hhead; exact ⟨W', by rw [hhead]⟩
      have hW'ne : W' ≠ [] := by rintro rfl; simp at hlen; omega
      have hW'last : W'.getLast hW'ne = 0 := by
        rw [List.getLast?_cons, List.getLast?_eq_some_getLast hW'ne] at hlast
        simpa using hlast
      have hW' : W' = W'.dropLast ++ [0] := by
        rw [← hW'last]; exact (List.dropLast_append_getLast hW'ne).symm
      set W'' := W'.dropLast with hW''
      simp only [List.tail_cons] at hstrip havoid hnd
      rw [← hW''] at havoid hnd
      have hW''ne : W'' ≠ [] := by
        intro h
        rw [h] at hW'
        rw [hW'] at hlen; simp at hlen; omega
      have hWeq : 0 :: W' = (0 :: W'') ++ [0] := by rw [hW']; simp
      rw [hWeq] at hc hlen
      have hu : Adj ((0 :: W'').getLast (List.cons_ne_nil _ _)) 0 :=
        adj_junction (L2 := [0]) hc (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
      have hus : InStrip ((0 :: W'').getLast (List.cons_ne_nil _ _)) := by
        rw [List.getLast_cons hW''ne]
        exact hstrip _ (by rw [hW']; exact List.mem_append_left _ (List.getLast_mem _))
      obtain ⟨i, hi⟩ := nb_of_adj hu hus
      refine ⟨i, 0 :: W'', ?_, hWeq.symm⟩
      rw [mem_Qset]
      refine ⟨by simp at hlen ⊢; omega, rfl, hc.left_of_append, ?_, ?_, ?_⟩
      · rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _), hi]
      · exact List.nodup_cons.2 ⟨fun h => havoid 0 h (by simp), hnd⟩
      · intro v hv
        rcases List.mem_cons.1 hv with rfl | hv
        · exact instrip_zero
        · exact hstrip v (by rw [hW']; exact List.mem_append_left _ hv)
    · rintro ⟨i, Q, hQ, rfl⟩
      obtain ⟨hlen, hhead, hc, hlast, hn, hs⟩ := mem_Qset.1 hQ
      obtain ⟨Q', rfl⟩ : ∃ Q', Q = 0 :: Q' := by
        match Q, hhead with
        | a :: Q', hhead => simp at hhead; exact ⟨Q', by rw [hhead]⟩
      refine ⟨⟨by simp at hlen ⊢; omega, by simp, ?_⟩, ?_, List.getLast?_concat, ?_, ?_⟩
      · refine List.IsChain.append hc (List.isChain_singleton _) ?_
        intro x hx y hy
        rw [hlast, Option.mem_def, Option.some.injEq] at hx
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        rw [← hx, ← hy]; exact adj_nb i
      · intro v hv
        simp only [List.cons_append, List.tail_cons, List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | rfl
        · exact hs v (List.mem_cons_of_mem _ hv)
        · exact instrip_zero
      · simp only [List.cons_append, List.tail_cons, List.dropLast_concat]
        intro v hv h0
        simp only [List.mem_singleton] at h0
        subst h0
        exact (List.nodup_cons.1 hn).1 hv
      · simp only [List.cons_append, List.tail_cons, List.dropLast_concat]
        exact (List.nodup_cons.1 hn).2

/-- `near σ r` is the closed half-plane on side `!σ` of row `r`. -/
private lemma near_true_iff (σ : Bool) (r : ℤ) (v : ℤ × ℤ) : near σ r v = true ↔ onSide (!σ) r v := by
  cases σ <;> simp [near, onSide]

/-- Vertices beyond row `dir σ` on side `σ` are not `near`. -/
private lemma near_false_of {σ : Bool} {v : ℤ × ℤ} (h : onSide σ (dir σ) v) : near σ 0 v = false := by
  cases σ <;> simp [near, onSide, dir] at h ⊢ <;> omega

/-- Vertices that are not `near σ 0` lie beyond row `dir σ` on side `σ`. -/
private lemma onSide_of_near_false {σ : Bool} {v : ℤ × ℤ} (h : near σ 0 v = false) :
    onSide σ (dir σ) v := by
  cases σ <;> simp [near, onSide, dir] at h ⊢ <;> omega

/-- Recovering a split `A ++ X` along a predicate. -/
private lemma split_take {q : ℤ × ℤ → Bool} {A X : List (ℤ × ℤ)} (hA : ∀ v ∈ A, q v = true)
    (hX : ∀ v ∈ X.head?, q v = false) :
    (A ++ X).takeWhile q = A ∧ (A ++ X).dropWhile q = X := by
  constructor
  · rw [List.takeWhile_append_of_pos hA]
    cases X with
    | nil => simp
    | cons x xs => rw [List.takeWhile_cons_of_neg (by simp [hX x (by simp)])]; simp
  · rw [List.dropWhile_append_of_pos hA]
    cases X with
    | nil => simp
    | cons x xs => rw [List.dropWhile_cons_of_neg (by simp [hX x (by simp)])]

/-- A split `A ++ X` along a predicate is unique. -/
private lemma split_inj {q : ℤ × ℤ → Bool} {A X A' X' : List (ℤ × ℤ)} (hA : ∀ v ∈ A, q v = true)
    (hX : ∀ v ∈ X.head?, q v = false) (hA' : ∀ v ∈ A', q v = true)
    (hX' : ∀ v ∈ X'.head?, q v = false) (h : A ++ X = A' ++ X') : A = A' ∧ X = X' := by
  have h1 := split_take hA hX
  have h2 := split_take hA' hX'
  rw [h] at h1
  exact ⟨h1.1.symm.trans h2.1, h1.2.symm.trans h2.2⟩

/-- Excursions on side `!σ` of row `0` are `near σ 0`. -/
private lemma exc_near {σ : Bool} {S : Finset (Fin 3)} {c1 c2 : Fin 3} {ℓ : ℕ} {A : List (ℤ × ℤ)}
    (h : A ∈ exc (!σ) 0 S c1 c2 ℓ) : ∀ v ∈ A, near σ 0 v = true := fun v hv =>
  (near_true_iff σ 0 v).2 ((mem_exc.1 h).2.2.2.2.2 v hv).2.1

/-- Excursions beyond row `dir σ` on side `σ` are not `near σ 0`. -/
private lemma exc_far {σ : Bool} {S : Finset (Fin 3)} {c1 c2 : Fin 3} {ℓ : ℕ} {X : List (ℤ × ℤ)}
    (h : X ∈ exc σ (dir σ) S c1 c2 ℓ) : ∀ v ∈ X, near σ 0 v = false := fun v hv =>
  near_false_of ((mem_exc.1 h).2.2.2.2.2 v hv).2.1

/-- A property of all entries holds for the head. -/
private lemma head?_mem_of {l : List (ℤ × ℤ)} {P : ℤ × ℤ → Prop} (h : ∀ v ∈ l, P v) :
    ∀ v ∈ l.head?, P v := fun v hv => h v (List.mem_of_mem_head? hv)

/-- A vertical unit step from row `0`. -/
private lemma adj_vert0 (σ : Bool) (c : ℤ) : Adj (c, 0) (c, dir σ) := by
  simpa using adj_vert σ c 0

/-- Walks from the origin to `(0, ±1)`: an excursion on the far side of the origin's row,
followed by an excursion on the near side. -/
private lemma Q1_card (σ : Bool) (j : ℕ) (hj : 2 ≤ j) :
    (Qset (0, dir σ) j).card = ∑ c : Fin 3, ∑ ℓ ∈ Finset.range j,
      (exc (!σ) 0 ∅ 0 c ℓ).card * (exc σ (dir σ) ∅ c 0 (j - 1 - ℓ)).card := by
  rw [card_eq_sum (Qset (0, dir σ) j) (Finset.univ ×ˢ Finset.range j)
    (fun p => exc (!σ) 0 ∅ 0 p.1 p.2 ×ˢ exc σ (dir σ) ∅ p.1 0 (j - 1 - p.2))
    (fun _ x => x.1 ++ x.2)
    (fun Q => (colOf (((Q.takeWhile (near σ 0)).getLast?).getD 0).1,
      (Q.takeWhile (near σ 0)).length - 1)) ?_ ?_ ?_]
  · rw [Finset.sum_product]; simp only [Finset.card_product]
  · rintro ⟨c, ℓ⟩ - ⟨A, X⟩ hAX ⟨A', X'⟩ hAX' h
    simp only [Finset.mem_product] at hAX hAX' h
    have := split_inj (exc_near hAX.1) (head?_mem_of (exc_far hAX.2)) (exc_near hAX'.1)
      (head?_mem_of (exc_far hAX'.2)) h
    rw [this.1, this.2]
  · rintro ⟨c, ℓ⟩ - ⟨A, X⟩ hAX
    simp only [Finset.mem_product] at hAX
    simp only
    rw [(split_take (exc_near hAX.1) (head?_mem_of (exc_far hAX.2))).1]
    obtain ⟨hl, -, -, ht, -⟩ := mem_exc.1 hAX.1
    rw [ht, hl]; simp [colOf_ci]
  · intro Q
    constructor
    · intro hQ
      obtain ⟨hlen, hhead, hc, hlast, hn, hs⟩ := mem_Qset.1 hQ
      obtain ⟨P, rfl⟩ : ∃ P, Q = 0 :: P := by
        match Q, hhead with
        | a :: P, hhead => simp at hhead; exact ⟨P, by rw [hhead]⟩
      have hPlen : P.length = j := by simpa using hlen
      have hPne : P ≠ [] := by rintro rfl; simp at hPlen; omega
      have hP0 : (0 : ℤ × ℤ) ∉ P := (List.nodup_cons.1 hn).1
      have hPn : P.Nodup := (List.nodup_cons.1 hn).2
      have hPc : P.IsChain Adj := hc.tail
      have hPs : ∀ v ∈ P, InStrip v := fun v hv => hs v (List.mem_cons_of_mem _ hv)
      have hPlast : P.getLast hPne = (0, dir σ) := by
        rw [List.getLast?_cons, List.getLast?_eq_some_getLast hPne] at hlast; simpa using hlast
      have hPhead : near σ 0 (P.head hPne) = true := by
        have hadj : Adj 0 (P.head hPne) := by
          obtain ⟨b, P', hP'⟩ := List.exists_cons_of_ne_nil hPne
          subst hP'
          exact (List.isChain_cons_cons.1 hc).1
        obtain ⟨i, hi⟩ := nb_of_adj (adj_symm hadj) (hPs _ (List.head_mem _))
        have hne := head_ne_getLast hPn (by omega) hPne
        rw [hPlast, hi] at hne
        rw [hi]
        fin_cases i <;> cases σ <;> simp [nb, near, dir] at hne ⊢
      obtain ⟨A, X, hPAX, hA, hX⟩ := once_split (near σ 0) 0 (dir σ)
        (fun a b hab ha hb => by simpa using near_hq σ 0 a b hab ha hb) hPc hPn hPs
        ⟨0, le_refl _, by norm_num, Or.inl hP0⟩
        (fun v hv => by
          rw [List.head?_eq_some_head hPne, Option.mem_def, Option.some.injEq] at hv
          rw [← hv]; exact hPhead)
        (fun v hv => by
          rw [List.getLast?_eq_some_getLast hPne, Option.mem_def, Option.some.injEq] at hv
          rw [← hv, hPlast]; cases σ <;> simp [near, dir])
      have hAne : A ≠ [] := by
        have hm : P.head hPne ∈ A ++ X := by rw [← hPAX]; exact List.head_mem hPne
        rcases List.mem_append.1 hm with h | h
        · exact List.ne_nil_of_mem h
        · have := hX _ h; rw [hPhead] at this; simp at this
      have hXne : X ≠ [] := by
        have hm : P.getLast hPne ∈ A ++ X := by rw [← hPAX]; exact List.getLast_mem hPne
        rcases List.mem_append.1 hm with h | h
        · have := hA _ h; rw [hPlast] at this; cases σ <;> simp [near, dir] at this
        · exact List.ne_nil_of_mem h
      subst hPAX
      have j1 : Adj (A.getLast hAne) (X.head hXne) := adj_junction hPc hAne hXne
      obtain ⟨e1, e1a, e1b⟩ := near_hq σ 0 _ _ j1 (hA _ (List.getLast_mem _))
        (hX _ (List.head_mem _))
      have hs1 := hPs _ (List.mem_append_left _ (List.getLast_mem hAne))
      unfold InStrip at hs1
      set c := colOf (A.getLast hAne).1 with hcdef
      have hAl : A.getLast hAne = (ci c, 0) := Prod.ext (by rw [hcdef, ci_colOf hs1.1 hs1.2]) e1a
      have hXh : X.head hXne = (ci c, dir σ) :=
        Prod.ext (by rw [← e1, hcdef, ci_colOf hs1.1 hs1.2]) (by simpa using e1b)
      have hlenAX : A.length + X.length = j := by simpa using hPlen
      have hXlen : 1 ≤ X.length := List.length_pos_iff.2 hXne
      refine ⟨(c, A.length), Finset.mem_product.2 ⟨Finset.mem_univ _,
        Finset.mem_range.2 (by omega)⟩, (0 :: A, X), Finset.mem_product.2 ⟨?_, ?_⟩, by simp⟩
      · rw [mem_exc]
        refine ⟨by simp, by rw [List.head?_cons, ci_zero]; rfl, ?_, ?_, ?_, ?_⟩
        · have : ((0 :: A) ++ X).IsChain Adj := by simpa using hc
          exact this.left_of_append
        · rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _), List.getLast_cons hAne, hAl]
        · exact List.nodup_cons.2 ⟨fun h => hP0 (List.mem_append_left _ h),
            (List.nodup_append.1 hPn).1⟩
        · intro v hv
          rcases List.mem_cons.1 hv with rfl | hv
          · exact ⟨instrip_zero, by cases σ <;> simp [onSide], by simp⟩
          · exact ⟨hPs v (List.mem_append_left _ hv), (near_true_iff σ 0 v).1 (hA v hv), by simp⟩
      · rw [mem_exc]
        refine ⟨by dsimp only; omega, by rw [List.head?_eq_some_head hXne, hXh], hPc.right_of_append, ?_,
          (List.nodup_append.1 hPn).2.1, fun v hv => ⟨hPs v (List.mem_append_right _ hv),
            onSide_of_near_false (hX v hv), by simp⟩⟩
        rw [List.getLast?_eq_some_getLast hXne, ← List.getLast_append_of_ne_nil hPne hXne,
          hPlast, ci_zero]
    · rintro ⟨⟨c, ℓ⟩, hp, ⟨A, X⟩, hAX, rfl⟩
      simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_range] at hp hAX
      obtain ⟨hAl, hAh, hAc, hAt, hAn, hAp⟩ := mem_exc.1 hAX.1
      obtain ⟨hXl, hXh, hXc, hXt, hXn, hXp⟩ := mem_exc.1 hAX.2
      have hAne : A ≠ [] := by rintro rfl; simp at hAl
      have hXne : X ≠ [] := by rintro rfl; simp at hXl
      rw [mem_Qset]
      refine ⟨by simp only [List.length_append]; omega, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.head?_append_of_ne_nil _ hAne, hAh, ci_zero]; rfl
      · refine List.IsChain.append hAc hXc fun x hx y hy => ?_
        rw [hAt, Option.mem_def, Option.some.injEq] at hx
        rw [hXh, Option.mem_def, Option.some.injEq] at hy
        rw [← hx, ← hy]; exact adj_vert0 σ _
      · rw [List.getLast?_append_of_ne_nil _ hXne, hXt, ci_zero]
      · refine List.nodup_append.2 ⟨hAn, hXn, fun a ha b hb hab => ?_⟩
        have h1 := exc_near hAX.1 a ha
        have h2 := exc_far hAX.2 b hb
        rw [hab, h2] at h1; simp at h1
      · intro v hv
        rcases List.mem_append.1 hv with hv | hv
        · exact (hAp v hv).1
        · exact (hXp v hv).1


/-- The side of the origin's row on which the second vertex of `Q` lies (`true`: above). -/
private def firstSide (Q : List (ℤ × ℤ)) : Bool := decide (0 < ((Q.tail.head?).getD 0).2)

/-- `firstSide` of a walk starting `0, (0, dir σ), …`. -/
private lemma firstSide_eq {σ : Bool} {c : Fin 3} {ℓ : ℕ} {A : List (ℤ × ℤ)}
    (hA : A ∈ exc σ (dir σ) ∅ 0 c ℓ) (X : List (ℤ × ℤ)) : firstSide (0 :: (A ++ X)) = σ := by
  obtain ⟨hAl, hAh, -⟩ := mem_exc.1 hA
  have hAne : A ≠ [] := by rintro rfl; simp at hAl
  unfold firstSide
  rw [List.tail_cons, List.head?_append_of_ne_nil _ hAne, hAh]
  cases σ <;> simp [dir]

/-- Walks from the origin to `(1, 0)`: a first step to `(0, ±1)`, an excursion on that side of
the origin's row, and an excursion on the other side that avoids the origin. -/
private lemma Q10_card (j : ℕ) (hj : 2 ≤ j) :
    (Qset (1, 0) j).card = ∑ σ : Bool, ∑ c : Fin 3, ∑ ℓ ∈ Finset.range (j - 1),
      (exc σ (dir σ) ∅ 0 c ℓ).card * (exc (!σ) 0 {0} c 1 (j - 2 - ℓ)).card := by
  rw [card_eq_sum (Qset (1, 0) j) ((Finset.univ ×ˢ Finset.univ) ×ˢ Finset.range (j - 1))
    (fun p => exc p.1.1 (dir p.1.1) ∅ 0 p.1.2 p.2 ×ˢ exc (!p.1.1) 0 {0} p.1.2 1 (j - 2 - p.2))
    (fun _ x => 0 :: (x.1 ++ x.2))
    (fun Q => ((firstSide Q, colOf ((((Q.tail.takeWhile
      (fun v => !near (firstSide Q) 0 v)).getLast?).getD 0).1)),
      (Q.tail.takeWhile (fun v => !near (firstSide Q) 0 v)).length - 1)) ?_ ?_ ?_]
  · rw [Finset.sum_product, Finset.sum_product]; simp only [Finset.card_product]
  · rintro ⟨⟨σ, c⟩, ℓ⟩ - ⟨A, X⟩ hAX ⟨A', X'⟩ hAX' h
    simp only [Finset.mem_product] at hAX hAX'
    simp only [List.cons.injEq, true_and] at h
    have := split_inj (q := fun v => !near σ 0 v)
      (fun v hv => by simp [exc_far hAX.1 v hv])
      (head?_mem_of (fun v hv => by simp [exc_near hAX.2 v hv]))
      (fun v hv => by simp [exc_far hAX'.1 v hv])
      (head?_mem_of (fun v hv => by simp [exc_near hAX'.2 v hv])) h
    rw [this.1, this.2]
  · rintro ⟨⟨σ, c⟩, ℓ⟩ - ⟨A, X⟩ hAX
    simp only [Finset.mem_product] at hAX
    simp only
    rw [firstSide_eq hAX.1 X, List.tail_cons,
      (split_take (q := fun v => !near σ 0 v) (fun v hv => by simp [exc_far hAX.1 v hv])
        (head?_mem_of (fun v hv => by simp [exc_near hAX.2 v hv]))).1]
    obtain ⟨hl, -, -, ht, -⟩ := mem_exc.1 hAX.1
    rw [ht, hl]; simp [colOf_ci]
  · intro Q
    constructor
    · intro hQ
      obtain ⟨hlen, hhead, hc, hlast, hn, hs⟩ := mem_Qset.1 hQ
      obtain ⟨P, rfl⟩ : ∃ P, Q = 0 :: P := by
        match Q, hhead with
        | a :: P, hhead => simp at hhead; exact ⟨P, by rw [hhead]⟩
      have hPlen : P.length = j := by simpa using hlen
      have hPne : P ≠ [] := by rintro rfl; simp at hPlen; omega
      have hP0 : (0 : ℤ × ℤ) ∉ P := (List.nodup_cons.1 hn).1
      have hPn : P.Nodup := (List.nodup_cons.1 hn).2
      have hPc : P.IsChain Adj := hc.tail
      have hPs : ∀ v ∈ P, InStrip v := fun v hv => hs v (List.mem_cons_of_mem _ hv)
      have hPlast : P.getLast hPne = (1, 0) := by
        rw [List.getLast?_cons, List.getLast?_eq_some_getLast hPne] at hlast; simpa using hlast
      obtain ⟨σ, hσ⟩ : ∃ σ : Bool, P.head hPne = (0, dir σ) := by
        have hadj : Adj 0 (P.head hPne) := by
          obtain ⟨b, P', hP'⟩ := List.exists_cons_of_ne_nil hPne
          subst hP'
          exact (List.isChain_cons_cons.1 hc).1
        obtain ⟨i, hi⟩ := nb_of_adj (adj_symm hadj) (hPs _ (List.head_mem _))
        have hne := head_ne_getLast hPn (by omega) hPne
        rw [hPlast, hi] at hne
        fin_cases i
        · simp [nb] at hne
        · exact ⟨true, by rw [hi]; simp [nb, dir]⟩
        · exact ⟨false, by rw [hi]; simp [nb, dir]⟩
      obtain ⟨A, X, hPAX, hA, hX⟩ := once_split (fun v => !near σ 0 v) (dir σ) 0
        (fun a b hab ha hb => by
          have := near_hq σ 0 b a (adj_symm hab) (by simpa using hb) (by simpa using ha)
          exact ⟨this.1.symm, by rw [this.2.2, zero_add], this.2.1⟩)
        hPc hPn hPs ⟨0, le_refl _, by norm_num, Or.inr fun h => hP0 h⟩
        (fun v hv => by
          rw [List.head?_eq_some_head hPne, Option.mem_def, Option.some.injEq] at hv
          rw [← hv, hσ]; cases σ <;> simp [near, dir])
        (fun v hv => by
          rw [List.getLast?_eq_some_getLast hPne, Option.mem_def, Option.some.injEq] at hv
          rw [← hv, hPlast]; cases σ <;> simp [near])
      have hAne : A ≠ [] := by
        have hm : P.head hPne ∈ A ++ X := by rw [← hPAX]; exact List.head_mem hPne
        rcases List.mem_append.1 hm with h | h
        · exact List.ne_nil_of_mem h
        · have := hX _ h; rw [hσ] at this; cases σ <;> simp [near, dir] at this
      have hXne : X ≠ [] := by
        have hm : P.getLast hPne ∈ A ++ X := by rw [← hPAX]; exact List.getLast_mem hPne
        rcases List.mem_append.1 hm with h | h
        · have := hA _ h; rw [hPlast] at this; cases σ <;> simp [near] at this
        · exact List.ne_nil_of_mem h
      subst hPAX
      have j1 : Adj (A.getLast hAne) (X.head hXne) := adj_junction hPc hAne hXne
      obtain ⟨e1, e1a, e1b⟩ := near_hq σ 0 _ _ (adj_symm j1)
        (by simpa using hX _ (List.head_mem hXne)) (by simpa using hA _ (List.getLast_mem hAne))
      have hs1 := hPs _ (List.mem_append_left _ (List.getLast_mem hAne))
      unfold InStrip at hs1
      set c := colOf (A.getLast hAne).1 with hcdef
      have hAl : A.getLast hAne = (ci c, dir σ) :=
        Prod.ext (by rw [hcdef, ci_colOf hs1.1 hs1.2]) (by rw [e1b, zero_add])
      have hXh : X.head hXne = (ci c, 0) :=
        Prod.ext (by rw [e1, hcdef, ci_colOf hs1.1 hs1.2]) e1a
      have hAh : A.head hAne = (ci 0, dir σ) := by
        rw [ci_zero, ← hσ, List.head_append_of_ne_nil hAne]
      have hlenAX : A.length + X.length = j := by simpa using hPlen
      have hAlen : 1 ≤ A.length := List.length_pos_iff.2 hAne
      have hXlen : 1 ≤ X.length := List.length_pos_iff.2 hXne
      refine ⟨((σ, c), A.length - 1), Finset.mem_product.2 ⟨Finset.mem_product.2
        ⟨Finset.mem_univ _, Finset.mem_univ _⟩, Finset.mem_range.2 (by omega)⟩, (A, X),
        Finset.mem_product.2 ⟨?_, ?_⟩, rfl⟩
      · rw [mem_exc]
        refine ⟨by dsimp only; omega, by rw [List.head?_eq_some_head hAne, hAh],
          hPc.left_of_append, by rw [List.getLast?_eq_some_getLast hAne, hAl],
          (List.nodup_append.1 hPn).1, fun v hv => ⟨hPs v (List.mem_append_left _ hv),
            onSide_of_near_false (by simpa using hA v hv), by simp⟩⟩
      · rw [mem_exc]
        refine ⟨by dsimp only; omega, by rw [List.head?_eq_some_head hXne, hXh],
          hPc.right_of_append, ?_, (List.nodup_append.1 hPn).2.1, fun v hv =>
            ⟨hPs v (List.mem_append_right _ hv), (near_true_iff σ 0 v).1 (by simpa using hX v hv),
              ?_⟩⟩
        · rw [List.getLast?_eq_some_getLast hXne, ← List.getLast_append_of_ne_nil hPne hXne,
            hPlast, ci_one]
        · intro c' hc' he
          rw [Finset.mem_singleton] at hc'
          subst hc'
          rw [ci_zero] at he
          subst he
          exact hP0 (List.mem_append_right _ hv)
    · rintro ⟨⟨⟨σ, c⟩, ℓ⟩, hp, ⟨A, X⟩, hAX, rfl⟩
      simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_range] at hp hAX
      obtain ⟨hAl, hAh, hAc, hAt, hAn, hAp⟩ := mem_exc.1 hAX.1
      obtain ⟨hXl, hXh, hXc, hXt, hXn, hXp⟩ := mem_exc.1 hAX.2
      have hAne : A ≠ [] := by rintro rfl; simp at hAl
      have hXne : X ≠ [] := by rintro rfl; simp at hXl
      have hAX0 : (0 : ℤ × ℤ) ∉ A ++ X := by
        intro h0
        rcases List.mem_append.1 h0 with h | h
        · have := exc_far hAX.1 _ h
          cases σ <;> simp [near] at this
        · exact (hXp _ h).2.2 0 (Finset.mem_singleton_self _) (by rw [ci_zero]; rfl)
      rw [mem_Qset]
      refine ⟨by simp only [List.length_cons, List.length_append]; omega, rfl, ?_, ?_, ?_, ?_⟩
      · have hc2 : (A ++ X).IsChain Adj := by
          refine List.IsChain.append hAc hXc fun x hx y hy => ?_
          rw [hAt, Option.mem_def, Option.some.injEq] at hx
          rw [hXh, Option.mem_def, Option.some.injEq] at hy
          rw [← hx, ← hy]; exact adj_symm (adj_vert0 σ _)
        have : ([0] ++ (A ++ X)).IsChain Adj := by
          refine List.IsChain.append (List.isChain_singleton _) hc2 fun x hx y hy => ?_
          simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hx
          rw [List.head?_append_of_ne_nil _ hAne, hAh, Option.mem_def, Option.some.injEq] at hy
          rw [← hx, ← hy, ci_zero]; exact adj_vert0 σ 0
        simpa using this
      · rw [List.getLast?_cons, List.getLast?_append_of_ne_nil _ hXne, hXt, ci_one]; rfl
      · refine List.nodup_cons.2 ⟨hAX0, List.nodup_append.2 ⟨hAn, hXn, fun a ha b hb hab => ?_⟩⟩
        have h1 := exc_far hAX.1 a ha
        have h2 := exc_near hAX.2 b hb
        rw [hab, h2] at h1; simp at h1
      · intro v hv
        rcases List.mem_cons.1 hv with rfl | hv
        · exact instrip_zero
        · rcases List.mem_append.1 hv with hv | hv
          · exact (hAp v hv).1
          · exact (hXp v hv).1

open Finset

/-! ### The generating function -/

/-- `rr m = (p (2m+1), q (2m))`, the nonzero excursion numbers (`pq_par`). -/
private def rr : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | 1 => (1, 1)
  | m + 2 => ((rr (m + 1)).1 + (rr (m + 1)).2, 2 * (rr m).1 + (rr (m + 1)).2)

/-- Recursion for `(rr n).1`. -/
private lemma rr_fst_succ : ∀ n, (rr (n + 1)).1 = (rr n).1 + (rr n).2
  | 0 => rfl
  | _ + 1 => rfl

/-- Recursion for `(rr n).2`. -/
private lemma rr_snd_succ_succ (n : ℕ) : (rr (n + 2)).2 = 2 * (rr n).1 + (rr (n + 1)).2 := rfl

/-- The defining recursion of `pq`. -/
private lemma pq_succ3 (n : ℕ) :
    pq (n + 3) = ((pq (n + 1)).1 + (pq n).2, 2 * (pq n).1 + (pq (n + 1)).2) := by
  rw [pq]

/-- Excursions between adjacent columns have odd length, between columns `0` and `2` even. -/
private lemma pq_par : ∀ m, pq (2 * m) = (0, (rr m).2) ∧ pq (2 * m + 1) = ((rr m).1, 0)
  | 0 => ⟨rfl, rfl⟩
  | 1 => ⟨rfl, rfl⟩
  | m + 2 => by
    obtain ⟨h1, h2⟩ := pq_par m
    obtain ⟨h3, h4⟩ := pq_par (m + 1)
    have h3' : pq (2 * m + 1 + 1) = (0, (rr (m + 1)).2) := by
      rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring]; exact h3
    have h4' : pq (2 * (m + 1) + 1) = ((rr (m + 1)).1, 0) := h4
    constructor
    · rw [show 2 * (m + 2) = 2 * m + 1 + 3 by ring, pq_succ3, h3', h2]
      simp [rr_snd_succ_succ]
    · rw [show 2 * (m + 2) + 1 = 2 * (m + 1) + 3 by ring, pq_succ3, h4', h3]
      simp [rr]

/-- `p` vanishes at even lengths. -/
private lemma p_even (i : ℕ) : (pq (2 * i)).1 = 0 := by rw [(pq_par i).1]
/-- `q` at even lengths. -/
private lemma q_even (i : ℕ) : (pq (2 * i)).2 = (rr i).2 := by rw [(pq_par i).1]
/-- `p` at odd lengths. -/
private lemma p_odd (i : ℕ) : (pq (2 * i + 1)).1 = (rr i).1 := by rw [(pq_par i).2]
/-- `q` vanishes at odd lengths. -/
private lemma q_odd (i : ℕ) : (pq (2 * i + 1)).2 = 0 := by rw [(pq_par i).2]

/-- Splitting a sum over `[0, 2m)` into even and odd indices. -/
private lemma sum_range_two_mul (F : ℕ → ℕ) (m : ℕ) :
    ∑ ℓ ∈ range (2 * m), F ℓ = ∑ i ∈ range m, (F (2 * i) + F (2 * i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    ring

/-- The walks to `(0, ±1)`, in terms of `rr`. -/
private lemma S1_eq (m j : ℕ) (hj : j = 2 * m + 3) :
    ∑ c : Fin 3, ∑ ℓ ∈ range j, Ef 0 c ℓ * Ef c 0 (j - 1 - ℓ) =
      ∑ i ∈ range (m + 1), (rr i).1 * (rr (m - i)).1 +
        ∑ i ∈ range (m + 2), (rr i).2 * (rr (m + 1 - i)).2 := by
  subst hj
  rw [Fin.sum_univ_three]
  simp only [Ef, Fin.isValue, Fin.reduceEq, if_true, if_false, and_false, or_false,
    and_self, or_true, and_true]
  have hA : ∑ ℓ ∈ range (2 * m + 3),
      (if ℓ = 0 then 1 else 0) * (if 2 * m + 3 - 1 - ℓ = 0 then 1 else 0) = 0 := by
    apply sum_eq_zero
    intro ℓ _
    split_ifs <;> omega
  have hB : ∑ ℓ ∈ range (2 * m + 3), (pq ℓ).1 * (pq (2 * m + 3 - 1 - ℓ)).1 =
      ∑ i ∈ range (m + 1), (rr i).1 * (rr (m - i)).1 := by
    rw [show 2 * m + 3 = 2 * (m + 1) + 1 by ring, sum_range_succ, sum_range_two_mul, p_even,
      zero_mul, add_zero]
    apply sum_congr rfl
    intro i hi
    rw [mem_range] at hi
    rw [p_even, zero_mul, zero_add, p_odd,
      show 2 * (m + 1) + 1 - 1 - (2 * i + 1) = 2 * (m - i) + 1 by omega, p_odd]
  have hC : ∑ ℓ ∈ range (2 * m + 3), (pq ℓ).2 * (pq (2 * m + 3 - 1 - ℓ)).2 =
      ∑ i ∈ range (m + 2), (rr i).2 * (rr (m + 1 - i)).2 := by
    rw [show 2 * m + 3 = 2 * (m + 1) + 1 by ring, sum_range_succ, sum_range_two_mul,
      sum_range_succ (fun i => (rr i).2 * (rr (m + 1 - i)).2)]
    congr 1
    · apply sum_congr rfl
      intro i hi
      rw [mem_range] at hi
      rw [q_odd, zero_mul, add_zero, q_even,
        show 2 * (m + 1) + 1 - 1 - 2 * i = 2 * (m + 1 - i) by omega, q_even]
    · rw [q_even, show 2 * (m + 1) + 1 - 1 - 2 * (m + 1) = 2 * 0 by omega, q_even]
      simp
  rw [hA, hB, hC, zero_add]

/-- The walks to `(1, 0)` (one direction of the first step), in terms of `rr`. -/
private lemma S2_eq (m j : ℕ) (hj : j = 2 * m + 3) :
    ∑ c : Fin 3, ∑ ℓ ∈ range (j - 1), Ef 0 c ℓ * E0 c (j - 2 - ℓ) =
      (rr m).1 + (rr m).2 + ∑ i ∈ range m, (rr i).2 * (rr (m - 1 - i)).1 := by
  subst hj
  rw [Fin.sum_univ_three]
  simp only [Ef, E0, Fin.isValue, Fin.reduceEq, if_true, if_false, and_false,
    or_false, and_self, and_true, mul_zero, sum_const_zero,
    zero_add, mul_add, sum_add_distrib]
  have e1 : 2 * m + 3 - 1 = 2 * m + 1 + 1 := by omega
  rw [e1]
  have hB : ∑ ℓ ∈ range (2 * m + 1 + 1), (pq ℓ).1 * (if 2 * m + 3 - 2 - ℓ = 0 then 1 else 0) =
      (rr m).1 := by
    rw [sum_range_succ, show 2 * m + 3 - 2 - (2 * m + 1) = 0 by omega, if_pos rfl, mul_one,
      p_odd]
    rw [sum_eq_zero, zero_add]
    intro ℓ hℓ
    rw [mem_range] at hℓ
    rw [if_neg (by omega), mul_zero]
  have hC : ∑ ℓ ∈ range (2 * m + 1 + 1), (pq ℓ).2 * (if 2 * m + 3 - 2 - ℓ = 1 then 1 else 0) =
      (rr m).2 := by
    rw [sum_range_succ, sum_range_succ, show 2 * m + 3 - 2 - (2 * m + 1) = 0 by omega,
      show 2 * m + 3 - 2 - 2 * m = 1 by omega, if_pos rfl, if_neg (by omega), mul_one,
      mul_zero, add_zero, q_even]
    rw [sum_eq_zero, zero_add]
    intro ℓ hℓ
    rw [mem_range] at hℓ
    rw [if_neg (by omega), mul_zero]
  have hD : ∑ ℓ ∈ range (2 * m + 1 + 1),
      (pq ℓ).2 * (if 2 ≤ 2 * m + 3 - 2 - ℓ then (pq (2 * m + 3 - 2 - ℓ - 2)).1 else 0) =
      ∑ i ∈ range m, (rr i).2 * (rr (m - 1 - i)).1 := by
    rw [sum_range_succ, sum_range_succ, if_neg (by omega), if_neg (by omega), mul_zero,
      mul_zero, add_zero, add_zero, sum_range_two_mul]
    apply sum_congr rfl
    intro i hi
    rw [mem_range] at hi
    rw [q_odd, zero_mul, add_zero, q_even, if_pos (by omega),
      show 2 * m + 3 - 2 - 2 * i - 2 = 2 * (m - 1 - i) + 1 by omega, p_odd]
  rw [hB, hC, hD]
  ring

open PowerSeries

/-- The generating function of `(rr m).1`. -/
private noncomputable def PP : PowerSeries ℤ := mk fun i => ((rr i).1 : ℤ)

/-- The generating function of `(rr m).2`. -/
private noncomputable def QQ : PowerSeries ℤ := mk fun i => ((rr i).2 : ℤ)

/-- The functional equation of `PP`. -/
private lemma PP_eq : PP = 1 + X * (PP + QQ) := by
  ext n
  rcases n with _ | n
  · simp [PP, rr]
  · rw [map_add, coeff_succ_X_mul, coeff_one, map_add]
    simp [PP, QQ, rr_fst_succ]

/-- The functional equation of `QQ`. -/
private lemma QQ_eq : QQ = X * (1 + QQ + X * (PP + PP)) := by
  ext n
  rcases n with _ | _ | n
  · simp [QQ, rr]
  · rw [coeff_succ_X_mul]
    simp [QQ, PP, rr]
  · rw [coeff_succ_X_mul, map_add, map_add, coeff_succ_X_mul, coeff_one]
    simp [QQ, PP, rr_snd_succ_succ]
    ring

/-- Solving for `PP`. -/
private lemma PP_sol : (1 - 2 * X) * (1 + X ^ 2) * PP = 1 - X + X ^ 2 := by
  linear_combination (1 - X) * PP_eq + X * QQ_eq

/-- Solving for `QQ`. -/
private lemma QQ_sol : (1 - 2 * X) * (1 + X ^ 2) * QQ = X + X ^ 2 := by
  linear_combination (1 - X) * QQ_eq + 2 * X ^ 2 * PP_eq

/-- Coefficients of a product of two generating functions. -/
private lemma coeff_mul_PQ (m : ℕ) (f g : ℕ → ℕ) :
    coeff m (mk (fun i => (f i : ℤ)) * mk (fun i => (g i : ℤ))) =
      ((∑ i ∈ range (m + 1), f i * g (m - i) : ℕ) : ℤ) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp

/-- The generating function identity from the formula for `a (m + 2)`. -/
private theorem gf_main (a : ℕ → ℕ) (h0 : a 0 = 1) (h1 : a 1 = 0)
    (h : ∀ m, a (m + 2) =
      2 * ((rr m).1 + (rr m).2 + ∑ i ∈ range m, (rr i).2 * (rr (m - 1 - i)).1) +
        2 * (∑ i ∈ range (m + 1), (rr i).1 * (rr (m - i)).1 +
          ∑ i ∈ range (m + 2), (rr i).2 * (rr (m + 1 - i)).2)) :
    mk (fun n => (a n : ℤ)) * ((1 + X ^ 2) ^ 2 * (1 - 2 * X) ^ 2) =
      -6 * X ^ 7 + 10 * X ^ 6 - 18 * X ^ 5 + 27 * X ^ 4 - 14 * X ^ 3 + 10 * X ^ 2 - 4 * X + 1 := by
  set F : PowerSeries ℤ :=
    X ^ 2 * (PP * PP) + X * (QQ * QQ) + X ^ 2 * PP + X ^ 2 * QQ + X ^ 3 * (QQ * PP) with hF
  have hA : mk (fun n => (a n : ℤ)) = 1 + F + F := by
    ext n
    rcases n with _ | _ | m
    · simp [hF, h0]
    · simp [hF, h1, coeff_succ_X_mul, coeff_X_pow_mul', QQ, rr]
    · rw [coeff_mk, h m, map_add, map_add, coeff_one, if_neg (by omega)]
      have hF2 : coeff (m + 1 + 1) F =
          ((∑ i ∈ range (m + 1), (rr i).1 * (rr (m - i)).1 : ℕ) : ℤ) +
          ((∑ i ∈ range (m + 2), (rr i).2 * (rr (m + 1 - i)).2 : ℕ) : ℤ) +
          (rr m).1 + (rr m).2 +
          ((∑ i ∈ range m, (rr i).2 * (rr (m - 1 - i)).1 : ℕ) : ℤ) := by
        rw [hF, map_add, map_add, map_add, map_add, coeff_succ_X_mul, coeff_X_pow_mul',
          coeff_X_pow_mul', coeff_X_pow_mul', coeff_X_pow_mul', if_pos (by omega),
          if_pos (by omega), if_pos (by omega)]
        simp only [PP, QQ, coeff_mul_PQ, coeff_mk, show m + 1 + 1 - 2 = m by omega]
        rcases m with _ | m
        · simp
        · rw [if_pos (by omega), show m + 1 + 1 + 1 - 3 = m by omega]
          simp only [show m + 1 - 1 = m by omega, show m + 1 + 1 + 1 = m + 1 + 2 by omega]
      rw [hF2]
      push_cast
      ring
  rw [hA]
  have key : (1 + F + F) * ((1 + X ^ 2) ^ 2 * (1 - 2 * X) ^ 2) =
      ((1 - 2 * X) * (1 + X ^ 2)) ^ 2 + 2 * (X ^ 2 * ((1 - 2 * X) * (1 + X ^ 2) * PP) ^ 2 +
        X * ((1 - 2 * X) * (1 + X ^ 2) * QQ) ^ 2 +
        X ^ 2 * ((1 - 2 * X) * (1 + X ^ 2)) * ((1 - 2 * X) * (1 + X ^ 2) * PP) +
        X ^ 2 * ((1 - 2 * X) * (1 + X ^ 2)) * ((1 - 2 * X) * (1 + X ^ 2) * QQ) +
        X ^ 3 * ((1 - 2 * X) * (1 + X ^ 2) * QQ) * ((1 - 2 * X) * (1 + X ^ 2) * PP)) := by
    rw [hF]; ring
  rw [key, PP_sol, QQ_sol]
  ring

/-- The first term. -/
private lemma a_zero : a 0 = 1 := by
  rw [a_eq_GLs 0 (by omega), show 2 * 0 = 0 from rfl, GLs_zero, if_pos rfl]

/-- The number of closed walks of length `2 (m + 2)`, from the decomposition. -/
private lemma a_formula (m : ℕ) : a (m + 2) =
    2 * ((rr m).1 + (rr m).2 + ∑ i ∈ Finset.range m, (rr i).2 * (rr (m - 1 - i)).1) +
      2 * (∑ i ∈ Finset.range (m + 1), (rr i).1 * (rr (m - i)).1 +
        ∑ i ∈ Finset.range (m + 2), (rr i).2 * (rr (m + 1 - i)).2) := by
  rw [a_eq_GLs (m + 2) (by omega), GLs_Q _ (by omega), Fin.sum_univ_three]
  have n0 : nb 0 = (1, 0) := rfl
  have n1 : nb 1 = (0, dir true) := rfl
  have n2 : nb 2 = (0, dir false) := rfl
  rw [n0, n1, n2, Q10_card (2 * (m + 2) - 1) (by omega), Q1_card true (2 * (m + 2) - 1) (by omega),
    Q1_card false (2 * (m + 2) - 1) (by omega)]
  simp only [exc_Ef, exc_E0, Fintype.sum_bool]
  rw [S1_eq m (2 * (m + 2) - 1) (by omega), S2_eq m (2 * (m + 2) - 1) (by omega)]
  ring

/-- Ralf Stephan's conjecture holds: the generating function of A022445 is
`(-6x⁷ + 10x⁶ - 18x⁵ + 27x⁴ - 14x³ + 10x² - 4x + 1) / ((1 + x²)² (1 - 2x)²)`. -/
theorem result : statement := gf_main a a_zero a_one a_formula

end Math0.Frontier.A022445

#math0_settles Math0.Frontier.A022445.result Math0.Statements.A022445.statement
