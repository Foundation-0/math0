/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A081200
import Math0.Audit

/-!
# Collinear 5-point sets in the grid `{0, …, 4}^n` (A081200)

We prove Hardin's conjecture in OEIS A081200: the number of 5-element subsets of the grid
`{0, …, 4}^n` that lie on a real line is `a n`, the 6th binomial transform of `0, 1, 0, 1, …`.

**Lines are words.** A word `w ∈ {0, 1, 2, 3, 4, ↑, ↓}^n` (here `Fin 7`, with `5 = ↑`, `6 = ↓`)
gives the five points `pt w t` (`t = 0, …, 4`) whose `i`-th coordinate is `c` if `w i = c` is a
constant, `t` if `w i = ↑` and `4 - t` if `w i = ↓` (`ev`). If some letter is `↑` or `↓` (the
set `NC n` of non-constant words) these points are distinct and collinear (`card_line`,
`line_collinear`). Conversely (`exists_line`), let `s` be a collinear set of 5 grid points.
Collinearity gives the integer identities `(x_i - z_i)(y_j - z_j) = (x_j - z_j)(y_i - z_i)`
for `x, y, z ∈ s` (`P_of_collinear`). Hence a coordinate that takes the same value at two
distinct points of `s` is constant on `s`; since `s` has two distinct points, some coordinate
`i₀` is injective on `s`, so it takes each value `t ∈ {0, …, 4}` at exactly one point `q t`.
For every other coordinate `j`, the identity with `x = q t, y = q 4, z = q 0` says
`t (q₄ - q₀) = 4 (q_t - q₀)` (values at `j`); a finite check (`H`) shows the only solutions
in `{0, …, 4}` are the constant, `t ↦ t` and `t ↦ 4 - t`. So `s` is the line of a word.

**Counting.** Two words in `NC n` give the same line iff they are equal or one is the other with
`↑` and `↓` swapped (`line_eq`, `line_rev`; the finite check is `F`), and this swap has no fixed
points on `NC n`. So the number of lines is `|NC n| / 2 = (7^n - 5^n)/2`, and
`2 a n = 7^n - 5^n` by the binomial theorem for `(6 + 1)^n` and `(6 - 1)^n` (`a_eq`).
-/

namespace Math0.Frontier.A081200
open Math0.Statements.A081200

/-- The value at parameter `t` of a letter `c`: the constant `c` for `c < 5`, `t` for `c = 5`
(increasing), `4 - t` for `c = 6` (decreasing). -/
private def ev (c : Fin 7) (t : Fin 5) : Fin 5 :=
  if h : c.val < 5 then ⟨c.val, h⟩ else if c.val = 5 then t else Fin.rev t

/-- Swap the two non-constant letters `5` and `6`. -/
private def rw7 (c : Fin 7) : Fin 7 := if c = 5 then 6 else if c = 6 then 5 else c

/-- The letter of a coordinate whose values at parameters `0` and `4` are `u0` and `u4`. -/
private def code (u0 u4 : Fin 5) : Fin 7 :=
  if u0 = u4 then ⟨u0.val, by omega⟩ else if u0.val = 0 then 5 else 6

/-- The point with parameter `t` on the line of the word `w`. -/
private def pt {n : ℕ} (w : Fin n → Fin 7) (t : Fin 5) : Fin n → Fin 5 := fun i => ev (w i) t

/-- The five points of the line of the word `w`. -/
private def line {n : ℕ} (w : Fin n → Fin 7) : Finset (Fin n → Fin 5) :=
  Finset.univ.image (pt w)

/-- The constant letters `0, …, 4`. -/
private def T : Finset (Fin 7) := Finset.univ.filter (fun c => c.val < 5)

/-- The non-constant words: those having some letter `5` or `6`. -/
private def NC (n : ℕ) : Finset (Fin n → Fin 7) := Finset.univ \ Fintype.piFinset (fun _ => T)

/-- Membership in `NC`. -/
private lemma mem_NC {n : ℕ} {w : Fin n → Fin 7} : w ∈ NC n ↔ ∃ i, 5 ≤ (w i).val := by
  simp [NC, T, Fintype.mem_piFinset]

/-! ### Finite checks -/

/-- A non-constant letter gives an injective coordinate. -/
private lemma ev_inj : ∀ c : Fin 7, 5 ≤ c.val → ∀ t u, ev c t = ev c u → t = u := by
  decide +kernel

/-- A constant letter gives a constant coordinate. -/
private lemma ev_const : ∀ c : Fin 7, c.val < 5 → ∀ t, ev c t = ev c 0 := by
  decide +kernel

/-- A non-constant letter gives an involution. -/
private lemma ev_invol : ∀ c : Fin 7, 5 ≤ c.val → ∀ t, ev c (ev c t) = t := by
  decide +kernel

/-- Swapping the direction letters reverses the parameter. -/
private lemma ev_rw7 : ∀ c : Fin 7, ∀ t, ev (rw7 c) t = ev c (Fin.rev t) := by
  decide +kernel

/-- Swapping keeps non-constant letters non-constant and moves them. -/
private lemma rw7_ge : ∀ c : Fin 7, 5 ≤ c.val → 5 ≤ (rw7 c).val ∧ rw7 c ≠ c := by
  decide +kernel

/-- Each coordinate is an affine function of the parameter. -/
private lemma ev_affine : ∀ c : Fin 7, ∀ t : Fin 5,
    ((ev c t : ℕ) : ℤ) = (ev c 0 : ℕ) + (t : ℕ) * (((ev c 1 : ℕ) : ℤ) - (ev c 0 : ℕ)) := by
  decide +kernel

/-- An affine relation `t (u4 - u0) = 4 (v - u0)` between a coordinate on `{0, …, 4}` and the
parameter forces the coordinate to be constant, `t` or `4 - t`. -/
private lemma H : ∀ u0 u1 u4 t v : Fin 5,
    ((u4 : ℕ) : ℤ) - (u0 : ℕ) = (((u1 : ℕ) : ℤ) - (u0 : ℕ)) * 4 →
    ((t : ℕ) : ℤ) * (((u4 : ℕ) : ℤ) - (u0 : ℕ)) = (((v : ℕ) : ℤ) - (u0 : ℕ)) * 4 →
    ev (code u0 u4) t = v := by
  decide +kernel

/-- If two words describe the same points with the reparametrisation `ev a ∘ ev a'`, then the
words agree (when `a' = a`) or are swaps of each other (otherwise). -/
private lemma F : ∀ a a' b b' : Fin 7, 5 ≤ a.val → 5 ≤ a'.val →
    (∀ t, ev b (ev a (ev a' t)) = ev b' t) → (a' = a → b' = b) ∧ (a' ≠ a → b' = rw7 b) := by
  decide +kernel

/-! ### Lines of words -/

/-- The points of the line of a non-constant word are distinct. -/
private lemma pt_inj {n : ℕ} {w : Fin n → Fin 7} (hw : w ∈ NC n) : Function.Injective (pt w) := by
  obtain ⟨i, hi⟩ := mem_NC.1 hw
  intro t u h
  exact ev_inj _ hi t u (congrFun h i)

/-- The line of a non-constant word has 5 points. -/
private lemma card_line {n : ℕ} {w : Fin n → Fin 7} (hw : w ∈ NC n) : (line w).card = 5 := by
  rw [line, Finset.card_image_of_injective _ (pt_inj hw)]
  simp

/-- The line of a word is collinear. -/
private lemma line_collinear {n : ℕ} (w : Fin n → Fin 7) :
    Collinear ℝ (toReal n '' (line w : Set (Fin n → Fin 5))) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨toReal n (pt w 0), fun i => ((ev (w i) 1 : ℕ) : ℝ) - (ev (w i) 0 : ℕ), ?_⟩
  rintro p ⟨x, hx, rfl⟩
  simp only [line, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
  obtain ⟨t, rfl⟩ := hx
  refine ⟨((t : ℕ) : ℝ), ?_⟩
  funext i
  simp only [toReal, pt, vadd_eq_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h := congrArg (fun z : ℤ => (z : ℝ)) (ev_affine (w i) t)
  push_cast at h
  linarith

/-- Reversing all direction letters gives the same line. -/
private lemma line_rev {n : ℕ} (w : Fin n → Fin 7) : line (fun j => rw7 (w j)) = line w := by
  have h : ∀ t, pt (fun j => rw7 (w j)) t = pt w (Fin.rev t) :=
    fun t => funext fun j => ev_rw7 _ _
  ext x
  simp only [line, Finset.mem_image, Finset.mem_univ, true_and, h]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨Fin.rev t, by rw [Fin.rev_rev]⟩

/-- Two non-constant words with the same line are equal or swaps of each other. -/
private lemma line_eq {n : ℕ} {w w' : Fin n → Fin 7} (hw : w ∈ NC n) (hw' : w' ∈ NC n)
    (h : line w' = line w) : w' = w ∨ w' = fun j => rw7 (w j) := by
  obtain ⟨i₀, hi₀⟩ := mem_NC.1 hw
  have hpt : ∀ t, pt w (ev (w i₀) (ev (w' i₀) t)) = pt w' t := by
    intro t
    have : pt w' t ∈ line w := h ▸ Finset.mem_image_of_mem _ (Finset.mem_univ t)
    simp only [line, Finset.mem_image, Finset.mem_univ, true_and] at this
    obtain ⟨u, hu⟩ := this
    have hu' : ev (w i₀) u = ev (w' i₀) t := congrFun hu i₀
    rw [← hu', ev_invol _ hi₀, hu]
  have ha' : 5 ≤ (w' i₀).val := by
    by_contra hlt'
    have hlt : (w' i₀).val < 5 := by omega
    have e : pt w' 1 = pt w' 0 := by rw [← hpt 1, ← hpt 0, ev_const _ hlt 1]
    exact absurd (pt_inj hw' e) (by decide)
  have hj : ∀ j t, ev (w j) (ev (w i₀) (ev (w' i₀) t)) = ev (w' j) t :=
    fun j t => congrFun (hpt t) j
  by_cases he : w' i₀ = w i₀
  · left
    funext j
    exact (F _ _ _ _ hi₀ ha' (hj j)).1 he
  · right
    funext j
    exact (F _ _ _ _ hi₀ ha' (hj j)).2 he

/-! ### Collinear sets are lines -/

/-- Collinearity of grid points as integer identities between coordinate differences. -/
private lemma P_of_collinear {n : ℕ} {s : Finset (Fin n → Fin 5)}
    (hs : Collinear ℝ (toReal n '' (s : Set (Fin n → Fin 5))))
    {x y z : Fin n → Fin 5} (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) (i j : Fin n) :
    (((x i : ℕ) : ℤ) - (z i : ℕ)) * (((y j : ℕ) : ℤ) - (z j : ℕ)) =
      (((x j : ℕ) : ℤ) - (z j : ℕ)) * (((y i : ℕ) : ℤ) - (z i : ℕ)) := by
  rw [collinear_iff_of_mem (Set.mem_image_of_mem _ (Finset.mem_coe.2 hz))] at hs
  obtain ⟨v, hv⟩ := hs
  obtain ⟨r, hr⟩ := hv _ (Set.mem_image_of_mem _ (Finset.mem_coe.2 hx))
  obtain ⟨r', hr'⟩ := hv _ (Set.mem_image_of_mem _ (Finset.mem_coe.2 hy))
  have e1 := congrFun hr i
  have e2 := congrFun hr j
  have e3 := congrFun hr' i
  have e4 := congrFun hr' j
  simp only [toReal, vadd_eq_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 e4
  have : (((x i : ℕ) : ℝ) - (z i : ℕ)) * (((y j : ℕ) : ℝ) - (z j : ℕ)) =
      (((x j : ℕ) : ℝ) - (z j : ℕ)) * (((y i : ℕ) : ℝ) - (z i : ℕ)) := by
    rw [e1, e2, e3, e4]; ring
  exact_mod_cast this

/-- Every collinear 5-point set of grid points is the line of a non-constant word. -/
private lemma exists_line {n : ℕ} {s : Finset (Fin n → Fin 5)} (hcard : s.card = 5)
    (hs : Collinear ℝ (toReal n '' (s : Set (Fin n → Fin 5)))) : ∃ w ∈ NC n, line w = s := by
  obtain ⟨y, hy, z, hz, hyz⟩ := Finset.one_lt_card.1 (by omega : 1 < s.card)
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hyz
  have key : ∀ x ∈ s, ∀ x' ∈ s, x i₀ = x' i₀ → x = x' := by
    intro x hx x' hx' h
    by_contra hne
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
    have hj' : ((x' j : ℕ) : ℤ) - (x j : ℕ) ≠ 0 := by
      intro h0
      apply hj
      apply Fin.ext
      omega
    have h1 := P_of_collinear hs hy hx' hx i₀ j
    have h2 := P_of_collinear hs hz hx' hx i₀ j
    rw [h, sub_self, mul_zero] at h1 h2
    have e1 := (mul_eq_zero.1 h1).resolve_right hj'
    have e2 := (mul_eq_zero.1 h2).resolve_right hj'
    apply hi₀
    apply Fin.ext
    omega
  have himg : s.image (fun x => x i₀) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn (fun x hx x' hx' h => key x hx x' hx' h), hcard]
    simp
  have hex : ∀ t : Fin 5, ∃ x ∈ s, x i₀ = t := by
    intro t
    have : t ∈ s.image (fun x => x i₀) := himg ▸ Finset.mem_univ t
    simpa using this
  choose q hqs hqi using hex
  have hpt : ∀ t, pt (fun j => code (q 0 j) (q 4 j)) t = q t := by
    intro t
    funext j
    have e0 : ((q 0 i₀ : ℕ) : ℤ) = 0 := by rw [hqi]; rfl
    have e1 : ((q 1 i₀ : ℕ) : ℤ) = 1 := by rw [hqi]; rfl
    have e4 : ((q 4 i₀ : ℕ) : ℤ) = 4 := by rw [hqi]; rfl
    have et : ((q t i₀ : ℕ) : ℤ) = (t : ℕ) := by rw [hqi]
    have h1 := P_of_collinear hs (hqs 1) (hqs 4) (hqs 0) i₀ j
    have h2 := P_of_collinear hs (hqs t) (hqs 4) (hqs 0) i₀ j
    rw [e0, e1, e4] at h1
    rw [e0, e4, et] at h2
    exact H _ (q 1 j) _ _ _ (by linear_combination h1) (by linear_combination h2)
  refine ⟨fun j => code (q 0 j) (q 4 j), ?_, ?_⟩
  · rw [mem_NC]
    refine ⟨i₀, ?_⟩
    simp only [hqi]
    decide
  · have hl : line (fun j => code (q 0 j) (q 4 j)) = Finset.univ.image q := by
      simp only [line]
      congr 1
      funext t
      exact hpt t
    rw [hl]
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨t, rfl⟩ := hx
      exact hqs t
    · rw [hcard, Finset.card_image_of_injective]
      · simp
      intro t u h
      have := congrFun h i₀
      rwa [hqi, hqi] at this

/-! ### Counting -/

/-- The collinear 5-point sets are exactly the lines of non-constant words. -/
private lemma set_eq (n : ℕ) :
    {s : Finset (Fin n → Fin 5) | s.card = 5 ∧ Collinear ℝ (toReal n '' (s : Set (Fin n → Fin 5)))}
      = ↑((NC n).image line) := by
  ext s
  simp only [Set.mem_ofPred_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe]
  constructor
  · rintro ⟨hc, hs⟩
    exact exists_line hc hs
  · rintro ⟨w, hw, rfl⟩
    exact ⟨card_line hw, line_collinear w⟩

/-- There are `7^n - 5^n` non-constant words. -/
private lemma card_NC (n : ℕ) : (NC n).card = 7 ^ n - 5 ^ n := by
  rw [NC, Finset.card_sdiff_of_subset (Finset.subset_univ _), Fintype.card_piFinset]
  have hT : T.card = 5 := by decide
  simp [hT]

/-- Each line comes from exactly two non-constant words. -/
private lemma two_mul_card (n : ℕ) : 2 * ((NC n).image line).card = (NC n).card := by
  rw [Finset.card_eq_sum_card_image line (NC n), Finset.sum_const_nat (m := 2), mul_comm]
  intro s hs
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hs
  obtain ⟨i₀, hi₀⟩ := mem_NC.1 hw
  have hrev : (fun j => rw7 (w j)) ∈ NC n := mem_NC.2 ⟨i₀, (rw7_ge _ hi₀).1⟩
  have hne : w ≠ fun j => rw7 (w j) := fun e => (rw7_ge _ hi₀).2 (congrFun e i₀).symm
  have : (NC n).filter (fun w' => line w' = line w) = {w, fun j => rw7 (w j)} := by
    ext w'
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hw', h⟩
      exact line_eq hw hw' h
    · rintro (rfl | rfl)
      · exact ⟨hw, rfl⟩
      · exact ⟨hrev, line_rev w⟩
  rw [this, Finset.card_pair hne]

/-- `2 a n = 7^n - 5^n`, by the binomial theorem for `(6 + 1)^n` and `(6 - 1)^n`. -/
private lemma a_eq (n : ℕ) : 2 * a n + 5 ^ n = 7 ^ n := by
  have hterm : ∀ k : ℕ, ((k % 2 : ℕ) : ℤ) * 2 = 1 - (-1) ^ k := by
    intro k
    rcases Nat.even_or_odd k with he | ho
    · rw [Nat.even_iff.1 he, he.neg_one_pow]
      norm_num
    · rw [Nat.odd_iff.1 ho, ho.neg_one_pow]
      norm_num
  have h7 : (7 : ℤ) ^ n = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * 6 ^ (n - k) := by
    rw [show (7 : ℤ) = 1 + 6 by norm_num, add_pow]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have h5 : (5 : ℤ) ^ n =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * 6 ^ (n - k) * (-1) ^ k := by
    rw [show (5 : ℤ) = -1 + 6 by norm_num, add_pow]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have key : ((2 * a n : ℕ) : ℤ) = 7 ^ n - 5 ^ n := by
    rw [h7, h5, ← Finset.sum_sub_distrib]
    simp only [a, binomialTransform, A000035, Nat.cast_mul, Nat.cast_sum, Nat.cast_pow,
      Nat.cast_ofNat]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    linear_combination ((n.choose k : ℤ) * 6 ^ (n - k)) * hterm k
  have : ((2 * a n : ℕ) : ℤ) + 5 ^ n = 7 ^ n := by rw [key]; ring
  exact_mod_cast this

/-- Hardin's conjecture (A081200): the number of collinear 5-point subsets of `{0, …, 4}^n`
is `a n`. -/
theorem result : statement := by
  intro n
  rw [set_eq, Set.ncard_coe_finset]
  have h1 := two_mul_card n
  have h2 := card_NC n
  have h3 := a_eq n
  omega

end Math0.Frontier.A081200

#math0_settles Math0.Frontier.A081200.result Math0.Statements.A081200.statement
