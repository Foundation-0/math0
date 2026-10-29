/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A333650: domino towers counted by number of bricks and height

Source: https://oeis.org/A333650, _Peter Kagey_, Mar 31 2020 (the first conjecture is the entry
author's; the next three are later comments). Verbatim:
> Conjecture: For n > 1, T(n,2) = A000071(n+2).
>
> Conjecture: T(n,n-1) = A339252(n-2). - _Peter Kagey_, Nov 21 2020
>
> Conjecture: T(n,n-2) = A339254(n-3). - _Peter Luschny_, Nov 29 2020
>
> Conjecture: T(n,n-3) = A339029(n-4). - _Peter Luschny_, Dec 01 2020
>
> From _Peter Luschny_, Dec 01 2020: (Start)
> The above conjectures can be summarized as follows:
> T(2*n + k, n + k) = d_{n}(n + k - 1) for k >= 1 and 0 <= n <= 3, where
> d_{0}(m) = 2^(m-1)*2;
> d_{1}(m) = 2^(m-3)*(10 + 6*m);
> d_{2}(m) = 2^(m-5)*(70 + 43*m + 9*m^2);
> d_{3}(m) = 2^(m-7)*(588 + 367*m + 84*m^2 + 9*m^3). (End)

The entry's definition: "Triangle read by rows: T(n,k) gives the number of domino towers of
height k consisting of n bricks." and "The towers must have a contiguous base of bricks, and each
brick must be at least half supported below by another brick. The stacks do not need to be
stable." Offset `1`: rows `n ≥ 1`, columns `1 ≤ k ≤ n`.

## Encoding

* Horizontal positions are measured in half bricks. A brick of layer `i` (layer `0` is the
  bottom) with left end `x ∈ ℤ` occupies `[x, x + 2)`. A tower is the list `t = [t₀, …, t_{k-1}]`
  of its layers, bottom first, each layer being the finset of left ends of its bricks. Its height
  is its number `k` of layers (all nonempty) and its number of bricks is `∑ᵢ #tᵢ` (`IsTower`).
* Towers are counted up to horizontal translation, so the base (a contiguous row of `b ≥ 1`
  bricks side by side) is normalised to `t₀ = {0, 2, …, 2b - 2}` (`base b`). Mirror images are
  different towers (`T(2,2) = 2`).
* Domino towers (Gouyou-Beauchamps–Viennot, Bétréma–Penaud, Zeilberger, all cited in the entry)
  are laid in the brick-wall pattern: consecutive layers are staggered by half a brick, i.e. the
  bricks of layer `i` have left ends `≡ i (mod 2)`. The entry's data force this reading: allowing
  a brick exactly on top of another would give `T(2,2) = 3` and `T(n,n) = 3^(n-1)`, whereas the
  entry lists `T(2,2) = 2` and states `T(n,n) = 2^(n-1)`; its picture of the four towers counted
  by `T(3,2) = 4` shows staggered layers only.
* The bricks of a layer do not overlap: distinct left ends in one layer differ by at least `2`
  (this follows from the staggering, but is stated explicitly).
* "Each brick must be at least half supported below by another brick": a brick `[x, x + 2)` of
  layer `i + 1` overlaps some brick `[y, y + 2)` of layer `i` in a segment of length
  `2 - |x - y| ≥ 1`, i.e. `|x - y| ≤ 1`. Stability is not required.
* `T n k` is the number (`Set.ncard`) of towers of height `k` with `n` bricks. The computable
  `Tc n k` builds the towers layer by layer (each layer above the base is a nonempty set of
  positions `y ± 1` with `y` in the layer below); `T_eq_Tc` proves `T n k = Tc n k`, so in
  particular the set of towers is finite.
* `a` is the triangle read by rows with the OEIS offset `1`; `a_spec` proves
  `a (n * (n - 1) / 2 + k) = T n k` for `1 ≤ k ≤ n`. `a_data` checks all 55 terms listed in the
  entry's DATA section (rows `1` to `10`) in the kernel.
* The other sequences are encoded by their own OEIS definitions and checked against their listed
  terms: A000071 (offset 1) is `Fibonacci(n) - 1`; A339252 and A339254 (offset 0) are given by
  their defining recurrences; A339029 (offset 0) is the coefficient sequence of the power series
  `(1 + 4x - 20x^2 + 8x^3 + 33x^4 - 4x^5 - 33x^6)/(1 - 2x)^4`, the inverse of `(1 - 2x)^4` being
  taken in `ℤ⟦X⟧` (`invOfUnit`). All four are `ℤ`-valued, and `T` is cast to `ℤ`.
* `statement` is the conjunction of the four conjectures. The first carries its own range
  `n > 1`. The other three state no range; they are read for every `n` at which the index of the
  right-hand sequence (offset `0`) is a natural number, i.e. `n ≥ 2`, `n ≥ 3`, `n ≥ 4`
  respectively (equivalently, the column `n - 1`, `n - 2`, `n - 3` is at least `1`), so the
  natural-number subtractions below are exact.
* Luschny's summary is a reformulation, through the closed forms of A339252, A339254, A339029
  listed in those entries, of the last three conjectures (on smaller ranges of `n`) together with
  the formula `T(n,n) = 2^(n-1)` stated in the entry; it is not formalized separately.
* `statement_check` verifies the four identities on the rows `n ≤ 10` (a consistency check of
  the offsets, not a proof).
-/

namespace Math0.Statements.A333650

open Finset

/-! ### Domino towers -/

/-- The base of `b` bricks side by side: left ends `0, 2, …, 2b - 2`. -/
def base (b : ℕ) : Finset ℤ := (range b).image fun j : ℕ => 2 * (j : ℤ)

/-- `t = [t₀, …, t_{k-1}]` is a domino tower of height `k` with `n` bricks: `tᵢ` is the finset of
left ends of the bricks of layer `i` (layer `0` at the bottom), a brick with left end `x`
occupying `[x, x + 2)` in half-brick units; the base is translated to start at `0`. -/
def IsTower (n k : ℕ) (t : List (Finset ℤ)) : Prop :=
  -- `k` layers, none of them empty
  t.length = k ∧ (∀ L ∈ t, L.Nonempty) ∧
  -- the bottom layer is a contiguous row of `b ≥ 1` bricks, translated to start at `0`
  (∃ b, 0 < b ∧ t.head? = some (base b)) ∧
  -- the bricks of a layer do not overlap
  (∀ L ∈ t, ∀ x ∈ L, ∀ y ∈ L, x ≠ y → 2 ≤ |x - y|) ∧
  -- brick-wall pattern: layer `i` is shifted by `i` half bricks
  (∀ (i : ℕ) (hi : i < t.length), ∀ x ∈ t[i], Even (x - i)) ∧
  -- each brick above the base overlaps a brick of the layer below by at least half a brick
  (∀ (i : ℕ) (hi : i + 1 < t.length), ∀ x ∈ t[i + 1], ∃ y ∈ t[i], |x - y| ≤ 1) ∧
  -- `n` bricks in total
  (t.map Finset.card).sum = n

/-- A333650: `T n k` is the number of domino towers of height `k` consisting of `n` bricks. -/
noncomputable def T (n k : ℕ) : ℕ := {t | IsTower n k t}.ncard

/-! ### Computing `T` -/

/-- The left ends of the bricks that a layer `L` supports in the next layer: `y ± 1`, `y ∈ L`. -/
def supported (L : Finset ℤ) : Finset ℤ := L.image (· - 1) ∪ L.image (· + 1)

/-- `ways L h m`: the number of ways to put `h` further nonempty layers, with `m` bricks in total,
on top of the layer `L`, each layer consisting of positions supported by the layer below. -/
def ways (L : Finset ℤ) : ℕ → ℕ → ℕ
  | 0, m => if m = 0 then 1 else 0
  | h + 1, m => ∑ j ∈ Icc 1 (m - h), ∑ L' ∈ (supported L).powersetCard j, ways L' h (m - j)

/-- Computable version of `T` (see `T_eq_Tc`): sum over the size `b` of the base. -/
def Tc (n k : ℕ) : ℕ := if k = 0 then 0 else ∑ b ∈ Icc 1 n, ways (base b) (k - 1) (n - b)

/-- Row and column of the `i`-th term of a triangle read by rows, starting the search at row `n`
(`fuel` bounds the number of rows visited). -/
def rowCol : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, n, i => (n, i)
  | fuel + 1, n, i => if i ≤ n then (n, i) else rowCol fuel (n + 1) (i - n)

/-- A333650 read by rows, with the OEIS offset `1`: `a 1 = T 1 1`, `a 2 = T 2 1`, `a 3 = T 2 2`,
`a 4 = T 3 1`, … (see `a_spec`). -/
def a (i : ℕ) : ℕ := Tc (rowCol i 1 i).1 (rowCol i 1 i).2

/-- The definition reproduces the 55 terms listed in OEIS (rows 1 to 10), kernel-checked. -/
theorem a_data : (List.range 55).map (fun i => a (i + 1)) =
    [1, 1, 2, 1, 4, 4, 1, 7, 11, 8, 1, 12, 24, 28, 16, 1, 20, 52, 70, 68, 32, 1, 33, 110, 168,
      193, 160, 64, 1, 54, 228, 401, 497, 510, 368, 128, 1, 88, 467, 944, 1257, 1412, 1304, 832,
      256, 1, 143, 949, 2187, 3172, 3736, 3879, 3248, 1856, 512] := by
  decide +kernel

/-! ### `T = Tc` -/

/-- `s` (bottom first) is a stack of nonempty layers on top of the layer `L`, each consisting of
positions supported by the layer below it. -/
def Stack : Finset ℤ → List (Finset ℤ) → Prop
  | _, [] => True
  | L, L' :: s => L'.Nonempty ∧ L' ⊆ supported L ∧ Stack L' s

/-- The finset of the stacks counted by `ways L h m`. -/
def stackSet (L : Finset ℤ) : ℕ → ℕ → Finset (List (Finset ℤ))
  | 0, m => if m = 0 then {[]} else ∅
  | h + 1, m => (Icc 1 (m - h)).biUnion fun j =>
      ((supported L).powersetCard j).biUnion fun L' => (stackSet L' h (m - j)).image (L' :: ·)

theorem length_le_sum : ∀ {L : Finset ℤ} {s : List (Finset ℤ)}, Stack L s →
    s.length ≤ (s.map Finset.card).sum
  | _, [], _ => by simp
  | _, L' :: s, ⟨hne, _, hs⟩ => by
    have h1 := length_le_sum hs
    have h2 := hne.card_pos
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

theorem mem_stacks (h : ℕ) : ∀ (L : Finset ℤ) (m : ℕ) (s : List (Finset ℤ)),
    s ∈ stackSet L h m ↔ s.length = h ∧ Stack L s ∧ (s.map Finset.card).sum = m := by
  induction h with
  | zero =>
    intro L m s
    rcases s with _ | ⟨L', s⟩
    · by_cases hm : m = 0 <;> simp [stackSet, hm, Stack, eq_comm]
    · by_cases hm : m = 0 <;> simp [stackSet, hm]
  | succ h ih =>
    intro L m s
    rcases s with _ | ⟨L', s⟩
    · simp [stackSet]
    · simp only [stackSet, mem_biUnion, mem_image, mem_Icc, mem_powersetCard, ih,
        List.cons.injEq, List.length_cons, List.map_cons, List.sum_cons, Stack]
      constructor
      · rintro ⟨j, ⟨hj1, hj2⟩, L'', ⟨hsub, hcard⟩, s', ⟨hlen, hst, hsum⟩, rfl, rfl⟩
        exact ⟨by omega, ⟨card_pos.1 (by omega), hsub, hst⟩, by omega⟩
      · rintro ⟨hlen, ⟨hne, hsub, hst⟩, hsum⟩
        have h1 := length_le_sum hst
        have h2 := hne.card_pos
        exact ⟨L'.card, ⟨by omega, by omega⟩, L', ⟨hsub, rfl⟩, s, ⟨by omega, hst, by omega⟩,
          rfl, rfl⟩

theorem card_stacks (h : ℕ) : ∀ (L : Finset ℤ) (m : ℕ), (stackSet L h m).card = ways L h m := by
  induction h with
  | zero => intro L m; by_cases hm : m = 0 <;> simp [stackSet, ways, hm]
  | succ h ih =>
    intro L m
    rw [stackSet, ways, card_biUnion]
    · refine sum_congr rfl fun j _ => ?_
      rw [card_biUnion]
      · refine sum_congr rfl fun L' _ => ?_
        rw [card_image_of_injective _ List.cons_injective, ih]
      · intro L₁ _ L₂ _ hne
        rw [Function.onFun, disjoint_left]
        intro s hs1 hs2
        simp only [mem_image] at hs1 hs2
        obtain ⟨s1, _, rfl⟩ := hs1
        obtain ⟨s2, _, h2⟩ := hs2
        exact hne (List.cons.inj h2).1.symm
    · intro j₁ _ j₂ _ hne
      rw [Function.onFun, disjoint_left]
      intro s hs1 hs2
      simp only [mem_biUnion, mem_image, mem_powersetCard] at hs1 hs2
      obtain ⟨L1, ⟨_, hc1⟩, s1, _, rfl⟩ := hs1
      obtain ⟨L2, ⟨_, hc2⟩, s2, _, h2⟩ := hs2
      rw [(List.cons.inj h2).1] at hc2
      exact hne (hc1.symm.trans hc2)

theorem card_base (b : ℕ) : (base b).card = b := by
  rw [base, card_image_of_injective _ (fun x y hxy => by simpa using hxy), card_range]

/-- The towers, as a finset (see `isTower_iff`). -/
def towerFinset (n k : ℕ) : Finset (List (Finset ℤ)) :=
  if k = 0 then ∅ else
    (Icc 1 n).biUnion fun b => (stackSet (base b) (k - 1) (n - b)).image (base b :: ·)

theorem card_towerFinset (n k : ℕ) : (towerFinset n k).card = Tc n k := by
  unfold towerFinset Tc
  split_ifs with hk
  · rfl
  · rw [card_biUnion]
    · refine sum_congr rfl fun b _ => ?_
      rw [card_image_of_injective _ List.cons_injective, card_stacks]
    · intro b₁ _ b₂ _ hne
      rw [Function.onFun, disjoint_left]
      intro s hs1 hs2
      simp only [mem_image] at hs1 hs2
      obtain ⟨s1, _, rfl⟩ := hs1
      obtain ⟨s2, _, h2⟩ := hs2
      have h3 := congrArg Finset.card (List.cons.inj h2).1
      rw [card_base, card_base] at h3
      exact hne h3.symm

theorem mem_supported {L : Finset ℤ} {x : ℤ} : x ∈ supported L ↔ x + 1 ∈ L ∨ x - 1 ∈ L := by
  simp only [supported, mem_union, mem_image]
  constructor
  · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · left; simpa using hy
    · right; simpa using hy
  · rintro (h | h)
    · left; exact ⟨x + 1, h, by ring⟩
    · right; exact ⟨x - 1, h, by ring⟩

theorem stack_iff (L : Finset ℤ) (s : List (Finset ℤ)) :
    Stack L s ↔ (∀ L' ∈ s, L'.Nonempty) ∧
      ∀ (i : ℕ) (hi : i < s.length), s[i] ⊆ supported ((L :: s)[i]'(by simp; omega)) := by
  induction s generalizing L with
  | nil => simp [Stack]
  | cons L' s ih =>
    rw [Stack, ih, List.forall_mem_cons]
    constructor
    · rintro ⟨hne, hsub, hall, hst⟩
      refine ⟨⟨hne, hall⟩, fun i hi => ?_⟩
      rcases i with _ | i
      · exact hsub
      · exact hst i (by simp at hi; omega)
    · rintro ⟨⟨hne, hall⟩, hst⟩
      exact ⟨hne, hst 0 (by simp), hall, fun i hi => hst (i + 1) (by simp; omega)⟩

theorem isTower_iff (n k : ℕ) (t : List (Finset ℤ)) : IsTower n k t ↔ t ∈ towerFinset n k := by
  constructor
  · rintro ⟨hlen, hne, ⟨b, hb, hhead⟩, -, hpar, hsupp, hsum⟩
    rcases t with _ | ⟨L, s⟩
    · simp at hhead
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    have hcard : (base b).card ≤ n := by
      rw [← hsum]; simp
    rw [card_base] at hcard
    have hk : k ≠ 0 := by rw [← hlen]; simp
    simp only [towerFinset, if_neg hk, mem_biUnion, mem_Icc, mem_image]
    refine ⟨b, ⟨hb, hcard⟩, s, ?_, rfl⟩
    rw [mem_stacks]
    refine ⟨by simp at hlen; omega, ?_, by simp [card_base] at hsum; omega⟩
    rw [stack_iff]
    refine ⟨fun L' h => hne L' (by simp [h]), fun i hi x hx => ?_⟩
    have hi' : i + 1 < (base b :: s).length := by simp; omega
    obtain ⟨y, hy, hxy⟩ := hsupp i hi' x hx
    obtain ⟨r, hr⟩ := hpar (i + 1) hi' x hx
    obtain ⟨r', hr'⟩ := hpar i (by omega) y hy
    push_cast at hr hr'
    rw [mem_supported]
    rcases abs_cases (x - y) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] at hxy
    · have : x = y + 1 := by omega
      right; rw [this]; simpa using hy
    · have : x = y - 1 := by omega
      left; rw [this]; simpa using hy
  · intro ht
    have hk : k ≠ 0 := by rintro rfl; simp [towerFinset] at ht
    simp only [towerFinset, if_neg hk, mem_biUnion, mem_Icc, mem_image] at ht
    obtain ⟨b, ⟨hb, hbn⟩, s, hs, rfl⟩ := ht
    rw [mem_stacks, stack_iff] at hs
    obtain ⟨hlen, ⟨hne, hst⟩, hsum⟩ := hs
    -- each layer above the base is supported by the layer below
    have hst' : ∀ (i : ℕ) (hi : i + 1 < (base b :: s).length),
        (base b :: s)[i + 1] ⊆ supported (base b :: s)[i] :=
      fun i hi => hst i (by simp at hi; omega)
    -- parity of every layer
    have hpar : ∀ (i : ℕ) (hi : i < (base b :: s).length), ∀ x ∈ (base b :: s)[i],
        Even (x - i) := by
      intro i
      induction i with
      | zero =>
        intro hi x hx
        simp only [List.getElem_cons_zero, base, mem_image, mem_range] at hx
        obtain ⟨j, -, rfl⟩ := hx
        exact ⟨j, by push_cast; ring⟩
      | succ i ih =>
        intro hi x hx
        have := hst' i hi hx
        rw [mem_supported] at this
        rcases this with h | h
        · obtain ⟨r, hr⟩ := ih (by omega) _ h
          exact ⟨r - 1, by push_cast at hr ⊢; linarith⟩
        · obtain ⟨r, hr⟩ := ih (by omega) _ h
          exact ⟨r, by push_cast at hr ⊢; linarith⟩
    refine ⟨by simp; omega, ?_, ⟨b, hb, rfl⟩, ?_, hpar, ?_, ?_⟩
    · intro L hL
      rcases List.mem_cons.1 hL with rfl | h
      · exact ⟨0, mem_image.2 ⟨0, mem_range.2 hb, by simp⟩⟩
      · exact hne L h
    · intro L hL x hx y hy hxy
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hL
      obtain ⟨r, hr⟩ := hpar i hi x hx
      obtain ⟨r', hr'⟩ := hpar i hi y hy
      rcases abs_cases (x - y) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] <;> omega
    · intro i hi x hx
      have := hst' i hi hx
      rw [mem_supported] at this
      rcases this with h | h
      · exact ⟨x + 1, h, by simp⟩
      · exact ⟨x - 1, h, by simp⟩
    · simp [card_base]; omega

/-- `T n k = Tc n k`; in particular there are finitely many towers of each size. -/
theorem T_eq_Tc (n k : ℕ) : T n k = Tc n k := by
  have : {t | IsTower n k t} = (towerFinset n k : Set (List (Finset ℤ))) := by
    ext t; simp [isTower_iff]
  rw [T, this, Set.ncard_coe_finset, card_towerFinset]

theorem rowCol_spec (d : ℕ) : ∀ (n fuel k : ℕ), d ≤ fuel → 1 ≤ k → k ≤ n + d →
    rowCol fuel n ((∑ j ∈ range d, (n + j)) + k) = (n + d, k) := by
  induction d with
  | zero =>
    intro n fuel k _ _ hk
    rcases fuel with _ | fuel
    · simp [rowCol]
    · simp [rowCol, show k ≤ n by omega]
  | succ d ih =>
    intro n fuel k hd hk1 hk
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [sum_range_succ']
    have h1 : ¬ (∑ j ∈ range d, (n + (j + 1)) + (n + 0) + k ≤ n) := by omega
    rw [rowCol, if_neg h1]
    have h2 : ∑ j ∈ range d, (n + (j + 1)) + (n + 0) + k - n =
        ∑ j ∈ range d, (n + 1 + j) + k := by
      have : ∑ j ∈ range d, (n + (j + 1)) = ∑ j ∈ range d, (n + 1 + j) :=
        sum_congr rfl fun j _ => by ring
      omega
    rw [h2, ih (n + 1) fuel k (by omega) hk1 (by omega), show n + 1 + d = n + (d + 1) by omega]

/-- `a` is the triangle `T` read by rows (offset `1`). -/
theorem a_spec (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) : a (n * (n - 1) / 2 + k) = T n k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsum : (m + 1) * (m + 1 - 1) / 2 = ∑ j ∈ range m, (1 + j) := by
    rw [← sum_range_id (m + 1), sum_range_succ']
    simp [add_comm]
  have hge : m ≤ ∑ j ∈ range m, (1 + j) := by
    rw [sum_add_distrib]; simp
  rw [a, hsum, rowCol_spec m 1 _ k (by omega) hk (by omega), T_eq_Tc, add_comm 1 m]

/-! ### The sequences on the right-hand sides -/

/-- A000071 (offset 1): `a(n) = Fibonacci(n) - 1`. -/
def A000071 (n : ℕ) : ℤ := (Nat.fib n : ℤ) - 1

theorem A000071_data : (List.range 40).map (fun i => A000071 (i + 1)) =
    [0, 0, 1, 2, 4, 7, 12, 20, 33, 54, 88, 143, 232, 376, 609, 986, 1596, 2583, 4180, 6764,
      10945, 17710, 28656, 46367, 75024, 121392, 196417, 317810, 514228, 832039, 1346268, 2178308,
      3524577, 5702886, 9227464, 14930351, 24157816, 39088168, 63245985, 102334154] := by
  decide +kernel

/-- A339252 (offset 0): `a(0) = 1`, `a(1) = 4`, `a(2) = 11`, and
`a(n) = 4*a(n-1) - 4*a(n-2)` for `n ≥ 3`. -/
def A339252 : ℕ → ℤ
  | 0 => 1
  | 1 => 4
  | 2 => 11
  | n + 3 => 4 * A339252 (n + 2) - 4 * A339252 (n + 1)

theorem A339252_data : (List.range 32).map A339252 =
    [1, 4, 11, 28, 68, 160, 368, 832, 1856, 4096, 8960, 19456, 41984, 90112, 192512, 409600,
      868352, 1835008, 3866624, 8126464, 17039360, 35651584, 74448896, 155189248, 322961408,
      671088640, 1392508928, 2885681152, 5972688896, 12348030976, 25501368320,
      52613349376] := by
  decide +kernel

/-- A339254 (offset 0): `a(n) = 6*a(n - 1) - 12*a(n - 2) + 8*a(n - 3)` for `n ≥ 5`,
`a(0) = 1`, `a(1) = 7`, `a(2) = 24`, `a(3) = 70`, `a(4) = 193`. -/
def A339254 : ℕ → ℤ
  | 0 => 1
  | 1 => 7
  | 2 => 24
  | 3 => 70
  | 4 => 193
  | n + 5 => 6 * A339254 (n + 4) - 12 * A339254 (n + 3) + 8 * A339254 (n + 2)

theorem A339254_data : (List.range 30).map A339254 =
    [1, 7, 24, 70, 193, 510, 1304, 3248, 7920, 18976, 44800, 104448, 240896, 550400, 1247232,
      2805760, 6270976, 13934592, 30801920, 67764224, 148439040, 323878912, 704118784,
      1525678080, 3295674368, 7098859520, 15250489344, 32682016768, 69877104640,
      149082341376] := by
  decide +kernel

open PowerSeries in
/-- A339029 (offset 0): expansion of
`(1 + 4*x - 20*x^2 + 8*x^3 + 33*x^4 - 4*x^5 - 33*x^6)/(1 - 2*x)^4`, i.e. the coefficients of the
power series `P * ((1 - 2X)^4)⁻¹` in `ℤ⟦X⟧` (`(1 - 2X)^4` has constant coefficient `1`). -/
noncomputable def A339029 (n : ℕ) : ℤ :=
  coeff n ((1 + 4 * X - 20 * X ^ 2 + 8 * X ^ 3 + 33 * X ^ 4 - 4 * X ^ 5 - 33 * X ^ 6 : ℤ⟦X⟧) *
    invOfUnit ((1 - 2 * X) ^ 4) 1)

/-- A computable version of `A339029` (see `A339029_eq`), by the recurrence read off from the
generating function. -/
def A339029rec : ℕ → ℤ
  | 0 => 1
  | 1 => 12
  | 2 => 52
  | 3 => 168
  | 4 => 497
  | 5 => 1412
  | 6 => 3879
  | n + 7 => 8 * A339029rec (n + 6) - 24 * A339029rec (n + 5) + 32 * A339029rec (n + 4) -
      16 * A339029rec (n + 3)

open PowerSeries in
theorem A339029rec_gf : ((1 - 2 * X) ^ 4 : ℤ⟦X⟧) * PowerSeries.mk A339029rec =
    1 + 4 * X - 20 * X ^ 2 + 8 * X ^ 3 + 33 * X ^ 4 - 4 * X ^ 5 - 33 * X ^ 6 := by
  have e1 : ((1 - 2 * X) ^ 4 : ℤ⟦X⟧) * PowerSeries.mk A339029rec = PowerSeries.mk A339029rec
      - C 8 * (X ^ 1 * PowerSeries.mk A339029rec) + C 24 * (X ^ 2 * PowerSeries.mk A339029rec)
      - C 32 * (X ^ 3 * PowerSeries.mk A339029rec)
      + C 16 * (X ^ 4 * PowerSeries.mk A339029rec) := by
    simp only [map_ofNat]; ring
  have e2 : (1 + 4 * X - 20 * X ^ 2 + 8 * X ^ 3 + 33 * X ^ 4 - 4 * X ^ 5 - 33 * X ^ 6 : ℤ⟦X⟧) =
      1 + C 4 * X ^ 1 - C 20 * X ^ 2 + C 8 * X ^ 3 + C 33 * X ^ 4 - C 4 * X ^ 5 - C 33 * X ^ 6 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_one, coeff_X_pow]
  rcases n with _ | _ | _ | _ | _ | _ | _ | n
  · simp [A339029rec]
  · simp [A339029rec]
  · simp [A339029rec]
  · simp [A339029rec]
  · simp [A339029rec]
  · simp [A339029rec]
  · simp [A339029rec]
  · have h1 : 1 ≤ n + 7 := by omega
    have h2 : 2 ≤ n + 7 := by omega
    have h3 : 3 ≤ n + 7 := by omega
    have h4 : 4 ≤ n + 7 := by omega
    simp only [h1, h2, h3, h4, if_true, A339029rec]
    simp
    ring

open PowerSeries in
theorem A339029_eq (n : ℕ) : A339029 n = A339029rec n := by
  have hu : constantCoeff ((1 - 2 * X) ^ 4 : ℤ⟦X⟧) = ((1 : ℤˣ) : ℤ) := by
    simp
  have h : PowerSeries.mk A339029rec =
      (1 + 4 * X - 20 * X ^ 2 + 8 * X ^ 3 + 33 * X ^ 4 - 4 * X ^ 5 - 33 * X ^ 6 : ℤ⟦X⟧) *
        invOfUnit ((1 - 2 * X) ^ 4) 1 := by
    rw [← A339029rec_gf, mul_comm ((1 - 2 * X) ^ 4 : ℤ⟦X⟧), mul_assoc, mul_invOfUnit _ _ hu,
      mul_one]
  rw [A339029, ← h, coeff_mk]

theorem A339029_data : (List.range 29).map A339029 =
    [1, 12, 52, 168, 497, 1412, 3879, 10360, 27016, 69024, 173264, 428288, 1044480, 2516992,
      6001408, 14174208, 33191936, 77127680, 177967104, 408027136, 930021376, 2108424192,
      4756275200, 10680270848, 23880794112, 53185871872, 118016180224, 260969594880,
      575223627776] := by
  rw [show A339029 = A339029rec from funext A339029_eq]
  decide +kernel

/-! ### The conjectures -/

/-- Consistency check of the offsets (not a proof): the four identities below hold on the rows
`n ≤ 10` listed in OEIS. Kernel-checked. -/
theorem statement_check :
    (∀ n < 11, 1 < n → (T n 2 : ℤ) = A000071 (n + 2)) ∧
    (∀ n < 11, 2 ≤ n → (T n (n - 1) : ℤ) = A339252 (n - 2)) ∧
    (∀ n < 11, 3 ≤ n → (T n (n - 2) : ℤ) = A339254 (n - 3)) ∧
    (∀ n < 11, 4 ≤ n → (T n (n - 3) : ℤ) = A339029 (n - 4)) := by
  simp only [T_eq_Tc, A339029_eq]
  decide +kernel

/-- Kagey (Mar 31 2020): for `n > 1`, `T(n,2) = A000071(n+2)`. -/
def statement_col2 : Prop :=
  ∀ n : ℕ, 1 < n → (T n 2 : ℤ) = A000071 (n + 2)

/-- Kagey (Nov 21 2020): `T(n,n-1) = A339252(n-2)`, for every `n ≥ 2`. -/
def statement_diag1 : Prop :=
  ∀ n : ℕ, 2 ≤ n → (T n (n - 1) : ℤ) = A339252 (n - 2)

/-- Luschny (Nov 29 2020): `T(n,n-2) = A339254(n-3)`, for every `n ≥ 3`. -/
def statement_diag2 : Prop :=
  ∀ n : ℕ, 3 ≤ n → (T n (n - 2) : ℤ) = A339254 (n - 3)

/-- Luschny (Dec 01 2020): `T(n,n-3) = A339029(n-4)`, for every `n ≥ 4`. -/
def statement_diag3 : Prop :=
  ∀ n : ℕ, 4 ≤ n → (T n (n - 3) : ℤ) = A339029 (n - 4)

/-- The four conjectures of A333650: the number of domino towers with `n` bricks and height `2`
is `A000071(n+2)` (`n > 1`), and those of height `n - 1`, `n - 2`, `n - 3` are counted by
`A339252(n-2)`, `A339254(n-3)`, `A339029(n-4)`. -/
def statement : Prop :=
  statement_col2 ∧ statement_diag1 ∧ statement_diag2 ∧ statement_diag3

end Math0.Statements.A333650
