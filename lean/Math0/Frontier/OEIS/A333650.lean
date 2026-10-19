/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A333650
import Math0.Audit

/-!
# Domino towers of height 2 and of height `n - 1`, `n - 2`, `n - 3` (A333650)

We prove all four conjectures of A333650: `T(n,2) = A000071(n+2)` for `n > 1`, and
`T(n,n-1) = A339252(n-2)`, `T(n,n-2) = A339254(n-3)`, `T(n,n-3) = A339029(n-4)`.

*Height 2.* A tower of height 2 with base `b` has a top layer that is any `n - b ≥ 1` element
subset of the `b + 1` positions `-1, 1, …, 2b - 1` supported by the base, so
`T(n,2) = ∑_{b=1}^{n-1} C(b+1, n-b)`, which is `F(n+2) - 1` by `F(N+1) = ∑_k C(N-k, k)`.

*Near-diagonals.* `ways L h m` (the number of stacks of `h` layers with `m` bricks on a layer
`L`) is invariant under translating `L`. A tower with `n` bricks and height `n - e` has
"excess" `e` (bricks beyond one per layer). Writing `V(S, e, h) = ways S h (h + e)` and
normalising each layer by translation (`nrm`), the recursion of `ways` closes up on just
thirteen states `(S, e)` with `e ≤ 3` (the bases `{0}`, `{0,2}`, `{0,2,4}`, `{0,2,4,6}` and the
gapped pairs `{0,4}`, `{0,6}`). For each state `128 · V(S, e, h) = 2^h · p_{S,e}(h)` for an
explicit integer cubic `p_{S,e}` once `h ≥ 3`: the base case `h = 3` and the fact that the
recursion maps the tuple of polynomials `p` to `2 p(h + 1)` are finite checks done by
`decide +kernel`, and the general statement follows by induction on `h`. Summing over the base
size gives `128 · T(n, n-e) = 2^h · P_e(h)` with `h = n - e - 1` and
`P_1 = 160 + 96h`, `P_2 = 280 + 172h + 36h^2`, `P_3 = 588 + 367h + 84h^2 + 9h^3`, and the same
closed forms are obtained for A339252, A339254, A339029 from their linear recurrences. The
rows `n ≤ 10` come from `statement_check`.
-/

namespace Math0.Frontier.A333650
open Math0.Statements.A333650 Finset

/-- Translating a layer translates the positions it supports. -/
private theorem supported_map (L : Finset ℤ) (c : ℤ) :
    supported (L.map (addRightEmbedding c)) = (supported L).map (addRightEmbedding c) := by
  ext x
  simp only [mem_supported, mem_map, addRightEmbedding_apply]
  constructor
  · rintro (⟨a, ha, hax⟩ | ⟨a, ha, hax⟩)
    · exact ⟨x - c, Or.inl (by rw [show x - c + 1 = a by omega]; exact ha), by ring⟩
    · exact ⟨x - c, Or.inr (by rw [show x - c - 1 = a by omega]; exact ha), by ring⟩
  · rintro ⟨y, hy | hy, rfl⟩
    · exact Or.inl ⟨y + 1, hy, by ring⟩
    · exact Or.inr ⟨y - 1, hy, by ring⟩

/-- `ways` is invariant under translating the bottom layer. -/
private theorem ways_map (c : ℤ) (h : ℕ) : ∀ (L : Finset ℤ) (m : ℕ),
    ways (L.map (addRightEmbedding c)) h m = ways L h m := by
  induction h with
  | zero => intro L m; rfl
  | succ h ih =>
    intro L m
    simp only [ways]
    refine sum_congr rfl fun j _ => ?_
    rw [supported_map, powersetCard_map, sum_map]
    refine sum_congr rfl fun L' _ => ?_
    exact ih L' _

/-- Normal form of a layer up to translation: shifted so that its leftmost brick is at `0`. -/
private def nrm (L : Finset ℤ) : Finset ℤ :=
  if hL : L.Nonempty then L.map (addRightEmbedding (-L.min' hL)) else L

/-- `ways` only depends on the normal form of the bottom layer. -/
private theorem ways_nrm (L : Finset ℤ) (h m : ℕ) : ways (nrm L) h m = ways L h m := by
  unfold nrm
  split_ifs
  · exact ways_map _ _ _ _
  · rfl

/-- One step of the recursion of `ways`, written with the excess `e` and normalised layers. -/
private theorem ways_succ (L : Finset ℤ) (h e : ℕ) :
    ways L (h + 1) (h + 1 + e) = ∑ j ∈ range (e + 1),
      ∑ L' ∈ (supported L).powersetCard (j + 1), ways (nrm L') h (h + (e - j)) := by
  rw [ways, show h + 1 + e - h = e + 1 by omega]
  have hI : Icc 1 (e + 1) = (range (e + 1)).map (addRightEmbedding 1) := by
    ext x; simp only [mem_Icc, mem_map, mem_range, addRightEmbedding_apply]
    constructor
    · intro hx; exact ⟨x - 1, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩; omega
  rw [hI, sum_map]
  refine sum_congr rfl fun j hj => sum_congr rfl fun L' _ => ?_
  rw [mem_range] at hj
  rw [ways_nrm, addRightEmbedding_apply, show h + 1 + e - (j + 1) = h + (e - j) by omega]

/-- Fewer bricks than layers: no stacks. -/
private theorem ways_eq_zero (L : Finset ℤ) (h m : ℕ) (hm : m < h) : ways L h m = 0 := by
  obtain ⟨h, rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  rw [ways, show m - h = 0 by omega]
  simp

/-- The thirteen states `(layer shape, remaining excess)`, with the coefficients (scaled by
`128`) of the polynomial `p` such that the number of stacks is `2^h * p(h) / 128`. -/
private def tab : List ((Finset ℤ × ℕ) × List ℤ) :=
  [(({0}, 0), [128, 0, 0, 0]),
   (({0}, 1), [-32, 96, 0, 0]),
   (({0, 2}, 0), [192, 0, 0, 0]),
   (({0}, 2), [-104, 28, 36, 0]),
   (({0, 2}, 1), [128, 144, 0, 0]),
   (({0, 2, 4}, 0), [256, 0, 0, 0]),
   (({0}, 3), [-228, 1, 30, 9]),
   (({0, 2}, 2), [80, 174, 54, 0]),
   (({0, 2, 4}, 1), [416, 192, 0, 0]),
   (({0, 2, 4, 6}, 0), [320, 0, 0, 0]),
   (({0, 4}, 0), [256, 0, 0, 0]),
   (({0, 4}, 1), [416, 192, 0, 0]),
   (({0, 6}, 0), [256, 0, 0, 0])]

/-- The states of `tab`. -/
private def states : List (Finset ℤ × ℕ) := tab.map Prod.fst

/-- The (scaled) coefficient of `h^d` in the polynomial of a state, `0` if absent. -/
private def coef (s : Finset ℤ × ℕ) (d : ℕ) : ℤ := ((tab.lookup s).getD []).getD d 0

/-- Evaluation of the cubic with coefficients `c 0, …, c 3`. -/
private def pe (c : ℕ → ℤ) (x : ℤ) : ℤ := c 0 + c 1 * x + c 2 * x ^ 2 + c 3 * x ^ 3

/-- Coefficients of `2 · p(x + 1)` from those of `p`. -/
private def nx (c : ℕ → ℤ) : ℕ → ℤ
  | 0 => 2 * (c 0 + c 1 + c 2 + c 3)
  | 1 => 2 * (c 1 + 2 * c 2 + 3 * c 3)
  | 2 => 2 * (c 2 + 3 * c 3)
  | _ => 2 * c 3

/-- The recursion from a state only reaches states (kernel check). -/
private theorem closure_check : ∀ s ∈ states, ∀ j ∈ range (s.2 + 1),
    ∀ L' ∈ (supported s.1).powersetCard (j + 1), (nrm L', s.2 - j) ∈ states := by
  decide +kernel

/-- The recursion maps the polynomial of each state to `2 p(h + 1)` (kernel check). -/
private theorem coef_check : ∀ s ∈ states, ∀ d ∈ range 4,
    ∑ j ∈ range (s.2 + 1), ∑ L' ∈ (supported s.1).powersetCard (j + 1),
      coef (nrm L', s.2 - j) d = nx (coef s) d := by
  decide +kernel

/-- The closed forms at `h = 3` (kernel check). -/
private theorem base_check : ∀ s ∈ states,
    128 * (ways s.1 3 (3 + s.2) : ℤ) = 2 ^ 3 * pe (coef s) 3 := by
  decide +kernel

/-- `pe` is linear in the coefficients. -/
private theorem pe_sum {ι : Type*} (I : Finset ι) (c : ι → ℕ → ℤ) (x : ℤ) :
    ∑ i ∈ I, pe (c i) x = pe (fun d => ∑ i ∈ I, c i d) x := by
  simp only [pe, sum_add_distrib, sum_mul]

/-- `pe` only depends on the first four coefficients. -/
private theorem pe_congr {c c' : ℕ → ℤ} (x : ℤ) (h : ∀ d ∈ range 4, c d = c' d) :
    pe c x = pe c' x := by
  simp only [pe, h 0 (by simp), h 1 (by simp), h 2 (by simp), h 3 (by simp)]

/-- `nx` realises `p ↦ 2 p(x + 1)`. -/
private theorem pe_nx (c : ℕ → ℤ) (x : ℤ) : pe (nx c) x = 2 * pe c (x + 1) := by
  simp only [pe, nx]; ring

/-- Closed form of every state: `128 · ways S h (h + e) = 2^h · p_{S,e}(h)` for `h ≥ 3`. -/
private theorem main (h : ℕ) (hh : 3 ≤ h) : ∀ s ∈ states,
    128 * (ways s.1 h (h + s.2) : ℤ) = 2 ^ h * pe (coef s) h := by
  induction h, hh using Nat.le_induction with
  | base => exact base_check
  | succ h hh ih =>
    intro s hs
    rw [ways_succ]
    push_cast
    rw [mul_sum]
    have step : ∀ j ∈ range (s.2 + 1), 128 * ∑ L' ∈ (supported s.1).powersetCard (j + 1),
        (ways (nrm L') h (h + (s.2 - j)) : ℤ) =
        2 ^ h * ∑ L' ∈ (supported s.1).powersetCard (j + 1), pe (coef (nrm L', s.2 - j)) h := by
      intro j hj
      rw [mul_sum, mul_sum]
      refine sum_congr rfl fun L' hL' => ?_
      exact ih (nrm L', s.2 - j) (closure_check s hs j hj L' hL')
    rw [sum_congr rfl step, ← mul_sum]
    simp only [pe_sum]
    rw [pe_congr _ (coef_check s hs), pe_nx]
    ring

/-- `T(n, n - e)` as a sum over the base size `b + 1 ≤ e + 1`. -/
private theorem Tc_diag (n e : ℕ) (hn : e + 1 ≤ n) :
    Tc n (n - e) = ∑ b ∈ range (e + 1),
      ways (base (b + 1)) (n - e - 1) (n - e - 1 + (e - b)) := by
  rw [Tc, if_neg (by omega)]
  have hsub : (range (e + 1)).map (addRightEmbedding 1) ⊆ Icc 1 n := by
    intro x hx
    simp only [mem_map, mem_range, addRightEmbedding_apply] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    simp only [mem_Icc]; omega
  rw [← sum_subset hsub, sum_map]
  · refine sum_congr rfl fun b hb => ?_
    rw [mem_range] at hb
    simp only [addRightEmbedding_apply]
    congr 1; omega
  · intro b hb hb'
    apply ways_eq_zero
    simp only [mem_map, mem_range, addRightEmbedding_apply, not_exists, not_and] at hb'
    simp only [mem_Icc] at hb
    have : e + 2 ≤ b := by
      by_contra hc
      exact hb' (b - 1) (by omega) (by omega)
    omega

/-- Coefficients of the polynomial for the diagonal `T(n, n - e)`. -/
private def R (e d : ℕ) : ℤ := ∑ b ∈ range (e + 1), coef (base (b + 1), e - b) d

/-- The bases with their remaining excess are states (kernel check). -/
private theorem base_mem :
    ∀ e ∈ range 4, ∀ b ∈ range (e + 1), (base (b + 1), e - b) ∈ states := by
  decide +kernel

/-- `128 · T(n, n - e) = 2^h · P_e(h)` with `h = n - e - 1`, for `e ≤ 3` and `n ≥ e + 4`. -/
private theorem diag (n e : ℕ) (he : e < 4) (hn : e + 4 ≤ n) :
    128 * (T n (n - e) : ℤ) = 2 ^ (n - e - 1) * pe (R e) (n - e - 1 : ℕ) := by
  rw [T_eq_Tc, Tc_diag n e (by omega)]
  push_cast
  rw [mul_sum]
  have key : ∀ b ∈ range (e + 1),
      128 * (ways (base (b + 1)) (n - e - 1) (n - e - 1 + (e - b)) : ℤ) =
      2 ^ (n - e - 1) * pe (coef (base (b + 1), e - b)) (n - e - 1 : ℕ) := by
    intro b hb
    exact main (n - e - 1) (by omega) _ (base_mem e (by simpa using he) b hb)
  rw [sum_congr rfl key, ← mul_sum, pe_sum]
  rfl

/-- The coefficients of `P_1`. -/
private theorem R1 : R 1 0 = 160 ∧ R 1 1 = 96 ∧ R 1 2 = 0 ∧ R 1 3 = 0 := by decide +kernel
/-- The coefficients of `P_2`. -/
private theorem R2 : R 2 0 = 280 ∧ R 2 1 = 172 ∧ R 2 2 = 36 ∧ R 2 3 = 0 := by decide +kernel
/-- The coefficients of `P_3`. -/
private theorem R3 : R 3 0 = 588 ∧ R 3 1 = 367 ∧ R 3 2 = 84 ∧ R 3 3 = 9 := by decide +kernel

/-- `128 · A339252(h) = 2^h (160 + 96 h)` for `h ≥ 1`. -/
private theorem A339252_closed (k : ℕ) :
    128 * A339252 (k + 1) = 2 ^ (k + 1) * (160 + 96 * ((k + 1 : ℕ) : ℤ)) ∧
    128 * A339252 (k + 2) = 2 ^ (k + 2) * (160 + 96 * ((k + 2 : ℕ) : ℤ)) := by
  induction k with
  | zero => norm_num [A339252]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    rw [show k + 1 + 2 = k + 3 from rfl, A339252]
    push_cast at h1 h2 ⊢
    linear_combination 4 * h2 - 4 * h1

/-- `128 · A339254(h) = 2^h (280 + 172 h + 36 h^2)` for `h ≥ 2`. -/
private theorem A339254_closed (k : ℕ) :
    128 * A339254 (k + 2) = 2 ^ (k + 2) * (280 + 172 * ((k + 2 : ℕ) : ℤ) +
      36 * ((k + 2 : ℕ) : ℤ) ^ 2) ∧
    128 * A339254 (k + 3) = 2 ^ (k + 3) * (280 + 172 * ((k + 3 : ℕ) : ℤ) +
      36 * ((k + 3 : ℕ) : ℤ) ^ 2) ∧
    128 * A339254 (k + 4) = 2 ^ (k + 4) * (280 + 172 * ((k + 4 : ℕ) : ℤ) +
      36 * ((k + 4 : ℕ) : ℤ) ^ 2) := by
  induction k with
  | zero => norm_num [A339254]
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨h2, h3, ?_⟩
    rw [show k + 1 + 4 = k + 5 from rfl, A339254]
    push_cast at h1 h2 h3 ⊢
    linear_combination 6 * h3 - 12 * h2 + 8 * h1

/-- `128 · A339029(h) = 2^h (588 + 367 h + 84 h^2 + 9 h^3)` for `h ≥ 3`. -/
private theorem A339029_closed (k : ℕ) :
    128 * A339029rec (k + 3) = 2 ^ (k + 3) * (588 + 367 * ((k + 3 : ℕ) : ℤ) +
      84 * ((k + 3 : ℕ) : ℤ) ^ 2 + 9 * ((k + 3 : ℕ) : ℤ) ^ 3) ∧
    128 * A339029rec (k + 4) = 2 ^ (k + 4) * (588 + 367 * ((k + 4 : ℕ) : ℤ) +
      84 * ((k + 4 : ℕ) : ℤ) ^ 2 + 9 * ((k + 4 : ℕ) : ℤ) ^ 3) ∧
    128 * A339029rec (k + 5) = 2 ^ (k + 5) * (588 + 367 * ((k + 5 : ℕ) : ℤ) +
      84 * ((k + 5 : ℕ) : ℤ) ^ 2 + 9 * ((k + 5 : ℕ) : ℤ) ^ 3) ∧
    128 * A339029rec (k + 6) = 2 ^ (k + 6) * (588 + 367 * ((k + 6 : ℕ) : ℤ) +
      84 * ((k + 6 : ℕ) : ℤ) ^ 2 + 9 * ((k + 6 : ℕ) : ℤ) ^ 3) := by
  induction k with
  | zero => norm_num [A339029rec]
  | succ k ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    refine ⟨h2, h3, h4, ?_⟩
    rw [show k + 1 + 6 = k + 7 from rfl, A339029rec]
    push_cast at h1 h2 h3 h4 ⊢
    linear_combination 8 * h4 - 24 * h3 + 32 * h2 - 16 * h1

/-- One layer of `m ≥ 1` bricks on `L`: any `m`-subset of the supported positions. -/
private theorem ways_one (L : Finset ℤ) (m : ℕ) (hm : 1 ≤ m) :
    ways L 1 m = (supported L).card.choose m := by
  simp only [ways, Nat.sub_zero]
  rw [sum_eq_single m]
  · simp [card_powersetCard]
  · intro j hj hjm
    simp only [mem_Icc] at hj
    refine sum_eq_zero fun L' _ => ?_
    rw [if_neg (by omega)]
  · intro hm'
    simp only [mem_Icc] at hm'
    omega

/-- A base of `b` bricks supports `b + 1` positions. -/
private theorem card_supported_base (b : ℕ) (hb : 1 ≤ b) :
    (supported (base b)).card = b + 1 := by
  have : supported (base b) = (range (b + 1)).image fun i : ℕ => 2 * (i : ℤ) - 1 := by
    ext x
    simp only [mem_supported, base, mem_image, mem_range]
    constructor
    · rintro (⟨j, hj, hjx⟩ | ⟨j, hj, hjx⟩)
      · exact ⟨j, by omega, by omega⟩
      · exact ⟨j + 1, by omega, by push_cast; omega⟩
    · rintro ⟨i, hi, rfl⟩
      by_cases hib : i < b
      · exact Or.inl ⟨i, hib, by ring⟩
      · exact Or.inr ⟨i - 1, by omega, by
          rw [Nat.cast_sub (by omega)]; push_cast; ring⟩
  rw [this, card_image_of_injective (f := fun i : ℕ => 2 * (i : ℤ) - 1) _
    (fun i j hij => by simp only at hij; omega), card_range]

/-- Kagey: `T(n,2) = F(n+2) - 1` for `n > 1`. -/
private theorem col2 : statement_col2 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hT : T (m + 2) 2 = ∑ b ∈ range (m + 1), (b + 2).choose (m + 1 - b) := by
    rw [T_eq_Tc, Tc, if_neg (by norm_num)]
    have hI : Icc 1 (m + 2) = (range (m + 2)).map (addRightEmbedding 1) := by
      ext x; simp only [mem_Icc, mem_map, mem_range, addRightEmbedding_apply]
      constructor
      · intro hx; exact ⟨x - 1, by omega, by omega⟩
      · rintro ⟨a, ha, rfl⟩; omega
    rw [hI, sum_map, sum_range_succ]
    simp only [addRightEmbedding_apply]
    rw [ways_eq_zero _ _ _ (by omega), add_zero]
    refine sum_congr rfl fun b hb => ?_
    rw [mem_range] at hb
    rw [show 2 - 1 = 1 from rfl, show m + 2 - (b + 1) = m + 1 - b by omega,
      ways_one _ _ (by omega), card_supported_base _ (by omega)]
  have hF : Nat.fib (m + 2 + 2) = (∑ b ∈ range (m + 1), (b + 2).choose (m + 1 - b)) + 1 := by
    rw [show m + 2 + 2 = (m + 3) + 1 by ring, Nat.fib_succ_eq_sum_choose,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => i.choose j),
      Nat.succ_eq_add_one, sum_range_succ', sum_range_succ', sum_range_succ]
    have h1 : (0 + 1).choose (m + 3 - (0 + 1)) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h2 : (m + 1 + 1 + 1).choose (m + 3 - (m + 1 + 1 + 1)) = 1 := by
      rw [show m + 3 - (m + 1 + 1 + 1) = 0 by omega, Nat.choose_zero_right]
    have h0 : Nat.choose 0 (m + 3 - 0) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h1, h2, h0]
    have h3 : ∀ k ∈ range (m + 1), (k + 1 + 1).choose (m + 3 - (k + 1 + 1)) =
        (k + 2).choose (m + 1 - k) := fun k _ => by
      rw [show m + 3 - (k + 1 + 1) = m + 1 - k by omega]
    rw [sum_congr rfl h3]
  rw [A000071, hT, hF]
  push_cast
  ring

/-- Kagey: `T(n,n-1) = A339252(n-2)`. -/
private theorem diag1 : statement_diag1 := by
  intro n hn
  by_cases hsmall : n < 11
  · exact statement_check.2.1 n hsmall hn
  have h1 := diag n 1 (by norm_num) (by omega)
  obtain ⟨r0, r1, r2, r3⟩ := R1
  have h2 := (A339252_closed (n - 3)).1
  rw [show n - 3 + 1 = n - 1 - 1 by omega] at h2
  rw [show n - 2 = n - 1 - 1 by omega]
  simp only [pe, r0, r1, r2, r3] at h1
  have : 128 * (T n (n - 1) : ℤ) = 128 * A339252 (n - 1 - 1) := by linear_combination h1 - h2
  linarith

/-- Luschny: `T(n,n-2) = A339254(n-3)`. -/
private theorem diag2 : statement_diag2 := by
  intro n hn
  by_cases hsmall : n < 11
  · exact statement_check.2.2.1 n hsmall hn
  have h1 := diag n 2 (by norm_num) (by omega)
  obtain ⟨r0, r1, r2, r3⟩ := R2
  have h2 := (A339254_closed (n - 5)).1
  rw [show n - 5 + 2 = n - 2 - 1 by omega] at h2
  rw [show n - 3 = n - 2 - 1 by omega]
  simp only [pe, r0, r1, r2, r3] at h1
  have : 128 * (T n (n - 2) : ℤ) = 128 * A339254 (n - 2 - 1) := by linear_combination h1 - h2
  linarith

/-- Luschny: `T(n,n-3) = A339029(n-4)`. -/
private theorem diag3 : statement_diag3 := by
  intro n hn
  by_cases hsmall : n < 11
  · exact statement_check.2.2.2 n hsmall hn
  have h1 := diag n 3 (by norm_num) (by omega)
  obtain ⟨r0, r1, r2, r3⟩ := R3
  have h2 := (A339029_closed (n - 7)).1
  rw [show n - 7 + 3 = n - 3 - 1 by omega] at h2
  rw [show n - 4 = n - 3 - 1 by omega, A339029_eq]
  simp only [pe, r0, r1, r2, r3] at h1
  have : 128 * (T n (n - 3) : ℤ) = 128 * A339029rec (n - 3 - 1) := by linear_combination h1 - h2
  linarith

/-- The four conjectures of A333650 hold. -/
theorem result : statement := ⟨col2, diag1, diag2, diag3⟩

end Math0.Frontier.A333650

#math0_settles Math0.Frontier.A333650.result Math0.Statements.A333650.statement
