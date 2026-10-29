/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A355360: columns 1 and 2 of the theta-series triangle

Source: https://oeis.org/A355360, _Paul D. Hanna_, Jul 19 2022 (COMMENTS section of the entry,
by its author). Verbatim:
> Conjectures.
> (C.1) Column 1 equals A000716, the number of partitions into parts of 3 kinds.
> (C.2) Column 2 equals twice A023005, the number of partitions into parts of 6 kinds.

The entry's name: "G.f. A(x,y) satisfies: x*y*A(x,y) = Sum_{n=-oo..+oo} (-1)^n *
x^(n*(n+1)/2) * A(x,y)^n, with coefficients T(n,k) of x^n*y^k in A(x,y) given as a triangle
read by rows." Keyword `tabl`, offset `0`: rows `n ≥ 0`, columns `0 ≤ k ≤ n`; the DATA section
lists rows `0` to `10` (66 terms).

## Encoding

* *The g.f.* `A(x,y) = ∑_{m ≥ 0} a_m(y) x^m` is a power series in `x` whose coefficients
  `a_m(y) = ∑_k T(m,k) y^k` are polynomials in `y` with integer coefficients. Write
  `F(B) = ∑_{n ∈ ℤ} (-1)^n x^{n(n+1)/2} B^n`; the defining equation is `x y A = F(A)`.
  Negative powers require `A` to be invertible, i.e. `a_0` invertible.
* *The solution is unique and is computed order by order* (this is what `coeffs` does):
  - order `x^0`: only `n = 0` and `n = -1` have `n(n+1)/2 = 0`, so `0 = 1 - a_0⁻¹`, i.e.
    `a_0 = 1`;
  - order `x^m`, `m ≥ 1`: the left side gives `y a_{m-1}`. On the right side every term with
    `n ≠ -1` has `n(n+1)/2 ≥ 1` or is the constant `1`, so its `x^m`-coefficient involves only
    `a_0, …, a_{m-1}`; and `-A⁻¹ = -A_{<m}⁻¹ + a_m x^m + O(x^{m+1})`, where
    `A_{<m} = a_0 + ⋯ + a_{m-1} x^{m-1}`. Hence `[x^m] F(A) = a_m + [x^m] F(A_{<m})` and the
    equation at order `x^m` is equivalent to
    `a_m = y a_{m-1} - [x^m] F(A_{<m})`.
  This recursion is also exactly the PARI program of the entry, which sets the new coefficient
  `a_m` to the `x^m`-coefficient of `x y A - F(A)` computed with `a_m = 0`.
* *Implementation.* A polynomial in `y` is its list of integer coefficients (`Poly`), a power
  series in `x` truncated mod `x^L` is the list of its first `L` coefficients (`Ser`).
  `[x^m] F(B)` (`thetaCoeff B m`) is computed mod `x^{m+1}`, the sum over `n ∈ ℤ` being grouped
  into the pairs `{n, -1-n}`, `n ≥ 0`, which carry the same power `x^{n(n+1)/2}` and opposite
  signs: `F(B) = ∑_{n ≥ 0} (-1)^n x^{n(n+1)/2} (B^n - B^{-(n+1)})`. Only the `n` with
  `n(n+1)/2 ≤ m` contribute (all of them satisfy `n ≤ m`). The inverse of a series with constant
  term `1` (`sinv`) is computed by `b_0 = 1`, `b_i = -∑_{j=1}^{i} a_j b_{i-j}`.
* `coeffs m = [a_0, …, a_m]` and `T n k` is the coefficient of `y^k` in `a_n`, i.e. of
  `x^n y^k` in `A(x,y)`; it is `ℤ`-valued (the entry's terms are nonnegative, but the recursion
  has signs). `a_data` checks, in the kernel, all 66 terms of the DATA section (rows `0` to `10`,
  read by rows), and `T_example_rows` the rows `11` and `12` displayed in the EXAMPLE section.
* *The other sequences.* A000716 (offset `0`) is "Number of partitions of n into parts of 3
  kinds" and A023005 (offset `0`) "Number of partitions of n into parts of 6 kinds". A partition
  of `n` into parts of `j` kinds is the same as a `j`-tuple of ordinary partitions (the parts of
  each kind) with total size `n`, so it is counted by
  `partitionsOfKinds j n = ∑_{n_1 + ⋯ + n_j = n} p(n_1) ⋯ p(n_j)`, where `p m` is the number of
  `Nat.Partition m` (equivalently, `[x^n] P(x)^j` with `P(x) = ∏_{m ≥ 1} 1/(1 - x^m)`, the g.f.
  in both entries). `Nat.Partition` is not kernel-friendly, so for the sanity checks only we
  prove `p m = pb m m` for a structurally recursive count `pb` (`p_eq_pb`), and check the first
  listed terms of both sequences (`A000716_data`, `A023005_data`).
* *The statement.* Column `k` of the triangle starts at its diagonal entry `T(k,k)` (row `k`),
  and both target sequences have offset `0`, so "column 1 equals A000716" is
  `T(n+1, 1) = A000716(n)` for every `n ≥ 0`, and "column 2 equals twice A023005" is
  `T(n+2, 2) = 2 · A023005(n)` for every `n ≥ 0` (the entry's EXAMPLE section displays the
  alignment: `P(x)^3 = 1 + 3x + 9x^2 + ⋯` against the column `1, 3, 9, …`). Equivalently, the
  coefficients of `y` and `y^2` in `A(x,y)` are `x P(x)^3` and `2 x^2 P(x)^6`.
  `statement_check` verifies both identities for the first `10` resp. `6` values of `n` (a
  consistency check of the offsets, not a proof).
-/

namespace Math0.Statements.A355360

/-! ### Truncated power series in `x` over `ℤ[y]` -/

/-- A polynomial in `y` with integer coefficients, as its coefficient list:
`[c₀, c₁, …]` is `c₀ + c₁ y + ⋯`. -/
abbrev Poly := List ℤ

/-- Sum of polynomials. -/
def padd : Poly → Poly → Poly
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: padd p q

/-- Multiplication of a polynomial by an integer. -/
def pscale (c : ℤ) (p : Poly) : Poly := p.map (c * ·)

/-- Product of polynomials. -/
def pmul : Poly → Poly → Poly
  | [], _ => []
  | a :: p, q => padd (pscale a q) (0 :: pmul p q)

/-- A power series in `x` with coefficients in `ℤ[y]`, truncated: `[b₀, b₁, …]` is
`b₀ + b₁ x + ⋯` (missing coefficients are `0`). -/
abbrev Ser := List Poly

/-- The coefficient of `x^i` in `A * B`. -/
def mulCoeff (A B : Ser) (i : ℕ) : Poly :=
  (List.range (i + 1)).foldl (fun s j => padd s (pmul (A.getD j []) (B.getD (i - j) []))) []

/-- `A * B mod x^L`. -/
def smul (L : ℕ) (A B : Ser) : Ser := (List.range L).map (mulCoeff A B)

/-- `A⁻¹ mod x^L`, for a series `A` with constant term `1`:
`b₀ = 1`, `b_i = -∑_{j=1}^{i} a_j b_{i-j}`. -/
def sinv (L : ℕ) (A : Ser) : Ser :=
  (List.range L).foldl (fun B i => B ++ [if i = 0 then [1] else
    pscale (-1) ((List.range i).foldl
      (fun s j => padd s (pmul (A.getD (j + 1) []) (B.getD (i - 1 - j) []))) [])]) []

/-- `[x^m] ∑_{n ∈ ℤ} (-1)^n x^{n(n+1)/2} B^n`, for a series `B` with constant term `1`, computed
mod `x^{m+1}` as `∑_{n ≥ 0, n(n+1)/2 ≤ m} (-1)^n [x^{m - n(n+1)/2}] (B^n - B^{-(n+1)})`
(the terms `n` and `-1-n` grouped together). The state of the loop is
`(partial sum, B^n, B^{-(n+1)})`. -/
def thetaCoeff (B : Ser) (m : ℕ) : Poly :=
  let L := m + 1
  let Binv := sinv L B
  ((List.range L).foldl (fun (st : Poly × Ser × Ser) n =>
    let t := n * (n + 1) / 2
    if t ≤ m then
      (padd st.1 (pscale ((-1) ^ n)
          (padd (st.2.1.getD (m - t) []) (pscale (-1) (st.2.2.getD (m - t) [])))),
        smul L st.2.1 B, smul L st.2.2 Binv)
    else st) ([], [[1]], Binv)).1

/-- `coeffs m = [a₀, …, a_m]`, the first coefficients (in `x`) of the unique solution `A(x,y)` of
`x y A = ∑_{n ∈ ℤ} (-1)^n x^{n(n+1)/2} A^n`: `a₀ = 1` and
`a_{m+1} = y a_m - [x^{m+1}] F(a₀ + ⋯ + a_m x^m)`. -/
def coeffs : ℕ → Ser
  | 0 => [[1]]
  | m + 1 =>
    let B := coeffs m
    B ++ [padd (0 :: B.getD m []) (pscale (-1) (thetaCoeff B (m + 1)))]

/-- `T(n,k)`, the coefficient of `x^n y^k` in `A(x,y)`. -/
def T (n k : ℕ) : ℤ := ((coeffs n).getD n []).getD k 0

/-- The definition reproduces all 66 terms of the DATA section (rows `0` to `10`, read by rows;
kernel-checked). -/
theorem a_data : (List.range 11).flatMap (fun n => (List.range (n + 1)).map (T n)) =
    [1, 0, 1, 0, 3, 2, 0, 9, 12, 5, 0, 22, 54, 46, 14, 0, 51, 196, 282, 175, 42, 0, 108, 630,
      1360, 1365, 666, 132, 0, 221, 1836, 5635, 8190, 6321, 2541, 429, 0, 429, 4984,
      20850, 41405, 45326, 28448, 9724, 1430, 0, 810, 12744, 70737, 184527, 270060, 237209,
      125532, 37323, 4862, 0, 1479, 31050, 223652, 745745, 1404102, 1625932, 1193116, 546039,
      143650, 16796] := by
  decide +kernel

/-- Rows `11` and `12`, as displayed in the EXAMPLE section of the entry (kernel-checked). -/
theorem T_example_rows : (List.range 2).map (fun i => (List.range (i + 12)).map (T (i + 11))) =
    [[0, 2640, 72560, 667005, 2784110, 6565030, 9646462, 9242178, 5826171, 2349490, 554268,
        58786],
      [0, 4599, 163632, 1892670, 9729720, 28161819, 51126740, 61555824, 50308245, 27806065,
        10023948, 2143428, 208012]] := by
  decide +kernel

/-! ### Partitions into parts of several kinds -/

/-- The partition number A000041(m): the number of partitions of `m`. -/
def p (m : ℕ) : ℕ := Fintype.card (Nat.Partition m)

/-- The number of partitions of `n` into parts of `j` kinds: `j`-tuples of partitions (the parts
of each kind) of total size `n`, i.e. `∑_{n_1 + ⋯ + n_j = n} p(n_1) ⋯ p(n_j)`. -/
def partitionsOfKinds (j n : ℕ) : ℕ :=
  ∑ f ∈ Finset.Nat.antidiagonalTuple j n, ∏ i, p (f i)

/-- A000716(n): the number of partitions of `n` into parts of 3 kinds. -/
def A000716 (n : ℕ) : ℕ := partitionsOfKinds 3 n

/-- A023005(n): the number of partitions of `n` into parts of 6 kinds. -/
def A023005 (n : ℕ) : ℕ := partitionsOfKinds 6 n

/-! ### The conjecture -/

/-- Hanna's conjectures (C.1) and (C.2): column 1 of the triangle is A000716,
`T(n+1, 1) = A000716(n)` for all `n ≥ 0`, and column 2 is twice A023005,
`T(n+2, 2) = 2 · A023005(n)` for all `n ≥ 0`. -/
def statement : Prop :=
  (∀ n : ℕ, T (n + 1) 1 = A000716 n) ∧ (∀ n : ℕ, T (n + 2) 2 = 2 * A023005 n)

/-! ### Sanity checks of the transcription (not a proof) -/

/-- The number of partitions of `n` all of whose parts are `≤ m`. -/
def B (n m : ℕ) : ℕ :=
  (Finset.univ.filter (fun π : n.Partition => ∀ i ∈ π.parts, i ≤ m)).card

/-- A computable count of the partitions of `n` into parts `≤ m` (`j` is the number of parts
equal to `m + 1`); `pb_eq_B` shows `pb n m = B n m`. -/
def pb : ℕ → ℕ → ℕ
  | n, 0 => if n = 0 then 1 else 0
  | n, m + 1 => ∑ j ∈ Finset.range (n / (m + 1) + 1), pb (n - j * (m + 1)) m

theorem part_le {n : ℕ} (π : n.Partition) {i : ℕ} (hi : i ∈ π.parts) : i ≤ n :=
  (Multiset.le_sum_of_mem hi).trans_eq π.parts_sum

theorem B_zero (m : ℕ) : B 0 m = 1 := by
  rw [B, Finset.filter_true_of_mem (by simp), Finset.card_univ, Fintype.card_unique]

theorem B_succ_zero (n : ℕ) : B (n + 1) 0 = 0 := by
  rw [B, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro π _ h
  have h0 : π.parts = 0 := Multiset.eq_zero_of_forall_notMem fun i hi => by
    have := π.parts_pos hi; have := h i hi; omega
  have := π.parts_sum
  rw [h0] at this
  simp at this

theorem B_succ (n m : ℕ) :
    B n (m + 1) = B n m + if m + 1 ≤ n then B (n - (m + 1)) (m + 1) else 0 := by
  rw [B, ← Finset.card_filter_add_card_filter_not
    (fun π : n.Partition => m + 1 ∈ π.parts), add_comm]
  congr 1
  · rw [B, Finset.filter_filter]
    congr 1
    ext π
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h, hm⟩ i hi
      have := h i hi
      have : i ≠ m + 1 := fun e => hm (e ▸ hi)
      omega
    · intro h
      exact ⟨fun i hi => (h i hi).trans (Nat.le_succ m), fun hm => by have := h _ hm; omega⟩
  · split_ifs with hmn
    · rw [B]
      let e := Nat.Partition.partitionWithPartEquiv (n := n) (a := m + 1) (by omega) hmn
      refine Finset.card_bij' (fun π hπ => e ⟨π, (Finset.mem_filter.1 hπ).2⟩)
        (fun π _ => (e.symm π).1) ?_ ?_ ?_ ?_
      · intro π hπ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
        intro i hi
        rw [Nat.Partition.partitionWithPartEquiv_apply_parts] at hi
        exact hπ.1 i (Multiset.mem_of_mem_erase hi)
      · intro π _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [Nat.Partition.partitionWithPartEquiv_symm_apply_parts]
        refine ⟨fun i hi => ?_, Multiset.mem_cons_self _ _⟩
        rcases Multiset.mem_cons.1 hi with rfl | hi
        · exact le_rfl
        · have h := Finset.mem_filter.1 ‹_›
          exact h.2 i hi
      · intro π _
        simp only [Equiv.symm_apply_apply]
      · intro π _
        simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro π _ h
      exact hmn (part_le π h)

theorem pb_zero_right (n : ℕ) : pb n 0 = if n = 0 then 1 else 0 := by
  rw [pb]

theorem pb_succ (n m : ℕ) :
    pb n (m + 1) = pb n m + if m + 1 ≤ n then pb (n - (m + 1)) (m + 1) else 0 := by
  rw [pb, Finset.sum_range_succ', add_comm]
  simp only [zero_mul, Nat.sub_zero]
  congr 1
  split_ifs with hmn
  · rw [pb, Nat.div_eq_sub_div (by omega) hmn]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [Nat.succ_mul]
    omega
  · rw [Nat.div_eq_of_lt (by omega)]
    simp

theorem pb_eq_B (n : ℕ) : ∀ m, pb n m = B n m := by
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro m
    induction m with
    | zero =>
      rcases n with _ | n
      · rw [pb_zero_right, B_zero]; rfl
      · rw [pb_zero_right, B_succ_zero]; simp
    | succ m ihm =>
      rw [pb_succ, B_succ, ihm]
      split_ifs with hmn
      · rw [ihn _ (by omega)]
      · rfl

/-- The partition numbers can be computed with `pb`. -/
theorem p_eq_pb (m : ℕ) : p m = pb m m := by
  rw [pb_eq_B, B, Finset.filter_true_of_mem (fun π _ i hi => part_le π hi), Finset.card_univ, p]

/-- The first 10 listed terms of A000716 (kernel-checked through `p_eq_pb`). -/
theorem A000716_data :
    (List.range 10).map (fun n => A000716 n) = [1, 3, 9, 22, 51, 108, 221, 429, 810, 1479] := by
  simp only [A000716, partitionsOfKinds, p_eq_pb]
  decide +kernel

/-- The first 6 listed terms of A023005 (kernel-checked through `p_eq_pb`). -/
theorem A023005_data :
    (List.range 6).map (fun n => A023005 n) = [1, 6, 27, 98, 315, 918] := by
  simp only [A023005, partitionsOfKinds, p_eq_pb]
  decide +kernel

/-- Both conjectured identities hold for the first values of `n` (rows `1` to `10` for column 1
and rows `2` to `7` for column 2). A consistency check of the offsets, not a proof. -/
theorem statement_check :
    (∀ n < 10, T (n + 1) 1 = A000716 n) ∧ (∀ n < 6, T (n + 2) 2 = 2 * A023005 n) := by
  simp only [A000716, A023005, partitionsOfKinds, p_eq_pb]
  decide +kernel

end Math0.Statements.A355360
