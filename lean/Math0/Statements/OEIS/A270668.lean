/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A270668: domino tilings of the `(2n+1) × (2m+1)` board with a central hole

Source: https://oeis.org/A270668, _R. J. Mathar_, Mar 23 2016 (FORMULA section). Verbatim:
> Conjectured g.f. for column 3: ( -1 -4*x +543*x^2 -6238*x^3 +17032*x^4 -6238*x^5 +543*x^6
> -4*x^7 -x^8 ) / ( (x-1) *(x^2-7*x+1) *(x^2-23*x+1)
> *(x^4 -161*x^3 +576*x^2 -161*x +1) ). - _R. J. Mathar_, Mar 23 2016

The entry (_R. J. Mathar_, Mar 21 2016; more terms by _Alois P. Heinz_) is "Triangle read by
rows: The number of domino tilings of the (2n+1) X (2m+1) board with a central free square."
with the comment "Arrangements obtained by rotations and flips are counted as distinct."
Offset `0`: rows `n ≥ 0`, columns `0 ≤ m ≤ n`.

## Encoding

* *Domino tilings.* Cells are pairs `(i, j)` of naturals (row `i`, column `j`). A domino is a
  set `{(i, j), (i, j + 1)}` or `{(i, j), (i + 1, j)}` (`IsDomino`). A domino tiling of a finite
  set of cells `S` is a finite set `D` of dominoes, each contained in `S`, such that every cell of
  `S` lies in exactly one domino of `D` (`IsTiling`). A tiling is the set of its dominoes, so two
  tilings that differ by a rotation or a flip of the board are counted as distinct, as the entry
  says.
* *The triangle.* `region n m` is the `(2n+1) × (2m+1)` board (rows `0, …, 2n`, columns
  `0, …, 2m`) with its central square `(n, m)` removed, and `T n m` is the number of domino
  tilings of `region n m` (`Set.ncard` of the set of tilings, which is finite by
  `tilings_finite`). `T` is defined for all `n, m`; the entry's triangle is `T n m` for
  `0 ≤ m ≤ n`, read by rows with offset `0`, and `a` is that sequence:
  `a (n (n + 1) / 2 + m) = T n m` for `m ≤ n` (`a_spec`).
* *Computation.* `a` is computed through `Tc`, a broken-profile transfer matrix whose count
  vectors are packed into single natural numbers, and `T_eq_Tc` proves `T n m = Tc n m` for all
  `n, m`. `a_data` checks all `36` listed terms (rows `0` to `7`) in the kernel.
* *Which column, which series.* "Column 3" is read as the third column of the triangle, `m = 2`
  (boards `(2n+1) × 5`). Its odd rows vanish in the data (`T 3 2 = T 5 2 = T 7 2 = 0`; in general
  by the checkerboard coloring), and the expansion of the conjectured g.f. is
  `1 + 196 x + 31329 x^2 + 4941729 x^3 + 777852100 x^4 + …`, whose coefficients of `x^1, x^2, x^3`
  are the listed terms `T 2 2 = 196`, `T 4 2 = 31329`, `T 6 2 = 4941729`. So the g.f. is read as
  `∑_{k ≥ 0} T(2k, 2) x^k`. Its constant term is `T 0 2 = 1`, the number of tilings of the
  `1 × 5` strip with its central square removed: this board is outside the triangle (`m > n`) but
  is given by the same definition (`column_data` checks `T(2k, 2)` for `k ≤ 3`). The column
  `m = 3` (`75272, 135663392, …`) does not match the g.f.
* *The identity.* `statement` says, in `ℚ⟦X⟧`, that the power series with coefficients
  `T(2k, 2)`, `k ≥ 0`, equals `num * den⁻¹`, `num` and `den` being the stated numerator and
  denominator. `den` has constant coefficient `-1`, so it is invertible, and the statement is
  equivalent to `mk (fun k => T (2k) 2) * den = num` (`statement_iff`).
-/

namespace Math0.Statements.A270668

open Finset

/-! ### Domino tilings -/

/-- Cells of the grid: `(i, j)` is the cell in row `i` and column `j`. -/
abbrev Cell := ℕ × ℕ

/-- A domino: two edge-adjacent cells, `{(i, j), (i, j + 1)}` (horizontal) or
`{(i, j), (i + 1, j)}` (vertical). -/
def IsDomino (d : Finset Cell) : Prop :=
  ∃ i j : ℕ, d = {(i, j), (i, j + 1)} ∨ d = {(i, j), (i + 1, j)}

/-- `D` is a domino tiling of the finite set of cells `S`: a set of dominoes contained in `S`
such that every cell of `S` lies in exactly one of them. -/
def IsTiling (S : Finset Cell) (D : Finset (Finset Cell)) : Prop :=
  (∀ d ∈ D, IsDomino d ∧ d ⊆ S) ∧ ∀ x ∈ S, ∃! d, d ∈ D ∧ x ∈ d

/-- The `r × c` board: rows `0, …, r - 1` and columns `0, …, c - 1`. -/
def board (r c : ℕ) : Finset Cell := range r ×ˢ range c

/-- The `(2n+1) × (2m+1)` board with its central square `(n, m)` removed. -/
def region (n m : ℕ) : Finset Cell := (board (2 * n + 1) (2 * m + 1)).erase (n, m)

/-- A270668: `T n m` is the number of domino tilings of the `(2n+1) × (2m+1)` board with a
central free square. -/
noncomputable def T (n m : ℕ) : ℕ := {D | IsTiling (region n m) D}.ncard

/-! ### A computable version of `T` (see `T_eq_Tc`)

The cells of the `r × c` board are numbered row by row, cell `(i, j)` getting the index
`i * c + j`; there are `N = r * c` of them, and `hx` is the index of the hole. The count runs
through the cells `k = N - 1, …, 1, 0` (a broken-profile transfer matrix). Its state at cell `k`
is a set `M` of cells among `k, …, k + c - 1` that are already covered by dominoes placed at
earlier cells, cell `x` being recorded by bit `x % c` of `M`. The vector of counts, indexed by
`M < 2 ^ c`, is packed into one natural number, entry `M` occupying the `W` bits starting at
bit `M * W`; `dig W X M` reads it. -/

/-- `dbl X a e`: starting from the `a`-bit block `X`, double `e` times (`X ↦ X + X <<< a`,
`a ↦ 2 a`), i.e. repeat the block `2 ^ e` times. -/
def dbl : ℕ → ℕ → ℕ → ℕ
  | X, _, 0 => X
  | X, a, e + 1 => dbl (X + (X <<< a)) (2 * a) e

/-- The packed vector whose entry `M < 2 ^ c` is `2 ^ W - 1` if bit `s` of `M` is clear, and
`0` otherwise. -/
def clr (c W s : ℕ) : ℕ := dbl (2 ^ (2 ^ s * W) - 1) (2 ^ (s + 1) * W) (c - (s + 1))

/-- The packed vector all of whose entries `M < 2 ^ c` are `1`. -/
def ones (c W : ℕ) : ℕ := dbl 1 W c

/-- Index `q` is a cell of the board with `N` cells and is not the hole `hx`. -/
def inS (N hx q : ℕ) : Bool := decide (q < N ∧ q ≠ hx)

/-- One step of the transfer matrix, at cell `k` (`s = k % c`): from the vector `X` of counts
at cell `k + 1` to the vector at cell `k`. Entries with bit `s` set (cell `k` already covered)
come from entry `M - 2 ^ s`; the others from entry `M` if `k` is not a cell of the region, and
otherwise from placing a vertical domino on `k, k + c` (entry `M + 2 ^ s`) or a horizontal one on
`k, k + 1` (entry `M + 2 ^ (s + 1)`). -/
def stepP (c W N hx k X : ℕ) : ℕ :=
  (X &&& clr c W (k % c)) <<< (2 ^ (k % c) * W) +
    if inS N hx k then
      (if inS N hx (k + c) then (X >>> (2 ^ (k % c) * W)) &&& clr c W (k % c) else 0) +
      (if k % c + 1 < c ∧ inS N hx (k + 1) then
        (X >>> (2 ^ (k % c + 1) * W)) &&& (clr c W (k % c) &&& clr c W (k % c + 1)) else 0)
    else X &&& clr c W (k % c)

/-- The packed vector of counts at cell `N - j`. -/
def vecP (c W N hx : ℕ) : ℕ → ℕ
  | 0 => ones c W
  | j + 1 => stepP c W N hx (N - (j + 1)) (vecP c W N hx j)

/-- Computable version of `T` (see `T_eq_Tc`): entry `0` of the packed vector at cell `0`,
with `c = 2m+1` columns, `N = (2n+1)(2m+1)` cells, the hole at index `n c + m`, and entries of
`W = N / 2 + 1` bits. -/
def Tc (n m : ℕ) : ℕ :=
  vecP (2 * m + 1) ((2 * n + 1) * (2 * m + 1) / 2 + 1) ((2 * n + 1) * (2 * m + 1))
      (n * (2 * m + 1) + m) ((2 * n + 1) * (2 * m + 1)) %
    2 ^ ((2 * n + 1) * (2 * m + 1) / 2 + 1)

/-- Row and column of the `i`-th entry of a triangle read by rows, starting the search at row
`n` (`fuel` bounds the number of rows visited). -/
def rowCol : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, n, i => (n, i)
  | fuel + 1, n, i => if i ≤ n then (n, i) else rowCol fuel (n + 1) (i - (n + 1))

/-- A270668 read by rows, with the OEIS offset `0`: `a 0 = T 0 0`, `a 1 = T 1 0`,
`a 2 = T 1 1`, `a 3 = T 2 0`, … (see `a_spec`). -/
def a (i : ℕ) : ℕ := Tc (rowCol i 0 i).1 (rowCol i 0 i).2

/-- The definition reproduces all 36 terms listed in OEIS (rows `0` to `7`), kernel-checked. -/
theorem a_data : (List.range 36).map (fun i => a i) =
    [1, 0, 2, 1, 0, 196, 0, 32, 0, 75272, 1, 0, 31329, 0, 599466256, 0, 450, 0, 135663392, 0,
      28838245503008, 1, 0, 4941729, 0, 10956424382401, 0, 22463213552677201984, 0, 6272, 0,
      233075146752, 0, 5652453608244879872, 0, 123818965842734619629420672] := by
  decide +kernel

/-! ### Tilings: the first-cell recursion -/

theorem IsDomino.nonempty {d : Finset Cell} (hd : IsDomino d) : d.Nonempty := by
  obtain ⟨i, j, rfl | rfl⟩ := hd <;> exact insert_nonempty _ _

theorem tilings_finite (S : Finset Cell) : {D | IsTiling S D}.Finite := by
  refine (S.powerset.powerset.finite_toSet).subset ?_
  intro D hD
  rw [mem_coe, mem_powerset]
  intro d hd
  rw [mem_powerset]
  exact (hD.1 d hd).2

theorem ncard_tilings_empty : {D | IsTiling ∅ D}.ncard = 1 := by
  have : {D | IsTiling ∅ D} = {∅} := by
    ext D
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, -⟩
      rw [eq_empty_iff_forall_notMem]
      intro d hd
      obtain ⟨x, hx⟩ := (h1 d hd).1.nonempty
      simpa using (h1 d hd).2 hx
    · rintro rfl
      exact ⟨by simp, by simp⟩
  rw [this, Set.ncard_singleton]

theorem isTiling_insert {F d₀ : Finset Cell} {D : Finset (Finset Cell)} (hd₀ : IsDomino d₀)
    (hsub : d₀ ⊆ F) (hD : IsTiling (F \ d₀) D) : IsTiling F (insert d₀ D) := by
  refine ⟨?_, ?_⟩
  · intro d hd
    rcases mem_insert.1 hd with rfl | hd
    · exact ⟨hd₀, hsub⟩
    · exact ⟨(hD.1 d hd).1, (hD.1 d hd).2.trans sdiff_subset⟩
  · intro x hx
    by_cases hxd : x ∈ d₀
    · refine ⟨d₀, ⟨mem_insert_self _ _, hxd⟩, ?_⟩
      rintro d ⟨hd, hxd'⟩
      rcases mem_insert.1 hd with rfl | hd
      · rfl
      · exact absurd hxd (mem_sdiff.1 ((hD.1 d hd).2 hxd')).2
    · obtain ⟨d, ⟨hd, hxd'⟩, huniq⟩ := hD.2 x (mem_sdiff.2 ⟨hx, hxd⟩)
      refine ⟨d, ⟨mem_insert_of_mem hd, hxd'⟩, ?_⟩
      rintro d' ⟨hd', hxd''⟩
      rcases mem_insert.1 hd' with rfl | hd'
      · exact absurd hxd'' hxd
      · exact huniq d' ⟨hd', hxd''⟩

theorem isTiling_erase {F d₀ : Finset Cell} {D : Finset (Finset Cell)} (hD : IsTiling F D)
    (hd₀ : d₀ ∈ D) : IsTiling (F \ d₀) (D.erase d₀) := by
  refine ⟨?_, ?_⟩
  · intro d hd
    obtain ⟨hne, hd⟩ := mem_erase.1 hd
    refine ⟨(hD.1 d hd).1, fun x hx => mem_sdiff.2 ⟨(hD.1 d hd).2 hx, fun hx₀ => hne ?_⟩⟩
    obtain ⟨e, -, he⟩ := hD.2 x ((hD.1 d hd).2 hx)
    exact (he d ⟨hd, hx⟩).trans (he d₀ ⟨hd₀, hx₀⟩).symm
  · intro x hx
    obtain ⟨hxF, hx₀⟩ := mem_sdiff.1 hx
    obtain ⟨d, ⟨hd, hxd⟩, huniq⟩ := hD.2 x hxF
    refine ⟨d, ⟨mem_erase.2 ⟨fun h => hx₀ (h ▸ hxd), hd⟩, hxd⟩, ?_⟩
    rintro d' ⟨hd', hxd'⟩
    exact huniq d' ⟨(mem_erase.1 hd').2, hxd'⟩

/-- The tilings of `F` containing the domino `d₀ ⊆ F` correspond to the tilings of `F \ d₀`. -/
theorem ncard_tilings_mem {F d₀ : Finset Cell} (hd₀ : IsDomino d₀) (hsub : d₀ ⊆ F) :
    {D | IsTiling F D ∧ d₀ ∈ D}.ncard = {D | IsTiling (F \ d₀) D}.ncard := by
  have himage : {D | IsTiling F D ∧ d₀ ∈ D} = insert d₀ '' {D | IsTiling (F \ d₀) D} := by
    ext D
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨hD, hmem⟩
      exact ⟨D.erase d₀, isTiling_erase hD hmem, insert_erase hmem⟩
    · rintro ⟨D', hD', rfl⟩
      exact ⟨isTiling_insert hd₀ hsub hD', mem_insert_self _ _⟩
  have hn : ∀ D, IsTiling (F \ d₀) D → d₀ ∉ D := by
    intro D hD hmem
    obtain ⟨x, hx⟩ := hd₀.nonempty
    exact (mem_sdiff.1 ((hD.1 d₀ hmem).2 hx)).2 hx
  rw [himage]
  apply Set.InjOn.ncard_image
  intro D₁ h₁ D₂ h₂ heq
  rw [← erase_insert (hn D₁ h₁), heq, erase_insert (hn D₂ h₂)]

/-- The right neighbour of a cell. -/
def rt (p : Cell) : Cell := (p.1, p.2 + 1)

/-- The lower neighbour of a cell. -/
def dn (p : Cell) : Cell := (p.1 + 1, p.2)

/-- The first-cell recursion: if `p` is the lexicographically first cell of `F`, the domino
covering `p` is `{p, rt p}` or `{p, dn p}`. -/
theorem ncard_tilings_step {F : Finset Cell} {p : Cell} (hp : p ∈ F)
    (hmin : ∀ q ∈ F, q ≠ p → p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)) :
    {D | IsTiling F D}.ncard =
      (if rt p ∈ F then {D | IsTiling (F \ {p, rt p}) D}.ncard else 0) +
      (if dn p ∈ F then {D | IsTiling (F \ {p, dn p}) D}.ncard else 0) := by
  have hsplit : {D | IsTiling F D} =
      {D | IsTiling F D ∧ {p, rt p} ∈ D} ∪ {D | IsTiling F D ∧ {p, dn p} ∈ D} := by
    ext D
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro hD
      obtain ⟨d, ⟨hd, hpd⟩, -⟩ := hD.2 p hp
      obtain ⟨⟨i, j, rfl | rfl⟩, hsub⟩ := hD.1 d hd
      · rcases mem_insert.1 hpd with rfl | hpd
        · exact Or.inl ⟨hD, hd⟩
        · rw [mem_singleton] at hpd
          subst hpd
          have := hmin (i, j) (hsub (by simp)) (by simp)
          simp at this
      · rcases mem_insert.1 hpd with rfl | hpd
        · exact Or.inr ⟨hD, hd⟩
        · rw [mem_singleton] at hpd
          subst hpd
          have := hmin (i, j) (hsub (by simp)) (by simp)
          simp at this
    · rintro (⟨hD, -⟩ | ⟨hD, -⟩) <;> exact hD
  have hdisj : Disjoint {D | IsTiling F D ∧ {p, rt p} ∈ D} {D | IsTiling F D ∧ {p, dn p} ∈ D} := by
    rw [Set.disjoint_left]
    rintro D ⟨hD, h1⟩ ⟨-, h2⟩
    obtain ⟨d, -, huniq⟩ := hD.2 p hp
    have : ({p, rt p} : Finset Cell) = {p, dn p} :=
      (huniq _ ⟨h1, by simp⟩).trans (huniq _ ⟨h2, by simp⟩).symm
    have hmem : rt p ∈ ({p, dn p} : Finset Cell) := this ▸ (by simp)
    simp [rt, dn, Prod.ext_iff] at hmem
  rw [hsplit, Set.ncard_union_eq hdisj ((tilings_finite F).subset fun D h => h.1)
    ((tilings_finite F).subset fun D h => h.1)]
  congr 1
  · split_ifs with h
    · refine ncard_tilings_mem ⟨p.1, p.2, Or.inl rfl⟩ ?_
      intro x hx
      rcases mem_insert.1 hx with rfl | hx
      · exact hp
      · rw [mem_singleton] at hx; exact hx ▸ h
    · convert Set.ncard_empty (Finset (Finset Cell))
      ext D
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hD hmem
      exact h ((hD.1 _ hmem).2 (by simp))
  · split_ifs with h
    · refine ncard_tilings_mem ⟨p.1, p.2, Or.inr rfl⟩ ?_
      intro x hx
      rcases mem_insert.1 hx with rfl | hx
      · exact hp
      · rw [mem_singleton] at hx; exact hx ▸ h
    · convert Set.ncard_empty (Finset (Finset Cell))
      ext D
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hD hmem
      exact h ((hD.1 _ hmem).2 (by simp))

theorem exists_lex_min {F : Finset Cell} (hF : F.Nonempty) :
    ∃ p ∈ F, ∀ q ∈ F, q ≠ p → p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2) := by
  obtain ⟨p, hp, hmin⟩ := F.exists_min_image (fun q => toLex q) hF
  refine ⟨p, hp, fun q hq hne => ?_⟩
  have h2 : toLex p < toLex q := lt_of_le_of_ne (hmin q hq) (fun e => hne (toLex.injective e).symm)
  exact Prod.Lex.toLex_lt_toLex.1 h2

/-- A finite set of cells has at most `2 ^ (#F / 2)` domino tilings. -/
theorem ncard_tilings_le (n : ℕ) : ∀ F : Finset Cell, F.card ≤ n →
    {D | IsTiling F D}.ncard ≤ 2 ^ (F.card / 2) := by
  induction n with
  | zero =>
    intro F hF
    rw [card_eq_zero.1 (Nat.le_zero.1 hF), ncard_tilings_empty]
    simp
  | succ n ih =>
    intro F hn
    rcases F.eq_empty_or_nonempty with rfl | hne
    · rw [ncard_tilings_empty]; simp
    obtain ⟨p, hp, hmin⟩ := exists_lex_min hne
    rw [ncard_tilings_step hp hmin]
    have hbr : ∀ q, q ≠ p → q ∈ F →
        {D | IsTiling (F \ {p, q}) D}.ncard ≤ 2 ^ ((F.card - 2) / 2) := by
      intro q hqp hq
      have hcard : (F \ {p, q}).card = F.card - 2 := by
        rw [card_sdiff_of_subset (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption),
          card_pair_eq_two_iff.2 hqp.symm]
      have := ih (F \ {p, q}) (by rw [hcard]; omega)
      rwa [hcard] at this
    have hrt : rt p ≠ p := by simp [rt, Prod.ext_iff]
    have hdn : dn p ≠ p := by simp [dn, Prod.ext_iff]
    have hc2 : ∀ q, q ≠ p → q ∈ F → 2 ≤ F.card := by
      intro q hqp hq
      have : ({p, q} : Finset Cell).card = 2 := card_pair_eq_two_iff.2 hqp.symm
      have hsub : ({p, q} : Finset Cell) ⊆ F := by
        intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
      have := card_le_card hsub
      omega
    have hpow : 2 ^ ((F.card - 2) / 2) ≤ 2 ^ (F.card / 2) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    by_cases hr : rt p ∈ F
    · by_cases hd : dn p ∈ F
      · rw [if_pos hr, if_pos hd]
        have h1 := hbr _ hrt hr
        have h2 := hbr _ hdn hd
        have hc := hc2 _ hrt hr
        have : 2 ^ ((F.card - 2) / 2) + 2 ^ ((F.card - 2) / 2) = 2 ^ (F.card / 2) := by
          rw [← two_mul, ← pow_succ']
          congr 1
          omega
        omega
      · rw [if_pos hr, if_neg hd]
        have h1 := hbr _ hrt hr
        omega
    · by_cases hd : dn p ∈ F
      · rw [if_neg hr, if_pos hd]
        have h2 := hbr _ hdn hd
        omega
      · rw [if_neg hr, if_neg hd]
        simp

/-! ### Bit manipulations -/

theorem testBit_add_two_pow {M s : ℕ} (h : M.testBit s = false) (j : ℕ) :
    (M + 2 ^ s).testBit j = (decide (j = s) || M.testBit j) := by
  have hlt : M % 2 ^ s < 2 ^ s := Nat.mod_lt _ (Nat.two_pow_pos s)
  have hM : M = 2 ^ s * (M / 2 ^ s) + M % 2 ^ s := (Nat.div_add_mod M (2 ^ s)).symm
  have heven : M / 2 ^ s % 2 = 0 := by
    rw [Nat.testBit_eq_decide_div_mod_eq] at h
    simp only [decide_eq_false_iff_not] at h
    omega
  have hM' : M + 2 ^ s = 2 ^ s * (M / 2 ^ s + 1) + M % 2 ^ s := by
    rw [mul_add, mul_one]; omega
  rw [hM', Nat.testBit_two_pow_mul_add _ hlt]
  conv_rhs => rw [hM, Nat.testBit_two_pow_mul_add _ hlt]
  by_cases hj : j < s
  · simp [hj, Nat.ne_of_lt hj]
  · rw [if_neg hj, if_neg hj]
    rcases Nat.lt_or_ge s j with hsj | hsj
    · obtain ⟨i, hi⟩ : ∃ i, j - s = i + 1 := ⟨j - s - 1, by omega⟩
      have hjs : j ≠ s := by omega
      simp only [hi, hjs, decide_false, Bool.false_or, Nat.testBit_succ]
      congr 1
      omega
    · have hjs : j = s := by omega
      rw [hjs, Nat.sub_self, Nat.testBit_zero, decide_eq_true (rfl : s = s), Bool.true_or,
        decide_eq_true_iff]
      omega

theorem testBit_sub_two_pow {M s : ℕ} (h : M.testBit s = true) (j : ℕ) :
    (M - 2 ^ s).testBit j = (decide (j ≠ s) && M.testBit j) := by
  have hle : 2 ^ s ≤ M := Nat.ge_two_pow_of_testBit h
  have hM : M = (M - 2 ^ s) + 2 ^ s := by omega
  have h' : (M - 2 ^ s).testBit s = false := by
    have := Nat.testBit_two_pow_add_eq (M - 2 ^ s) s
    rw [add_comm, ← hM, h] at this
    cases hb : (M - 2 ^ s).testBit s
    · rfl
    · rw [hb] at this
      exact absurd this (by decide)
  have key := testBit_add_two_pow h' j
  rw [← hM] at key
  rw [key]
  by_cases hj : j = s
  · subst hj; simp [h']
  · simp [hj]

theorem testBit_sub_two_pow_of_false {M s : ℕ} (hle : 2 ^ s ≤ M) (h : M.testBit s = false) :
    (M - 2 ^ s).testBit s = true := by
  by_contra h'
  rw [Bool.not_eq_true] at h'
  have := testBit_add_two_pow h' s
  rw [Nat.sub_add_cancel hle, h] at this
  simp at this

theorem add_two_pow_lt {M s c : ℕ} (hM : M < 2 ^ c) (hs : s < c) (h : M.testBit s = false) :
    M + 2 ^ s < 2 ^ c := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_add_two_pow h,
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hM (Nat.pow_le_pow_right (by norm_num) hi))]
  simp only [Bool.or_false, decide_eq_false_iff_not]
  omega

theorem testBit_iff_mod (M s : ℕ) : M.testBit s = true ↔ 2 ^ s ≤ M % 2 ^ (s + 1) := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]
  have := Nat.mod_lt M (Nat.two_pow_pos s)
  have := Nat.mod_lt (M / 2 ^ s) (show 0 < 2 by norm_num)
  constructor
  · intro h; rw [h]; omega
  · intro h
    by_contra h'
    have h0 : M / 2 ^ s % 2 = 0 := by omega
    rw [h0] at h; omega

theorem eq_of_mod_eq_window {a x c : ℕ} (h1 : a ≤ x) (h2 : x < a + c) (h : x % c = a % c) :
    x = a := by
  have hd : c ∣ x - a := (Nat.modEq_iff_dvd' h1).1 h.symm
  have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
  omega

theorem mul_add_lt_iff {M W i n : ℕ} (hi : i < W) : M * W + i < n * W ↔ M < n := by
  constructor
  · intro h
    by_contra h'
    push Not at h'
    have := Nat.mul_le_mul_right W h'
    omega
  · intro h
    have := Nat.mul_le_mul_right W (show M + 1 ≤ n from h)
    rw [add_mul, one_mul] at this
    omega

theorem mul_add_mod' {M W i : ℕ} (hi : i < W) : (M * W + i) % W = i := by
  rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

theorem mul_add_div' {M W i : ℕ} (hi : i < W) : (M * W + i) / W = M := by
  rw [add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hi, zero_add]

/-! ### Packed vectors -/

/-- Entry `M` of the packed vector `X` (entries of `W` bits). -/
def dig (W X M : ℕ) : ℕ := (X >>> (M * W)) % 2 ^ W

theorem dig_lt (W X M : ℕ) : dig W X M < 2 ^ W := Nat.mod_lt _ (Nat.two_pow_pos W)

theorem testBit_dig (W X M i : ℕ) :
    (dig W X M).testBit i = (decide (i < W) && X.testBit (M * W + i)) := by
  simp [dig, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

theorem dig_and (W X Y M : ℕ) : dig W (X &&& Y) M = dig W X M &&& dig W Y M := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, testBit_dig, testBit_dig, testBit_dig, Nat.testBit_and]
  cases decide (i < W) <;> simp

theorem dig_shiftRight (W X a M : ℕ) : dig W (X >>> (a * W)) M = dig W X (M + a) := by
  simp only [dig, ← Nat.shiftRight_add]
  congr 2
  ring

theorem dig_shiftLeft (W X a M : ℕ) :
    dig W (X <<< (a * W)) M = if a ≤ M then dig W X (M - a) else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_dig, Nat.testBit_shiftLeft]
  split_ifs with ha
  · rw [testBit_dig]
    by_cases hi : i < W
    · have h1 : a * W ≤ M * W := Nat.mul_le_mul_right W ha
      have h2 : (M - a) * W = M * W - a * W := Nat.sub_mul M a W
      rw [show M * W + i - a * W = (M - a) * W + i by omega]
      simp [hi, show a * W ≤ M * W + i by omega]
    · simp [hi]
  · rw [Nat.zero_testBit]
    by_cases hi : i < W
    · have h1 : (M + 1) * W ≤ a * W := Nat.mul_le_mul_right W (by omega)
      rw [add_mul, one_mul] at h1
      have : ¬ (a * W ≤ M * W + i) := by omega
      simp [this]
    · simp [hi]

theorem dig_eq_div (W X M : ℕ) : dig W X M = X / (2 ^ W) ^ M % 2 ^ W := by
  rw [dig, Nat.shiftRight_eq_div_pow, ← pow_mul, mul_comm]

theorem mod_add_mod_lt {B X Y : ℕ} (hB : 0 < B) :
    ∀ M, (∀ i < M, X / B ^ i % B + Y / B ^ i % B < B) → X % B ^ M + Y % B ^ M < B ^ M
  | 0, _ => by rw [pow_zero, Nat.mod_one, Nat.mod_one]; norm_num
  | M + 1, h => by
    have ih := mod_add_mod_lt hB M (fun i hi => h i (by omega))
    have hM := h M (by omega)
    rw [Nat.mod_pow_succ, Nat.mod_pow_succ, pow_succ]
    have : B ^ M * (X / B ^ M % B) + B ^ M * (Y / B ^ M % B) + B ^ M ≤ B ^ M * B := by
      rw [← mul_add, ← Nat.mul_succ]
      exact Nat.mul_le_mul_left _ hM
    omega

/-- Adding packed vectors adds the entries, as long as no entry overflows. -/
theorem dig_add {W X Y M : ℕ} (h : ∀ i ≤ M, dig W X i + dig W Y i < 2 ^ W) :
    dig W (X + Y) M = dig W X M + dig W Y M := by
  simp only [dig_eq_div] at h ⊢
  have hB : 0 < 2 ^ W := Nat.two_pow_pos W
  have hpos : 0 < (2 ^ W) ^ M := pow_pos hB M
  have hlow := mod_add_mod_lt hB M (fun i hi => h i hi.le)
  have hdiv : (X + Y) / (2 ^ W) ^ M = X / (2 ^ W) ^ M + Y / (2 ^ W) ^ M := by
    have e : X + Y = (X % (2 ^ W) ^ M + Y % (2 ^ W) ^ M) +
        (2 ^ W) ^ M * (X / (2 ^ W) ^ M + Y / (2 ^ W) ^ M) := by
      have := Nat.div_add_mod X ((2 ^ W) ^ M)
      have := Nat.div_add_mod Y ((2 ^ W) ^ M)
      rw [mul_add]
      omega
    rw [e, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlow, zero_add]
  rw [hdiv, Nat.add_mod, Nat.mod_eq_of_lt (h M le_rfl)]

theorem testBit_dbl : ∀ (e X a : ℕ), 0 < a → X < 2 ^ a → ∀ j,
    (dbl X a e).testBit j = (decide (j < 2 ^ e * a) && X.testBit (j % a))
  | 0, X, a, ha, hX, j => by
    simp only [dbl, pow_zero, one_mul]
    by_cases hj : j < a
    · simp [hj, Nat.mod_eq_of_lt hj]
    · simp only [hj, decide_false, Bool.false_and]
      exact Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hX (Nat.pow_le_pow_right (by norm_num) (by omega)))
  | e + 1, X, a, ha, hX, j => by
    have hX' : X + (X <<< a) < 2 ^ (2 * a) := by
      rw [Nat.shiftLeft_eq, two_mul, pow_add]
      have : X + 1 ≤ 2 ^ a := hX
      nlinarith
    rw [dbl, testBit_dbl e _ (2 * a) (by omega) hX' j,
      show X + (X <<< a) = 2 ^ a * X + X by rw [Nat.shiftLeft_eq]; ring,
      Nat.testBit_two_pow_mul_add _ hX,
      show 2 ^ e * (2 * a) = 2 ^ (e + 1) * a by ring]
    have hmod : j % (2 * a) % a = j % a := Nat.mod_mod_of_dvd j (dvd_mul_left a 2)
    by_cases hj : j < 2 ^ (e + 1) * a
    · simp only [hj, decide_true, Bool.true_and]
      have hlt : j % (2 * a) < 2 * a := Nat.mod_lt _ (by omega)
      split_ifs with h
      · rw [← hmod, Nat.mod_eq_of_lt h]
      · have h1 : j % (2 * a) % a = j % (2 * a) - a := by
          rw [Nat.mod_eq_sub_mod (show a ≤ j % (2 * a) by omega),
            Nat.mod_eq_of_lt (show j % (2 * a) - a < a by omega)]
        rw [← hmod, h1]
    · simp [hj]

theorem testBit_clr {c W s : ℕ} (hs : s < c) (hW : 0 < W) (j : ℕ) :
    (clr c W s).testBit j =
      (decide (j < 2 ^ c * W) && decide (j % (2 ^ (s + 1) * W) < 2 ^ s * W)) := by
  have ha : 0 < 2 ^ (s + 1) * W := Nat.mul_pos (Nat.two_pow_pos _) hW
  have hX : 2 ^ (2 ^ s * W) - 1 < 2 ^ (2 ^ (s + 1) * W) := by
    have : 2 ^ (2 ^ s * W) ≤ 2 ^ (2 ^ (s + 1) * W) :=
      Nat.pow_le_pow_right (by norm_num)
        (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega)))
    have := Nat.two_pow_pos (2 ^ s * W)
    omega
  rw [clr, testBit_dbl _ _ _ ha hX, Nat.testBit_two_pow_sub_one, ← mul_assoc, ← pow_add,
    show c - (s + 1) + (s + 1) = c by omega]

theorem dig_clr {c W s : ℕ} (hs : s < c) (hW : 0 < W) (M : ℕ) :
    dig W (clr c W s) M = if M < 2 ^ c ∧ M.testBit s = false then 2 ^ W - 1 else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_dig]
  by_cases hi : i < W
  · rw [testBit_clr hs hW]
    have e2 : (M * W + i) % (2 ^ (s + 1) * W) = W * (M % 2 ^ (s + 1)) + i := by
      rw [mul_comm (2 ^ (s + 1)) W, Nat.mod_mul, mul_add_mod' hi, mul_add_div' hi]
      ring
    have e3 : W * (M % 2 ^ (s + 1)) + i < 2 ^ s * W ↔ M.testBit s = false := by
      rw [← Bool.not_eq_true, testBit_iff_mod]
      constructor
      · intro h h'
        have := Nat.mul_le_mul_left W h'
        rw [mul_comm W (2 ^ s)] at this
        omega
      · intro h
        push Not at h
        have : W * (M % 2 ^ (s + 1)) + W ≤ W * 2 ^ s := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left W h
        rw [mul_comm (2 ^ s) W]
        omega
    rw [e2]
    simp only [hi, decide_true, Bool.true_and, mul_add_lt_iff hi, e3]
    split_ifs with hc
    · rw [Nat.testBit_two_pow_sub_one]; simp [hi, hc.1, hc.2]
    · rw [Nat.zero_testBit]
      by_cases h1 : M < 2 ^ c
      · have h2 : ¬ M.testBit s = false := fun h2 => hc ⟨h1, h2⟩
        simp [h1, h2]
      · simp [h1]
  · split_ifs <;> simp [hi]

theorem dig_ones {c W : ℕ} (hW : 0 < W) (M : ℕ) :
    dig W (ones c W) M = if M < 2 ^ c then 1 else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_dig, ones, testBit_dbl c 1 W hW (Nat.one_lt_two_pow hW.ne')]
  by_cases hi : i < W
  · simp only [hi, decide_true, Bool.true_and, mul_add_lt_iff hi, mul_add_mod' hi]
    split_ifs with hM
    · simp [hM]
    · simp [hM]
  · split_ifs <;> simp [hi]
    rw [Nat.testBit_lt_two_pow]
    exact lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 1 ≤ i))

/-! ### Cell indices and the states of the transfer matrix -/

/-- The cell with index `q` on a board with `c` columns. -/
def cellOf (c q : ℕ) : Cell := (q / c, q % c)

/-- The index of the cell `p` on a board with `c` columns. -/
def idx (c : ℕ) (p : Cell) : ℕ := p.1 * c + p.2

theorem idx_cellOf (c q : ℕ) : idx c (cellOf c q) = q := Nat.div_add_mod' q c

theorem cellOf_injective (c : ℕ) : Function.Injective (cellOf c) := fun x y h => by
  rw [← idx_cellOf c x, h, idx_cellOf]

theorem cellOf_idx {c : ℕ} {p : Cell} (hp : p.2 < c) : cellOf c (idx c p) = p := by
  simp only [cellOf, idx]
  rw [mul_add_div' hp, mul_add_mod' hp]

theorem cellOf_lex {c : ℕ} {x y : ℕ} (h : x < y) :
    (cellOf c x).1 < (cellOf c y).1 ∨
      ((cellOf c x).1 = (cellOf c y).1 ∧ (cellOf c x).2 < (cellOf c y).2) := by
  simp only [cellOf]
  rcases lt_or_eq_of_le (Nat.div_le_div_right (c := c) h.le) with h1 | h1
  · exact Or.inl h1
  · refine Or.inr ⟨h1, ?_⟩
    have e1 := Nat.div_add_mod' x c
    have e2 := Nat.div_add_mod' y c
    rw [h1] at e1
    omega

theorem rt_cellOf {c k : ℕ} (hs : k % c + 1 < c) : rt (cellOf c k) = cellOf c (k + 1) := by
  rw [← cellOf_idx (p := rt (cellOf c k)) hs]
  congr 1
  simp only [idx, rt, cellOf]
  have := Nat.div_add_mod' k c
  omega

theorem dn_cellOf {c : ℕ} (hc : 0 < c) (k : ℕ) : dn (cellOf c k) = cellOf c (k + c) := by
  rw [← cellOf_idx (p := dn (cellOf c k)) (Nat.mod_lt k hc)]
  congr 1
  simp only [idx, dn, cellOf]
  have := Nat.div_add_mod' k c
  rw [add_mul, one_mul]
  omega

/-- The indices of the cells that are still free in the state `(k, M)`: cells `x ≥ k` of the
region (all `x < N` except the hole `hx`) whose bit `x % c` of `M` is clear if `x < k + c`. -/
def G (N c hx k M : ℕ) : Finset ℕ :=
  (range N).filter fun x => x ≠ hx ∧ k ≤ x ∧ ¬(x < k + c ∧ M.testBit (x % c) = true)

theorem mem_G {N c hx k M x : ℕ} :
    x ∈ G N c hx k M ↔ x < N ∧ x ≠ hx ∧ k ≤ x ∧ ¬(x < k + c ∧ M.testBit (x % c) = true) := by
  simp only [G, mem_filter, mem_range]

/-- The free cells in the state `(k, M)`. -/
def Fs (N c hx k M : ℕ) : Finset Cell := (G N c hx k M).image (cellOf c)

/-- The number of ways to complete the state `(k, M)` to a tiling. -/
noncomputable def cnt (N c hx k M : ℕ) : ℕ := {D | IsTiling (Fs N c hx k M) D}.ncard

section States

variable {N c hx : ℕ}

theorem mem_Fs_cellOf {k M y : ℕ} : cellOf c y ∈ Fs N c hx k M ↔ y ∈ G N c hx k M :=
  (cellOf_injective c).mem_finset_image

theorem snd_lt_of_mem_Fs (hc : 0 < c) {k M : ℕ} {p : Cell} (hp : p ∈ Fs N c hx k M) :
    p.2 < c := by
  obtain ⟨y, -, rfl⟩ := mem_image.1 hp
  exact Nat.mod_lt y hc

theorem Fs_sdiff (k M a b : ℕ) :
    Fs N c hx k M \ {cellOf c a, cellOf c b} = (G N c hx k M \ {a, b}).image (cellOf c) := by
  rw [Fs, image_sdiff _ _ (cellOf_injective c)]
  simp [image_insert, image_singleton]

theorem G_of_set (hc : 0 < c) {k M : ℕ} (h : M.testBit (k % c) = true) :
    G N c hx k M = G N c hx (k + 1) (M - 2 ^ (k % c)) := by
  ext x
  rw [mem_G, mem_G, testBit_sub_two_pow h]
  constructor
  · rintro ⟨hN, hh, hk, hw⟩
    have hxk : x ≠ k := by rintro rfl; exact hw ⟨by omega, h⟩
    refine ⟨hN, hh, by omega, ?_⟩
    rintro ⟨h1, h2⟩
    rw [Bool.and_eq_true, decide_eq_true_iff] at h2
    by_cases hx' : x < k + c
    · exact hw ⟨hx', h2.2⟩
    · have : x = k + c := by omega
      subst this
      exact h2.1 (Nat.add_mod_right k c)
  · rintro ⟨hN, hh, hk, hw⟩
    refine ⟨hN, hh, by omega, ?_⟩
    rintro ⟨h1, h2⟩
    apply hw
    refine ⟨by omega, ?_⟩
    rw [Bool.and_eq_true, decide_eq_true_iff]
    refine ⟨fun he => ?_, h2⟩
    have := eq_of_mod_eq_window (show k ≤ x by omega) h1 he
    omega

theorem G_of_notS (_hc : 0 < c) {k M : ℕ} (h : M.testBit (k % c) = false)
    (hk : ¬(k < N ∧ k ≠ hx)) : G N c hx k M = G N c hx (k + 1) M := by
  ext x
  rw [mem_G, mem_G]
  constructor
  · rintro ⟨hN, hh, hk', hw⟩
    have hxk : x ≠ k := by rintro rfl; exact hk ⟨hN, hh⟩
    refine ⟨hN, hh, by omega, ?_⟩
    rintro ⟨h1, h2⟩
    by_cases hx' : x < k + c
    · exact hw ⟨hx', h2⟩
    · have : x = k + c := by omega
      subst this
      rw [Nat.add_mod_right, h] at h2
      exact absurd h2 (by simp)
  · rintro ⟨hN, hh, hk', hw⟩
    exact ⟨hN, hh, by omega, fun ⟨h1, h2⟩ => hw ⟨by omega, h2⟩⟩

theorem G_down (hc : 0 < c) {k M : ℕ} (h : M.testBit (k % c) = false) :
    G N c hx k M \ {k, k + c} = G N c hx (k + 1) (M + 2 ^ (k % c)) := by
  ext x
  rw [mem_sdiff, mem_G, mem_G, testBit_add_two_pow h, mem_insert, mem_singleton]
  constructor
  · rintro ⟨⟨hN, hh, hk, hw⟩, hne⟩
    push Not at hne
    refine ⟨hN, hh, by omega, ?_⟩
    rintro ⟨h1, h2⟩
    have h1' : x < k + c := by omega
    rw [Bool.or_eq_true, decide_eq_true_iff] at h2
    rcases h2 with h2 | h2
    · exact absurd (eq_of_mod_eq_window (by omega) h1' h2) hne.1
    · exact hw ⟨h1', h2⟩
  · rintro ⟨hN, hh, hk, hw⟩
    have hne : x ≠ k + c := by
      rintro rfl
      exact hw ⟨by omega, by rw [Nat.add_mod_right]; simp⟩
    refine ⟨⟨hN, hh, by omega, ?_⟩, ?_⟩
    · rintro ⟨h1, h2⟩
      exact hw ⟨by omega, by rw [h2]; simp⟩
    · push Not
      exact ⟨by omega, hne⟩

theorem G_right (hc : 0 < c) {k M : ℕ} (h : M.testBit (k % c) = false)
    (h' : M.testBit (k % c + 1) = false) (hs : k % c + 1 < c) :
    G N c hx k M \ {k, k + 1} = G N c hx (k + 1) (M + 2 ^ (k % c + 1)) := by
  have hk1 : (k + 1) % c = k % c + 1 := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < c by omega), Nat.mod_eq_of_lt hs]
  ext x
  rw [mem_sdiff, mem_G, mem_G, testBit_add_two_pow h', mem_insert, mem_singleton]
  constructor
  · rintro ⟨⟨hN, hh, hk, hw⟩, hne⟩
    push Not at hne
    refine ⟨hN, hh, by omega, ?_⟩
    rintro ⟨h1, h2⟩
    rw [Bool.or_eq_true, decide_eq_true_iff] at h2
    by_cases hx' : x < k + c
    · rcases h2 with h2 | h2
      · rw [← hk1] at h2
        exact hne.2 (eq_of_mod_eq_window (by omega) (by omega) h2)
      · exact hw ⟨hx', h2⟩
    · have hxe : x = k + c := by omega
      subst hxe
      rw [Nat.add_mod_right] at h2
      rcases h2 with h2 | h2
      · omega
      · rw [h] at h2
        exact absurd h2 (by simp)
  · rintro ⟨hN, hh, hk, hw⟩
    have hne : x ≠ k + 1 := by
      rintro rfl
      exact hw ⟨by omega, by rw [hk1]; simp⟩
    refine ⟨⟨hN, hh, by omega, ?_⟩, ?_⟩
    · rintro ⟨h1, h2⟩
      exact hw ⟨by omega, by rw [h2]; simp⟩
    · push Not
      exact ⟨by omega, hne⟩

theorem cnt_end {k M : ℕ} (hk : N ≤ k) : cnt N c hx k M = 1 := by
  have : G N c hx k M = ∅ := by
    ext x
    simp only [mem_G, notMem_empty, iff_false]
    rintro ⟨h1, -, h3, -⟩
    omega
  rw [cnt, Fs, this, image_empty, ncard_tilings_empty]

theorem cnt_of_set (hc : 0 < c) {k M : ℕ} (h : M.testBit (k % c) = true) :
    cnt N c hx k M = cnt N c hx (k + 1) (M - 2 ^ (k % c)) := by
  rw [cnt, cnt, Fs, Fs, G_of_set hc h]

theorem cnt_of_notS (hc : 0 < c) {k M : ℕ} (h : M.testBit (k % c) = false)
    (hk : inS N hx k = false) : cnt N c hx k M = cnt N c hx (k + 1) M := by
  have hk' : ¬(k < N ∧ k ≠ hx) := by simpa [inS] using hk
  rw [cnt, cnt, Fs, Fs, G_of_notS hc h hk']

theorem cnt_of_free (hc : 0 < c) {k M : ℕ} (h : M.testBit (k % c) = false)
    (hk : inS N hx k = true) :
    cnt N c hx k M =
      (if k % c + 1 < c ∧ inS N hx (k + 1) = true ∧ M.testBit (k % c + 1) = false then
        cnt N c hx (k + 1) (M + 2 ^ (k % c + 1)) else 0) +
      (if inS N hx (k + c) = true then cnt N c hx (k + 1) (M + 2 ^ (k % c)) else 0) := by
  simp only [inS, decide_eq_true_iff] at hk ⊢
  have hkG : k ∈ G N c hx k M := mem_G.2 ⟨hk.1, hk.2, le_rfl, fun ⟨_, h2⟩ => by
    rw [h] at h2; exact absurd h2 (by simp)⟩
  have hp : cellOf c k ∈ Fs N c hx k M := mem_Fs_cellOf.2 hkG
  have hmin : ∀ q ∈ Fs N c hx k M, q ≠ cellOf c k →
      (cellOf c k).1 < q.1 ∨ ((cellOf c k).1 = q.1 ∧ (cellOf c k).2 < q.2) := by
    intro q hq hne
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hq
    have hky : k ≤ y := (mem_G.1 hy).2.2.1
    have : k ≠ y := fun e => hne (e ▸ rfl)
    exact cellOf_lex (by omega)
  rw [cnt, ncard_tilings_step hp hmin]
  congr 1
  · by_cases hs : k % c + 1 < c
    · have hk1 : (k + 1) % c = k % c + 1 := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < c by omega), Nat.mod_eq_of_lt hs]
      have hmem : k + 1 ∈ G N c hx k M ↔
          (k + 1 < N ∧ k + 1 ≠ hx) ∧ M.testBit (k % c + 1) = false := by
        rw [mem_G, hk1]
        constructor
        · rintro ⟨h1, h2, -, h4⟩
          refine ⟨⟨h1, h2⟩, ?_⟩
          cases hb : M.testBit (k % c + 1)
          · rfl
          · exact absurd ⟨by omega, hb⟩ h4
        · rintro ⟨⟨h1, h2⟩, h3⟩
          refine ⟨h1, h2, by omega, ?_⟩
          rintro ⟨-, h4⟩
          rw [h3] at h4
          exact absurd h4 (by simp)
      rw [rt_cellOf hs]
      by_cases hcond : (k + 1 < N ∧ k + 1 ≠ hx) ∧ M.testBit (k % c + 1) = false
      · rw [if_pos (mem_Fs_cellOf.2 (hmem.2 hcond)),
          if_pos (show k % c + 1 < c ∧ (k + 1 < N ∧ k + 1 ≠ hx) ∧
            M.testBit (k % c + 1) = false from ⟨hs, hcond⟩), Fs_sdiff, G_right hc h hcond.2 hs]
        rfl
      · rw [if_neg (fun h' => hcond (hmem.1 (mem_Fs_cellOf.1 h'))),
          if_neg (show ¬(k % c + 1 < c ∧ (k + 1 < N ∧ k + 1 ≠ hx) ∧
            M.testBit (k % c + 1) = false) from fun h' => hcond h'.2)]
    · have : rt (cellOf c k) ∉ Fs N c hx k M := fun hm => by
        have := snd_lt_of_mem_Fs hc hm
        simp only [rt, cellOf] at this
        omega
      rw [if_neg this, if_neg (fun h' => hs h'.1)]
  · rw [dn_cellOf hc k]
    have hmem : k + c ∈ G N c hx k M ↔ k + c < N ∧ k + c ≠ hx := by
      rw [mem_G]
      constructor
      · rintro ⟨h1, h2, -, -⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, h2, by omega, fun ⟨h3, _⟩ => by omega⟩
    by_cases hcond : k + c < N ∧ k + c ≠ hx
    · rw [if_pos (mem_Fs_cellOf.2 (hmem.2 hcond)), if_pos hcond, Fs_sdiff, G_down hc h]
      rfl
    · rw [if_neg (fun h' => hcond (hmem.1 (mem_Fs_cellOf.1 h'))), if_neg hcond]

theorem cnt_lt {W' : ℕ} (hN : N / 2 ≤ W') (k M : ℕ) : cnt N c hx k M < 2 ^ (W' + 1) := by
  have h1 : (Fs N c hx k M).card ≤ N := by
    calc (Fs N c hx k M).card ≤ (G N c hx k M).card := card_image_le
      _ ≤ (range N).card := card_filter_le _ _
      _ = N := card_range N
  calc cnt N c hx k M ≤ 2 ^ ((Fs N c hx k M).card / 2) := ncard_tilings_le _ _ le_rfl
    _ ≤ 2 ^ W' := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ < 2 ^ (W' + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-! ### Correctness of the packed transfer matrix -/

theorem dig_stepP (hc : 0 < c) {W k X : ℕ} (hW : 0 < W)
    (hbound : ∀ M, cnt N c hx k M < 2 ^ W)
    (hX : ∀ M < 2 ^ c, dig W X M = cnt N c hx (k + 1) M) :
    ∀ M < 2 ^ c, dig W (stepP c W N hx k X) M = cnt N c hx k M := by
  set s := k % c with hs_def
  have hs : s < c := Nat.mod_lt k hc
  -- the entries of the masked vector
  have hP : ∀ M < 2 ^ c, dig W (X &&& clr c W s) M =
      if M.testBit s = true then 0 else cnt N c hx (k + 1) M := by
    intro M hM
    rw [dig_and, dig_clr hs hW]
    by_cases hb : M.testBit s = true
    · rw [if_neg (fun h => by rw [hb] at h; exact absurd h.2 (by simp)), if_pos hb, Nat.and_zero]
    · rw [Bool.not_eq_true] at hb
      rw [if_pos ⟨hM, hb⟩, if_neg (by rw [hb]; simp), Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_eq_of_lt (dig_lt _ _ _), hX M hM]
  have hA : ∀ M < 2 ^ c, dig W ((X &&& clr c W s) <<< (2 ^ s * W)) M =
      if M.testBit s = true then cnt N c hx (k + 1) (M - 2 ^ s) else 0 := by
    intro M hM
    have hM' : M - 2 ^ s < 2 ^ c := lt_of_le_of_lt (Nat.sub_le _ _) hM
    rw [dig_shiftLeft]
    by_cases hb : M.testBit s = true
    · have hle : 2 ^ s ≤ M := Nat.ge_two_pow_of_testBit hb
      have hb' : (M - 2 ^ s).testBit s = false := by
        rw [testBit_sub_two_pow hb]; simp
      rw [if_pos hle, if_pos hb, hP _ hM',
        if_neg (show ¬((M - 2 ^ s).testBit s = true) by rw [hb']; simp)]
    · have hb' : M.testBit s = false := by simpa using hb
      rw [if_neg hb]
      by_cases hle : 2 ^ s ≤ M
      · rw [if_pos hle, hP _ hM', if_pos (testBit_sub_two_pow_of_false hle hb')]
      · rw [if_neg hle]
  have hfinal : ∀ Y, (∀ M < 2 ^ c, dig W Y M = if M.testBit s = true then 0 else cnt N c hx k M) →
      ∀ M < 2 ^ c, dig W ((X &&& clr c W s) <<< (2 ^ s * W) + Y) M = cnt N c hx k M := by
    intro Y hY
    have hsum : ∀ M < 2 ^ c,
        dig W ((X &&& clr c W s) <<< (2 ^ s * W)) M + dig W Y M = cnt N c hx k M := by
      intro M hM
      rw [hA M hM, hY M hM]
      split_ifs with hb
      · rw [add_zero, ← cnt_of_set hc hb]
      · rw [zero_add]
    intro M hM
    rw [dig_add (fun i hi => by rw [hsum i (lt_of_le_of_lt hi hM)]; exact hbound i), hsum M hM]
  unfold stepP
  rw [← hs_def]
  apply hfinal
  intro M hM
  have h0 : ∀ M', dig W 0 M' = 0 := fun M' => by simp [dig]
  by_cases hk : inS N hx k = true
  · -- `k` is a cell of the region
    rw [if_pos hk]
    have hD : ∀ M' < 2 ^ c,
        dig W (if inS N hx (k + c) = true then (X >>> (2 ^ s * W)) &&& clr c W s else 0) M' =
        if M'.testBit s = true then 0 else
          if inS N hx (k + c) = true then cnt N c hx (k + 1) (M' + 2 ^ s) else 0 := by
      intro M' hM'
      by_cases hkc : inS N hx (k + c) = true
      · rw [if_pos hkc, if_pos hkc, dig_and, dig_clr hs hW]
        by_cases hb : M'.testBit s = true
        · rw [if_pos hb, if_neg (show ¬(M' < 2 ^ c ∧ M'.testBit s = false) from
            fun h => by rw [hb] at h; exact absurd h.2 (by simp))]
          simp only [Nat.and_zero]
        · have hb' : M'.testBit s = false := by simpa using hb
          rw [if_neg hb, if_pos (show M' < 2 ^ c ∧ M'.testBit s = false from ⟨hM', hb'⟩),
            dig_shiftRight, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (dig_lt _ _ _),
            hX _ (add_two_pow_lt hM' hs hb')]
      · rw [if_neg hkc, if_neg hkc, h0]
        split_ifs <;> rfl
    have hR : ∀ M' < 2 ^ c, dig W (if s + 1 < c ∧ inS N hx (k + 1) = true then
          (X >>> (2 ^ (s + 1) * W)) &&& (clr c W s &&& clr c W (s + 1)) else 0) M' =
        if M'.testBit s = true then 0 else
          if s + 1 < c ∧ inS N hx (k + 1) = true ∧ M'.testBit (s + 1) = false then
            cnt N c hx (k + 1) (M' + 2 ^ (s + 1)) else 0 := by
      intro M' hM'
      by_cases hcond : s + 1 < c ∧ inS N hx (k + 1) = true
      · rw [if_pos hcond, dig_and, dig_and, dig_clr hs hW, dig_clr hcond.1 hW]
        by_cases hb : M'.testBit s = true
        · rw [if_pos hb, if_neg (show ¬(M' < 2 ^ c ∧ M'.testBit s = false) from
            fun h => by rw [hb] at h; exact absurd h.2 (by simp))]
          simp only [Nat.zero_and, Nat.and_zero]
        · have hb' : M'.testBit s = false := by simpa using hb
          rw [if_neg hb, if_pos (show M' < 2 ^ c ∧ M'.testBit s = false from ⟨hM', hb'⟩)]
          by_cases hb1 : M'.testBit (s + 1) = false
          · rw [if_pos (show M' < 2 ^ c ∧ M'.testBit (s + 1) = false from ⟨hM', hb1⟩),
              if_pos (show s + 1 < c ∧ inS N hx (k + 1) = true ∧ M'.testBit (s + 1) = false from
                ⟨hcond.1, hcond.2, hb1⟩), Nat.and_self, dig_shiftRight,
              Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (dig_lt _ _ _),
              hX _ (add_two_pow_lt hM' hcond.1 hb1)]
          · rw [if_neg (show ¬(M' < 2 ^ c ∧ M'.testBit (s + 1) = false) from fun h => hb1 h.2),
              if_neg (show ¬(s + 1 < c ∧ inS N hx (k + 1) = true ∧
                M'.testBit (s + 1) = false) from fun h => hb1 h.2.2)]
            simp only [Nat.and_zero]
      · rw [if_neg hcond, h0]
        split_ifs with h1 h2 <;> first | rfl | exact absurd ⟨h2.1, h2.2.1⟩ hcond
    have hsum2 : ∀ M' < 2 ^ c,
        dig W (if inS N hx (k + c) = true then (X >>> (2 ^ s * W)) &&& clr c W s else 0) M' +
        dig W (if s + 1 < c ∧ inS N hx (k + 1) = true then
          (X >>> (2 ^ (s + 1) * W)) &&& (clr c W s &&& clr c W (s + 1)) else 0) M' =
        if M'.testBit s = true then 0 else cnt N c hx k M' := by
      intro M' hM'
      rw [hD M' hM', hR M' hM']
      by_cases hb : M'.testBit s = true
      · simp [hb]
      · have hb' : M'.testBit s = false := by simpa using hb
        rw [if_neg hb, if_neg hb, if_neg hb, cnt_of_free hc hb' hk]
        exact add_comm _ _
    rw [dig_add (fun i hi => by
      rw [hsum2 i (lt_of_le_of_lt hi hM)]
      split_ifs
      · exact Nat.two_pow_pos W
      · exact hbound i), hsum2 M hM]
  · have hk' : inS N hx k = false := by simpa using hk
    rw [if_neg hk, hP M hM]
    by_cases hb : M.testBit s = true
    · rw [if_pos hb, if_pos hb]
    · have hb' : M.testBit s = false := by simpa using hb
      rw [if_neg hb, if_neg hb, cnt_of_notS hc hb' hk']

end States

/-- The packed vector at cell `N - j` holds the completion counts. -/
theorem dig_vecP {N c hx W : ℕ} (hc : 0 < c) (hW : 0 < W)
    (hbound : ∀ k M, cnt N c hx k M < 2 ^ W) :
    ∀ j ≤ N, ∀ M < 2 ^ c, dig W (vecP c W N hx j) M = cnt N c hx (N - j) M
  | 0, _, M, hM => by
    rw [vecP, dig_ones hW, if_pos hM, Nat.sub_zero, cnt_end le_rfl]
  | j + 1, hj, M, hM => by
    rw [vecP]
    have hk : N - (j + 1) + 1 = N - j := by omega
    refine dig_stepP hc hW (hbound _) ?_ M hM
    intro M' hM'
    rw [hk]
    exact dig_vecP hc hW hbound j (by omega) M' hM'

/-- The region is the set of free cells of the initial state. -/
theorem region_eq (n m : ℕ) :
    region n m = Fs ((2 * n + 1) * (2 * m + 1)) (2 * m + 1) (n * (2 * m + 1) + m) 0 0 := by
  ext p
  simp only [region, board, Fs, mem_erase, mem_product, mem_range, mem_image, mem_G,
    Nat.zero_testBit, Bool.false_eq_true, and_false, not_false_eq_true, and_true, zero_le]
  constructor
  · rintro ⟨hne, h1, h2⟩
    refine ⟨idx (2 * m + 1) p, ⟨(mul_add_lt_iff h2).2 h1, fun e => hne ?_⟩, cellOf_idx h2⟩
    rw [← cellOf_idx h2, e, ← cellOf_idx (p := (n, m)) (show m < 2 * m + 1 by omega)]
    rfl
  · rintro ⟨x, ⟨hx, hne⟩, rfl⟩
    refine ⟨fun e => hne ?_, ?_, Nat.mod_lt _ (by omega)⟩
    · rw [← idx_cellOf (2 * m + 1) x, e]
      rfl
    · exact (Nat.div_lt_iff_lt_mul (by omega)).2 hx

/-- `T` is computed by `Tc`. -/
theorem T_eq_Tc (n m : ℕ) : T n m = Tc n m := by
  have hc : 0 < 2 * m + 1 := by omega
  have hb : ∀ k M, cnt ((2 * n + 1) * (2 * m + 1)) (2 * m + 1) (n * (2 * m + 1) + m) k M <
      2 ^ ((2 * n + 1) * (2 * m + 1) / 2 + 1) := fun k M => cnt_lt le_rfl k M
  have := dig_vecP hc (by omega) hb _ le_rfl 0 (Nat.two_pow_pos _)
  rw [Nat.sub_self] at this
  rw [T, region_eq, Tc, ← cnt, ← this, dig, zero_mul, Nat.shiftRight_zero]

theorem rowCol_spec : ∀ (d n fuel m : ℕ), d ≤ fuel → m ≤ n + d →
    rowCol fuel n ((∑ j ∈ range d, (n + 1 + j)) + m) = (n + d, m)
  | 0, n, fuel, m, _, hm => by
    rcases fuel with _ | fuel
    · simp [rowCol]
    · simp [rowCol, show m ≤ n by omega]
  | d + 1, n, fuel, m, hd, hm => by
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [sum_range_succ']
    have h1 : ¬ (∑ j ∈ range d, (n + 1 + (j + 1)) + (n + 1 + 0) + m ≤ n) := by omega
    rw [rowCol, if_neg h1]
    have h2 : ∑ j ∈ range d, (n + 1 + (j + 1)) + (n + 1 + 0) + m - (n + 1) =
        ∑ j ∈ range d, (n + 1 + 1 + j) + m := by
      have : ∑ j ∈ range d, (n + 1 + (j + 1)) = ∑ j ∈ range d, (n + 1 + 1 + j) :=
        sum_congr rfl fun j _ => by ring
      omega
    rw [h2, rowCol_spec d (n + 1) fuel m (by omega) (by omega)]
    congr 1
    omega

/-- `a` is the triangle `T` read by rows (offset `0`). -/
theorem a_spec (n m : ℕ) (hm : m ≤ n) : a (n * (n + 1) / 2 + m) = T n m := by
  have hsum : ∀ n : ℕ, ∑ j ∈ range n, (0 + 1 + j) = n * (n + 1) / 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih,
        show (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) by ring]
      omega
  have hge : n ≤ ∑ j ∈ range n, (0 + 1 + j) := by
    rw [sum_add_distrib]; simp
  rw [a, ← hsum n, rowCol_spec n 0 _ m (by omega) (by omega), T_eq_Tc, zero_add]

/-! ### The conjecture -/

open PowerSeries

/-- The numerator of the conjectured generating function. -/
noncomputable def num : ℚ⟦X⟧ :=
  -1 - 4 * X + 543 * X ^ 2 - 6238 * X ^ 3 + 17032 * X ^ 4 - 6238 * X ^ 5 + 543 * X ^ 6 -
    4 * X ^ 7 - X ^ 8

/-- The denominator of the conjectured generating function. -/
noncomputable def den : ℚ⟦X⟧ :=
  (X - 1) * (X ^ 2 - 7 * X + 1) * (X ^ 2 - 23 * X + 1) *
    (X ^ 4 - 161 * X ^ 3 + 576 * X ^ 2 - 161 * X + 1)

/-- Mathar's conjecture: the generating function `∑_{k ≥ 0} T(2k, 2) x^k` of column `m = 2`
(the third column, `(4k+1) × 5` boards) equals `num / den`. -/
def statement : Prop :=
  PowerSeries.mk (fun k => (T (2 * k) 2 : ℚ)) = num * den⁻¹

theorem constantCoeff_den : constantCoeff den = -1 := by
  simp [den]

/-- The conjecture with the denominator cleared. -/
theorem statement_iff : statement ↔ PowerSeries.mk (fun k => (T (2 * k) 2 : ℚ)) * den = num := by
  rw [statement, eq_mul_inv_iff_mul_eq (by rw [constantCoeff_den]; norm_num)]

/-- Sanity check: the first coefficients `T(2k, 2)`, `k = 0, …, 3`, of the series in `statement`
are `1, 196, 31329, 4941729`, the first coefficients of the conjectured g.f. (kernel-checked). -/
theorem column_data : (List.range 4).map (fun k => T (2 * k) 2) = [1, 196, 31329, 4941729] := by
  rw [show (fun k => T (2 * k) 2) = fun k => Tc (2 * k) 2 from funext fun k => T_eq_Tc _ _]
  decide +kernel

end Math0.Statements.A270668
