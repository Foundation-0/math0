/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A060693: Schulte's alternating quadratic sum over the Schröder-peaks triangle

Source: https://oeis.org/A060693, Werner Schulte, Jan 11 2017 (FORMULA section). Verbatim:
> Conjecture: Sum_{k=0..n} (-1)^k*T(n,k)*(n+1-k)^2 = 1+n+n^2.

The entry (F. Chapoton, Apr 20 2001; name by Peter Luschny, Jul 26 2017; offset `0`, keyword
`tabl`) is "Triangle (0 <= k <= n) read by rows: T(n, k) is the number of Schröder paths from
(0,0) to (2n,0) having k peaks." A comment by Emeric Deutsch explains: "Schroeder paths (i.e.,
consisting of steps U=(1,1), D=(1,-1), H=(2,0) and never going below the x-axis) from (0,0) to
(2n,0), having k peaks. Example: T(2,1)=3 because we have UU*DD, U*DH and HU*D, the peaks being
shown by *."

## Encoding

* *Paths.* A path is a word `p : List Step` over the steps `U = (1,1)`, `D = (1,-1)`,
  `H = (2,0)`, drawn from `(0,0)`. After the initial segment `q` of `p` the path is at the point
  `(width q, height q)`, where `width` (resp. `height`) adds up the `x`- (resp. `y`-)
  displacements of the steps.
* *Schröder paths.* `IsSchroderPath n p`: the path ends at `(2n, 0)` (`width p = 2 * n` and
  `height p = 0`) and never goes below the `x`-axis: every initial segment `q ∈ p.inits` ends at
  height `≥ 0`. (Checking the vertices suffices: between two vertices the path is a straight
  segment.)
* *Peaks.* A peak is a `U` step immediately followed by a `D` step; `peaks p` is the number of
  adjacent pairs `(U, D)` in `p`, i.e. of positions `i` with `p[i] = U` and `p[i+1] = D`.
* *The triangle.* `words m` lists all words of total width `m` (`mem_words`; it has no
  repetitions, `nodup_words`). `schroderPaths n` is the finite set of Schröder paths from `(0,0)`
  to `(2n,0)` (`mem_schroderPaths`), and `T n k` is the number of those with exactly `k` peaks
  (`T_eq_ncard` restates it as the cardinality of
  `{p | IsSchroderPath n p ∧ peaks p = k}`). `T` is computable but enumerates `words (2n)`, so
  for evaluation we use a dynamic program: `cnt m h b k` counts the words of width `m` that,
  started at height `h`, stay weakly above the axis and end on it with `k` peaks (an initial `D`
  counts as a peak when `b = true`, i.e. when the step before was a `U`). It satisfies a
  three-term recursion in `m` according to the first step (`cnt_step`), and the tables `tabs m`
  store `cnt m` and `cnt (m+1)` (`tabs_spec`). `T_eq_Tfast` proves `T n k = Tfast n k` for all
  `n, k`, where `Tfast n k` reads the value off the table.
* *Data.* `T_data` checks all 56 listed terms (rows `n = 0, …, 9` and `T(10,0) = 16796`) in the
  kernel. `a` is the triangle read by rows (the OEIS sequence itself, offset `0`), and `a_data`
  checks the same 56 terms as `a 0, …, a 55`.
* *The conjecture.* `statement`: for every `n ≥ 0`,
  `∑_{k=0}^{n} (-1)^k · T(n,k) · (n+1-k)^2 = 1 + n + n^2`, computed in `ℤ` (so `n + 1 - k` is
  integer subtraction; it is positive for `k ≤ n` anyway). `statement_check` confirms the
  identity for `n ≤ 12` (a sanity check of the transcription, not a proof).
-/

namespace Math0.Statements.A060693

/-! ### Schröder paths and peaks -/

/-- The steps of a Schröder path: `U = (1,1)`, `D = (1,-1)`, `H = (2,0)`. -/
inductive Step
  | U
  | D
  | H
  deriving DecidableEq, Repr

namespace Step

/-- The `x`-displacement of a step. -/
def dx : Step → ℕ
  | U => 1
  | D => 1
  | H => 2

/-- The `y`-displacement of a step. -/
def dy : Step → ℤ
  | U => 1
  | D => -1
  | H => 0

end Step

open Step

/-- The `x`-coordinate reached by the path `p` started at `(0,0)`. -/
def width (p : List Step) : ℕ := (p.map Step.dx).sum

/-- The `y`-coordinate reached by the path `p` started at `(0,0)`. -/
def height (p : List Step) : ℤ := (p.map Step.dy).sum

/-- `p` is a Schröder path from `(0,0)` to `(2n,0)`: it ends at `(2n,0)` and never goes below the
`x`-axis (every initial segment of `p` ends at height `≥ 0`). -/
def IsSchroderPath (n : ℕ) (p : List Step) : Prop :=
  width p = 2 * n ∧ height p = 0 ∧ ∀ q ∈ p.inits, 0 ≤ height q

instance (n : ℕ) : DecidablePred (IsSchroderPath n) := fun p => by
  unfold IsSchroderPath; infer_instance

/-- The number of peaks of `p`: adjacent pairs of steps `U` followed by `D`. -/
def peaks (p : List Step) : ℕ := (p.zip p.tail).count (U, D)

/-- All words over `{U, D, H}` of total width `m`. -/
def words : ℕ → List (List Step)
  | 0 => [[]]
  | 1 => [[U], [D]]
  | m + 2 => (words (m + 1)).map (U :: ·) ++ (words (m + 1)).map (D :: ·) ++
      (words m).map (H :: ·)

/-- The Schröder paths from `(0,0)` to `(2n,0)`. -/
def schroderPaths (n : ℕ) : Finset (List Step) :=
  (words (2 * n)).toFinset.filter (IsSchroderPath n)

/-- A060693: `T(n, k)` is the number of Schröder paths from `(0,0)` to `(2n,0)` having `k`
peaks. -/
def T (n k : ℕ) : ℕ := ((schroderPaths n).filter (fun p => peaks p = k)).card

/-! ### Basic facts -/

@[simp] theorem width_nil : width [] = 0 := rfl

@[simp] theorem width_cons (s : Step) (p : List Step) : width (s :: p) = s.dx + width p := by
  simp [width]

@[simp] theorem height_nil : height [] = 0 := rfl

@[simp] theorem height_cons (s : Step) (p : List Step) : height (s :: p) = s.dy + height p := by
  simp [height]

theorem width_eq_zero {p : List Step} : width p = 0 ↔ p = [] := by
  cases p with
  | nil => simp
  | cons s p => cases s <;> simp [Step.dx]

theorem mem_words : ∀ (p : List Step) (m : ℕ), p ∈ words m ↔ width p = m
  | [], 0 => by simp [words]
  | [], 1 => by simp [words]
  | [], m + 2 => by simp [words]
  | s :: p, 0 => by cases s <;> simp [words, Step.dx]
  | s :: p, 1 => by
    cases s <;> simp [words, Step.dx, width_eq_zero]
    omega
  | s :: p, m + 2 => by
    have h1 := mem_words p (m + 1)
    have h0 := mem_words p m
    cases s <;> simp [words, Step.dx, h1, h0] <;> omega

theorem nodup_words : ∀ m, (words m).Nodup ∧ (words (m + 1)).Nodup
  | 0 => by simp [words]
  | m + 1 => by
    obtain ⟨h0, h1⟩ := nodup_words m
    refine ⟨h1, ?_⟩
    show ((words (m + 1)).map (U :: ·) ++ (words (m + 1)).map (D :: ·) ++
      (words m).map (H :: ·)).Nodup
    have hinj : ∀ s : Step, Function.Injective (s :: · : List Step → List Step) :=
      fun s _ _ h => List.cons_injective h
    rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨h1.map (hinj U), h1.map (hinj D), ?_⟩, h0.map (hinj H), ?_⟩
    · simp
    · simp only [List.mem_append, List.mem_map]
      rintro a (⟨a1, -, rfl⟩ | ⟨a1, -, rfl⟩) b ⟨a2, -, rfl⟩ h <;> simp at h

theorem mem_schroderPaths (n : ℕ) (p : List Step) : p ∈ schroderPaths n ↔ IsSchroderPath n p := by
  simp only [schroderPaths, Finset.mem_filter, List.mem_toFinset, mem_words]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- `T n k` is the number of Schröder paths from `(0,0)` to `(2n,0)` with exactly `k` peaks. -/
theorem T_eq_ncard (n k : ℕ) :
    T n k = {p : List Step | IsSchroderPath n p ∧ peaks p = k}.ncard := by
  rw [T, ← Set.ncard_coe_finset]
  congr 1
  ext p
  simp [mem_schroderPaths]

/-! ### A dynamic program for `T` -/

/-- Walking along `p` from height `h`, the path never goes below the axis and ends on it. -/
def valid : ℕ → List Step → Bool
  | h, [] => h == 0
  | h, U :: p => valid (h + 1) p
  | 0, D :: _ => false
  | h + 1, D :: p => valid h p
  | h, H :: p => valid h p

/-- The number of peaks of `p`, where an initial `D` also counts as a peak if `b = true` (the step
before `p` was a `U`). -/
def peaksFrom : Bool → List Step → ℕ
  | _, [] => 0
  | _, U :: p => peaksFrom true p
  | b, D :: p => (if b then 1 else 0) + peaksFrom false p
  | _, H :: p => peaksFrom false p

theorem valid_iff : ∀ (p : List Step) (h : ℕ),
    valid h p = true ↔ (h : ℤ) + height p = 0 ∧ ∀ q ∈ p.inits, 0 ≤ (h : ℤ) + height q
  | [], h => by simp [valid]
  | U :: p, h => by
    rw [valid, valid_iff p (h + 1)]
    simp only [List.inits_cons, List.mem_cons, List.mem_map, forall_eq_or_imp, height_nil,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, height_cons, Step.dy]
    push_cast
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, by omega, fun q hq => by have := h2 q hq; omega⟩
    · rintro ⟨h1, -, h2⟩
      exact ⟨by omega, fun q hq => by have := h2 q hq; omega⟩
  | D :: p, 0 => by
    simp only [valid, Bool.false_eq_true, false_iff, not_and]
    intro _ h2
    have := h2 [D] (by simp)
    simp [Step.dy] at this
  | D :: p, h + 1 => by
    rw [valid, valid_iff p h]
    simp only [List.inits_cons, List.mem_cons, List.mem_map, forall_eq_or_imp, height_nil,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, height_cons, Step.dy]
    push_cast
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, by omega, fun q hq => by have := h2 q hq; omega⟩
    · rintro ⟨h1, -, h2⟩
      exact ⟨by omega, fun q hq => by have := h2 q hq; omega⟩
  | H :: p, h => by
    rw [valid, valid_iff p h]
    simp only [List.inits_cons, List.mem_cons, List.mem_map, forall_eq_or_imp, height_nil,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, height_cons, Step.dy]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, by omega, fun q hq => by have := h2 q hq; omega⟩
    · rintro ⟨h1, -, h2⟩
      exact ⟨by omega, fun q hq => by have := h2 q hq; omega⟩

theorem peaks_cons (s : Step) (p : List Step) :
    peaks (s :: p) = (if s = U ∧ p.head? = some D then 1 else 0) + peaks p := by
  cases p with
  | nil => simp [peaks]
  | cons t p =>
    simp only [peaks, List.tail_cons, List.zip_cons_cons, List.count_cons, List.head?_cons,
      Option.some.injEq, beq_iff_eq, Prod.mk.injEq]
    omega

theorem peaksFrom_eq : ∀ (b : Bool) (p : List Step),
    peaksFrom b p = (if b = true ∧ p.head? = some D then 1 else 0) + peaks p
  | _, [] => by simp [peaksFrom, peaks]
  | b, U :: p => by
    rw [peaksFrom, peaksFrom_eq true p, peaks_cons]
    simp
  | b, D :: p => by
    rw [peaksFrom, peaksFrom_eq false p, peaks_cons]
    cases b <;> simp
  | b, H :: p => by
    rw [peaksFrom, peaksFrom_eq false p, peaks_cons]
    simp

theorem peaks_eq_peaksFrom (p : List Step) : peaks p = peaksFrom false p := by
  simp [peaksFrom_eq]

theorem valid_le : ∀ (p : List Step) (h : ℕ), valid h p = true → h ≤ width p
  | [], h => by simp [valid]
  | U :: p, h => by
    intro hv
    have := valid_le p (h + 1) hv
    simp [Step.dx]; omega
  | D :: p, 0 => by simp [valid]
  | D :: p, h + 1 => by
    intro hv
    have := valid_le p h hv
    simp [Step.dx]; omega
  | H :: p, h => by
    intro hv
    have := valid_le p h hv
    simp [Step.dx]; omega

theorem peaksFrom_le : ∀ (b : Bool) (p : List Step), peaksFrom b p ≤ width p
  | _, [] => by simp [peaksFrom]
  | _, U :: p => by
    have := peaksFrom_le true p
    simp [peaksFrom, Step.dx]; omega
  | b, D :: p => by
    have := peaksFrom_le false p
    simp only [peaksFrom, width_cons, Step.dx]
    split <;> omega
  | _, H :: p => by
    have := peaksFrom_le false p
    simp [peaksFrom, Step.dx]; omega

/-- The number of words of width `m` that, started at height `h`, stay weakly above the axis,
end on it, and have `k` peaks (an initial `D` counting as a peak when `b = true`). -/
def cnt (m h : ℕ) (b : Bool) (k : ℕ) : ℕ :=
  (words m).countP (fun w => valid h w && peaksFrom b w == k)

/-- The contribution of an initial `D` step to the recursion for `cnt`. -/
def dTerm (f : ℕ → Bool → ℕ → ℕ) : ℕ → Bool → ℕ → ℕ
  | 0, _, _ => 0
  | h + 1, false, k => f h false k
  | _ + 1, true, 0 => 0
  | h + 1, true, k + 1 => f h false k

/-- One step of the recursion: the first step is `U`, `D` or `H`. -/
def step (f1 f0 : ℕ → Bool → ℕ → ℕ) (h : ℕ) (b : Bool) (k : ℕ) : ℕ :=
  f1 (h + 1) true k + dTerm f1 h b k + f0 h false k

theorem cnt_step (m h : ℕ) (b : Bool) (k : ℕ) :
    cnt (m + 2) h b k = step (cnt (m + 1)) (cnt m) h b k := by
  rw [cnt, words, List.countP_append, List.countP_append, List.countP_map, List.countP_map,
    List.countP_map, step]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · simp [cnt, valid, peaksFrom, Function.comp_def]
  · rcases h with _ | h
    · simp [valid, dTerm, Function.comp_def]
    · rcases b with _ | _
      · simp [cnt, valid, peaksFrom, dTerm, Function.comp_def]
      · rcases k with _ | k
        · simp [valid, peaksFrom, dTerm, Function.comp_def]
        · simp only [cnt, valid, peaksFrom, dTerm, if_true, Function.comp_def]
          congr 1
          funext w
          congr 1
          rw [Bool.eq_iff_iff]
          simp only [beq_iff_eq]
          omega
  · simp [cnt, valid, peaksFrom, Function.comp_def]

theorem cnt_eq_zero (m h : ℕ) (b : Bool) (k : ℕ) (hm : m < h ∨ m < k) : cnt m h b k = 0 := by
  rw [cnt, List.countP_eq_zero]
  intro w hw
  rw [mem_words] at hw
  have h1 := valid_le w h
  have h2 := peaksFrom_le b w
  simp only [Bool.and_eq_true, beq_iff_eq, not_and]
  intro hv hk
  have := h1 hv
  omega

/-- A table: entry `h` holds the coefficient lists (indexed by `k`) for `b = false` and
`b = true`. -/
abbrev Tab := List (List ℕ × List ℕ)

/-- Look up the entry `(h, b, k)` of a table (`0` outside the table). -/
def look (t : Tab) (h : ℕ) (b : Bool) (k : ℕ) : ℕ :=
  (if b then (t.getD h ([], [])).2 else (t.getD h ([], [])).1).getD k 0

/-- The next table, of size `N × N`, computed from the previous two by `step`. -/
def next (N : ℕ) (t0 t1 : Tab) : Tab :=
  (List.range N).map fun h =>
    ((List.range N).map fun k => step (look t1) (look t0) h false k,
     (List.range N).map fun k => step (look t1) (look t0) h true k)

theorem look_next (N : ℕ) (t0 t1 : Tab) (h : ℕ) (b : Bool) (k : ℕ) :
    look (next N t0 t1) h b k = if h < N ∧ k < N then step (look t1) (look t0) h b k else 0 := by
  simp only [look, next, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hh : h < N
  · rw [List.getElem?_range hh]
    by_cases hk : k < N
    · cases b <;> simp [hh, hk]
    · cases b <;> simp [hk]
  · cases b <;> simp [hh]

/-- The tables for widths `m` and `m + 1`. -/
def tabs : ℕ → Tab × Tab
  | 0 => ([([1], [1])], [([0, 0], [0, 0]), ([1, 0], [0, 1])])
  | m + 1 => ((tabs m).2, next (m + 3) (tabs m).1 (tabs m).2)

theorem tabs_spec : ∀ m : ℕ,
    look (tabs m).1 = cnt m ∧ look (tabs m).2 = cnt (m + 1)
  | 0 => by
    constructor
    · funext h b k
      rcases h with _ | _ | h <;> rcases k with _ | _ | k <;> cases b <;>
        simp [look, tabs, cnt, words, valid, peaksFrom]
    · funext h b k
      rcases h with _ | _ | h <;> rcases k with _ | _ | k <;> cases b <;>
        simp [look, tabs, cnt, words, valid, peaksFrom]
  | m + 1 => by
    obtain ⟨h0, h1⟩ := tabs_spec m
    refine ⟨h1, ?_⟩
    funext h b k
    show look (next (m + 3) (tabs m).1 (tabs m).2) h b k = cnt (m + 2) h b k
    rw [look_next, h0, h1, cnt_step]
    split_ifs with hk
    · rfl
    · rw [← cnt_step, cnt_eq_zero]
      omega

/-- Fast evaluation of `T n k` via the tables. -/
def Tfast (n k : ℕ) : ℕ := look (tabs (2 * n)).1 0 false k

theorem T_eq_cnt (n k : ℕ) : T n k = cnt (2 * n) 0 false k := by
  rw [T, schroderPaths, Finset.filter_filter, ← List.toFinset_eq (nodup_words _).1,
    Finset.card_def, Finset.filter_val, Multiset.filter_coe, Multiset.coe_card, cnt,
    List.countP_eq_length_filter]
  congr 1
  apply List.filter_congr
  intro w hw
  rw [mem_words] at hw
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, valid_iff, IsSchroderPath, hw,
    peaks_eq_peaksFrom]
  push_cast
  simp

theorem T_eq_Tfast (n k : ℕ) : T n k = Tfast n k := by
  rw [T_eq_cnt, Tfast, (tabs_spec _).1]

/-! ### Data -/

/-- The definition reproduces the listed rows `n = 0, …, 9` of the triangle (kernel-checked). -/
theorem T_data : (List.range 10).map (fun n => (List.range (n + 1)).map (T n)) =
    [[1],
     [1, 1],
     [2, 3, 1],
     [5, 10, 6, 1],
     [14, 35, 30, 10, 1],
     [42, 126, 140, 70, 15, 1],
     [132, 462, 630, 420, 140, 21, 1],
     [429, 1716, 2772, 2310, 1050, 252, 28, 1],
     [1430, 6435, 12012, 12012, 6930, 2310, 420, 36, 1],
     [4862, 24310, 51480, 60060, 42042, 18018, 4620, 660, 45, 1]] ∧
    T 10 0 = 16796 := by
  rw [funext₂ T_eq_Tfast]
  decide +kernel

/-- A060693 as a sequence (offset `0`): the triangle `T` read by rows. (Rows `0, …, i` contain at
least `i + 1` entries, so the `i`-th entry of the concatenation lies among them.) -/
def a (i : ℕ) : ℕ :=
  ((List.range (i + 1)).flatMap fun n => (List.range (n + 1)).map (T n)).getD i 0

/-- The definition reproduces all 56 terms listed in OEIS, `a 0, …, a 55` (kernel-checked). -/
theorem a_data : (List.range 56).map (fun i => a (i + 0)) =
    [1, 1, 1, 2, 3, 1, 5, 10, 6, 1, 14, 35, 30, 10, 1, 42, 126, 140, 70, 15, 1, 132, 462, 630,
      420, 140, 21, 1, 429, 1716, 2772, 2310, 1050, 252, 28, 1, 1430, 6435, 12012, 12012,
      6930, 2310, 420, 36, 1, 4862, 24310, 51480, 60060, 42042, 18018, 4620, 660, 45, 1,
      16796] := by
  unfold a
  rw [funext₂ T_eq_Tfast]
  decide +kernel

/-! ### The conjecture -/

/-- Conjecture (Werner Schulte, 2017): for every `n ≥ 0`,
`∑_{k=0}^{n} (-1)^k · T(n,k) · (n+1-k)^2 = 1 + n + n^2`. -/
def statement : Prop :=
  ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * (T n k : ℤ) * ((n : ℤ) + 1 - k) ^ 2 =
    1 + (n : ℤ) + (n : ℤ) ^ 2

/-- Sanity check of the transcription (not a proof): the identity holds for `n ≤ 12`. -/
theorem statement_check : ∀ n < 13, ∑ k ∈ Finset.range (n + 1),
    (-1 : ℤ) ^ k * (T n k : ℤ) * ((n : ℤ) + 1 - k) ^ 2 = 1 + (n : ℤ) + (n : ℤ) ^ 2 := by
  rw [funext₂ T_eq_Tfast]
  decide +kernel

end Math0.Statements.A060693
