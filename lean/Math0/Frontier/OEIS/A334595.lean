/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A334595
import Math0.Audit

/-!
# A334595: `a(n) = 1` iff `n` is a power of two, and records occur at `1` and `2^k + 1`

We prove both conjectures of Peter Kagey on the right diagonal of the XOR-triangle.

**Reversal.** XOR is commutative, so `xorRow` commutes with list reversal; hence the right
diagonal of the triangle of `binExp n = (digits 2 n).reverse` is the *head column*
`D c = [head c, head (xorRow c), head (xorRow² c), …]` of the least-significant-first digit list
`c = digits 2 n`, and `a n = ofDigits 2 (D c).reverse`.

**Involution.** `D (x :: r) = x :: D (xorRow (x :: r))` and, by induction on the length,
`xorRow (D c) = D c.tail` (the only algebra used is `x ^^^ (x ^^^ y) = y`). Consequently
`D (D c) = c` (Newton's forward-difference formula over `GF(2)`). Together with injectivity of
`ofDigits 2` on `0`/`1` lists of a fixed length, `a` is injective on numbers with `L` binary
digits, and `a n` is determined by solving `D c = d`, i.e. `c = D d`.

**Explicit values.** `D` fixes `(0,…,0,1)` (the digits of `2^k`), so `a(2^k) = 1`, and
`a n = 1` forces the digits of `n` to be `(0,…,0,1)`. `D (1,0,…,0,1) = (1,…,1,0)`, so
`a(2^(j+1)+1) = 2^(j+2) - 2`. `D (1,0,…,0) = (1,…,1)`, so `a n = 2^L - 1` forces `n = 1`.
Since `a n < 2^L` for an `L`-digit `n`, every `L`-digit `n ≥ 2` other than `2^(L-1)` and
`2^(L-1) + 1` has `a n ≤ 2^L - 2 = a(2^(L-1)+1)`, while `a(2^(L-1)) = 1 = a 1` and all shorter
`m` have `a m < 2^(L-1)`. This gives exactly the record positions `1, 3, 5, 9, 17, …`.
-/

namespace Math0.Frontier.A334595
open Math0.Statements.A334595

/-- The head column of a row: entry `r` is the head of the `r`-th iterated XOR-row. -/
private def D (c : List ℕ) : List ℕ :=
  (List.range c.length).map (fun r => (xorRow^[r] c).headD 0)

/-- `xorRow` of a one-entry row is empty. -/
private lemma xorRow_single (x : ℕ) : xorRow [x] = [] := rfl

/-- Unfolding `xorRow` on a row with at least two entries. -/
private lemma xorRow_cons_cons (x y : ℕ) (r : List ℕ) :
    xorRow (x :: y :: r) = (x ^^^ y) :: xorRow (y :: r) := rfl

/-- `xorRow` shortens a row by one. -/
private lemma length_xorRow (l : List ℕ) : (xorRow l).length = l.length - 1 := by
  simp [xorRow, List.length_zipWith]

/-- Entry `i` of `xorRow l` is `l[i] ^^^ l[i+1]`. -/
private lemma getElem_xorRow (l : List ℕ) (i : ℕ) (h : i < (xorRow l).length) :
    (xorRow l)[i] = l[i]'(by rw [length_xorRow] at h; omega) ^^^
      l[i + 1]'(by rw [length_xorRow] at h; omega) := by
  simp [xorRow, List.getElem_zipWith, List.getElem_tail]

/-- `xorRow` commutes with reversal (XOR is commutative). -/
private lemma xorRow_reverse (l : List ℕ) : xorRow l.reverse = (xorRow l).reverse := by
  apply List.ext_getElem
  · simp [length_xorRow]
  · intro i h1 h2
    rw [getElem_xorRow, List.getElem_reverse, List.getElem_reverse, List.getElem_reverse,
      getElem_xorRow]
    simp only [length_xorRow, List.length_reverse] at h1 h2 ⊢
    rw [Nat.xor_comm]
    congr 2 <;> omega

/-- Iterated `xorRow` commutes with reversal. -/
private lemma iterate_xorRow_reverse (l : List ℕ) (r : ℕ) :
    xorRow^[r] l.reverse = (xorRow^[r] l).reverse := by
  induction r with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      xorRow_reverse]

/-- The right diagonal of the triangle of `c.reverse` is the head column `D c` of `c`. -/
private lemma rightDiag_reverse (c : List ℕ) : rightDiag c.reverse = D c := by
  simp only [rightDiag, triangle, D, List.length_reverse, List.map_map]
  congr 1
  funext r
  simp [iterate_xorRow_reverse]

/-- `a n` read through the least-significant-first digit list of `n`. -/
private lemma a_eq (n : ℕ) : a n = Nat.ofDigits 2 (D (Nat.digits 2 n)).reverse := by
  rw [a, binExp, rightDiag_reverse]

/-- `D` preserves length. -/
private lemma length_D (c : List ℕ) : (D c).length = c.length := by
  simp [D]

/-- `D [] = []`. -/
private lemma D_nil : D [] = [] := rfl

/-- Recursion for `D`: the head column of `x :: r` is `x` followed by the head column of the
next row. -/
private lemma D_cons (x : ℕ) (r : List ℕ) : D (x :: r) = x :: D (xorRow (x :: r)) := by
  unfold D
  rw [length_xorRow, List.length_cons, Nat.add_sub_cancel, List.range_succ_eq_map,
    List.map_cons, List.map_map]
  congr 1

/-- `xorRow` commutes with `tail`. -/
private lemma tail_xorRow (l : List ℕ) : (xorRow l).tail = xorRow l.tail := by
  match l with
  | [] => rfl
  | [_] => rfl
  | x :: y :: r => rfl

/-- Key identity `xorRow (D c) = D c.tail`, by induction on the length of `c`. -/
private lemma xorRow_D_aux (n : ℕ) :
    ∀ c : List ℕ, c.length = n → xorRow (D c) = D c.tail := by
  induction n with
  | zero =>
    intro c hc
    rw [List.length_eq_zero_iff.mp hc]
    rfl
  | succ n ih =>
    intro c hc
    match c, hc with
    | [x], _ =>
      rw [D_cons, xorRow_single, D_nil, xorRow_single]
      rfl
    | x :: y :: r, hc =>
      have h1 : D (x :: y :: r) = x :: D (xorRow (x :: y :: r)) := D_cons x (y :: r)
      have h2 : D (xorRow (x :: y :: r)) =
          (x ^^^ y) :: D (xorRow (xorRow (x :: y :: r))) := by
        rw [xorRow_cons_cons x y r, D_cons]
      have h3 : xorRow (D (xorRow (x :: y :: r))) = D (xorRow (y :: r)) := by
        rw [ih _ (by rw [length_xorRow]; simp only [List.length_cons] at hc ⊢; omega),
          tail_xorRow]
        rfl
      rw [h1, h2, xorRow_cons_cons x (x ^^^ y) (D (xorRow (xorRow (x :: y :: r)))), ← h2, h3,
        ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, List.tail_cons, D_cons y r]

/-- Key identity: the XOR-row of the head column of `c` is the head column of `c.tail`. -/
private lemma xorRow_D (c : List ℕ) : xorRow (D c) = D c.tail :=
  xorRow_D_aux c.length c rfl

/-- `D` is an involution, by induction on the length. -/
private lemma D_D_aux (n : ℕ) : ∀ c : List ℕ, c.length = n → D (D c) = c := by
  induction n with
  | zero =>
    intro c hc
    rw [List.length_eq_zero_iff.mp hc]
    rfl
  | succ n ih =>
    intro c hc
    match c, hc with
    | x :: r, hc =>
      calc D (D (x :: r)) = D (x :: D (xorRow (x :: r))) := by rw [D_cons x r]
        _ = x :: D (xorRow (x :: D (xorRow (x :: r)))) := D_cons _ _
        _ = x :: D (xorRow (D (x :: r))) := by rw [D_cons x r]
        _ = x :: D (D r) := by rw [xorRow_D]; rfl
        _ = x :: r := by rw [ih r (by simpa using hc)]

/-- `D` is an involution (Newton's forward-difference formula over `GF(2)`). -/
private lemma D_D (c : List ℕ) : D (D c) = c :=
  D_D_aux c.length c rfl

/-- `xorRow` keeps a `0`/`1` row a `0`/`1` row. -/
private lemma xorRow_lt_two (l : List ℕ) (h : ∀ x ∈ l, x < 2) :
    ∀ x ∈ xorRow l, x < 2 := by
  intro z hz
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
  rw [getElem_xorRow]
  have hi' : i + 1 < l.length := by rw [length_xorRow] at hi; omega
  have h1 := h _ (List.getElem_mem (show i < l.length by omega))
  have h2 := h _ (List.getElem_mem hi')
  have := Nat.xor_lt_two_pow (n := 1) (by simpa using h1) (by simpa using h2)
  simpa using this

/-- Iterated `xorRow` keeps a `0`/`1` row a `0`/`1` row. -/
private lemma iterate_xorRow_lt_two (l : List ℕ) (h : ∀ x ∈ l, x < 2) (r : ℕ) :
    ∀ x ∈ xorRow^[r] l, x < 2 := by
  induction r with
  | zero => exact h
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact xorRow_lt_two _ ih

/-- The head column of a `0`/`1` row is a `0`/`1` row. -/
private lemma D_lt_two (c : List ℕ) (h : ∀ x ∈ c, x < 2) : ∀ x ∈ D c, x < 2 := by
  intro z hz
  simp only [D, List.mem_map, List.mem_range] at hz
  obtain ⟨r, _, rfl⟩ := hz
  have := iterate_xorRow_lt_two c h r
  cases hl : xorRow^[r] c with
  | nil => simp
  | cons y t =>
    rw [hl] at this
    simpa using this y (by simp)

/-- `xorRow (0,…,0,1) = (0,…,0,1)` with one zero fewer. -/
private lemma xorRow_e (k : ℕ) :
    xorRow (List.replicate (k + 1) 0 ++ [1]) = List.replicate k 0 ++ [1] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ih' : xorRow (0 :: (List.replicate k 0 ++ [1])) = List.replicate k 0 ++ [1] := ih
    show xorRow (0 :: 0 :: (List.replicate k 0 ++ [1])) = 0 :: (List.replicate k 0 ++ [1])
    rw [xorRow_cons_cons, ih', Nat.xor_self]

/-- `D` fixes `e_k = (0,…,0,1)` (`k` zeros), the digits of `2^k`. -/
private lemma D_e (k : ℕ) : D (List.replicate k 0 ++ [1]) = List.replicate k 0 ++ [1] := by
  induction k with
  | zero =>
    show D [1] = [1]
    rw [D_cons, xorRow_single, D_nil]
  | succ k ih =>
    show D (0 :: (List.replicate k 0 ++ [1])) = 0 :: (List.replicate k 0 ++ [1])
    rw [D_cons]
    have h : xorRow (0 :: (List.replicate k 0 ++ [1])) = List.replicate k 0 ++ [1] := xorRow_e k
    rw [h, ih]

/-- `xorRow` of a constant row is a zero row. -/
private lemma xorRow_rep (m x : ℕ) : xorRow (List.replicate (m + 1) x) = List.replicate m 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show xorRow (x :: x :: List.replicate m x) = 0 :: List.replicate m 0
    rw [xorRow_cons_cons, Nat.xor_self]
    exact congrArg (0 :: ·) ih

/-- `D` fixes zero rows. -/
private lemma D_rep0 (m : ℕ) : D (List.replicate m 0) = List.replicate m 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show D (0 :: List.replicate m 0) = 0 :: List.replicate m 0
    rw [D_cons]
    have h : xorRow (0 :: List.replicate m 0) = List.replicate m 0 := xorRow_rep m 0
    rw [h, ih]

/-- `D (1,…,1) = (1,0,…,0)`. -/
private lemma D_rep1 (m : ℕ) : D (List.replicate (m + 1) 1) = 1 :: List.replicate m 0 := by
  show D (1 :: List.replicate m 1) = 1 :: List.replicate m 0
  rw [D_cons]
  have h : xorRow (1 :: List.replicate m 1) = List.replicate m 0 := xorRow_rep m 1
  rw [h, D_rep0]

/-- `xorRow (1,0,…,0,1) = (1,0,…,0,1)` with one zero fewer. -/
private lemma xorRow_f (j : ℕ) :
    xorRow (1 :: (List.replicate (j + 1) 0 ++ [1])) = 1 :: (List.replicate j 0 ++ [1]) := by
  show xorRow (1 :: 0 :: (List.replicate j 0 ++ [1])) = 1 :: (List.replicate j 0 ++ [1])
  rw [xorRow_cons_cons]
  have h : xorRow (0 :: (List.replicate j 0 ++ [1])) = List.replicate j 0 ++ [1] := xorRow_e j
  rw [h]
  rfl

/-- `D (1,0,…,0,1) = (1,…,1,0)`; here `(1,0,…,0,1)` (`j` zeros) is the digit list of
`2^(j+1)+1`. -/
private lemma D_f (j : ℕ) :
    D (1 :: (List.replicate j 0 ++ [1])) = List.replicate (j + 1) 1 ++ [0] := by
  induction j with
  | zero =>
    show D [1, 1] = [1, 0]
    rw [D_cons, xorRow_cons_cons, xorRow_single, Nat.xor_self, D_cons, xorRow_single, D_nil]
  | succ j ih =>
    rw [D_cons, xorRow_f, ih]
    rfl

/-- The value of `e_k` is `2^k`. -/
private lemma ofDigits_e (k : ℕ) : Nat.ofDigits 2 (List.replicate k 0 ++ [1]) = 2 ^ k := by
  simp [Nat.ofDigits_append, Nat.ofDigits_replicate_zero, Nat.ofDigits_singleton]

/-- The value of `e_k` reversed is `1`. -/
private lemma ofDigits_e_rev (k : ℕ) :
    Nat.ofDigits 2 (List.replicate k 0 ++ [1]).reverse = 1 := by
  simp [List.reverse_append, List.reverse_replicate, Nat.ofDigits_cons,
    Nat.ofDigits_replicate_zero]

/-- `ofDigits 2 (1,…,1) + 1 = 2^m` (`m` ones). -/
private lemma ofDigits_rep1 (m : ℕ) : Nat.ofDigits 2 (List.replicate m 1) + 1 = 2 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons, pow_succ]
    omega

/-- `e_k` is a `0`/`1` row. -/
private lemma e_lt (k : ℕ) : ∀ x ∈ List.replicate k 0 ++ [1], x < 2 := by
  intro x hx
  simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hx
  omega

/-- `(1,0,…,0,1)` is a `0`/`1` row. -/
private lemma f_lt (j : ℕ) : ∀ x ∈ 1 :: (List.replicate j 0 ++ [1]), x < 2 := by
  intro x hx
  simp at hx
  omega

/-- `a` of the number with (least-significant-first) binary digits `l`. -/
private lemma a_ofDigits (l : List ℕ) (hl : ∀ x ∈ l, x < 2)
    (hlast : ∀ h : l ≠ [], l.getLast h ≠ 0) :
    a (Nat.ofDigits 2 l) = Nat.ofDigits 2 (D l).reverse := by
  rw [a_eq, Nat.digits_ofDigits 2 (by norm_num) l hl hlast]

/-- `a n < 2^L` where `L` is the number of binary digits of `n`. -/
private lemma a_lt (n : ℕ) : a n < 2 ^ (Nat.digits 2 n).length := by
  have hc : ∀ x ∈ Nat.digits 2 n, x < 2 := fun x hx => Nat.digits_lt_base (by norm_num) hx
  rw [a_eq]
  have := Nat.ofDigits_lt_base_pow_length (b := 2) (by norm_num)
    (l := (D (Nat.digits 2 n)).reverse) (fun x hx => D_lt_two _ hc x (List.mem_reverse.mp hx))
  simpa [length_D] using this

/-- Injectivity: if `a n` equals the value attached to a `0`/`1` row `l` of the same length as
the digits of `n`, then `l` is the digit list of `n`. -/
private lemma eq_ofDigits_of_a_eq (n : ℕ) (l : List ℕ) (hl : ∀ x ∈ l, x < 2)
    (hlen : l.length = (Nat.digits 2 n).length) (h : a n = Nat.ofDigits 2 (D l).reverse) :
    n = Nat.ofDigits 2 l := by
  have hc : ∀ x ∈ Nat.digits 2 n, x < 2 := fun x hx => Nat.digits_lt_base (by norm_num) hx
  rw [a_eq] at h
  have h1 := Nat.ofDigits_inj_of_len_eq (b := 2) (by norm_num)
    (by simp [length_D, hlen]) (fun x hx => D_lt_two _ hc x (List.mem_reverse.mp hx))
    (fun x hx => D_lt_two _ hl x (List.mem_reverse.mp hx)) h
  rw [List.reverse_inj] at h1
  have h2 : Nat.digits 2 n = l := by rw [← D_D (Nat.digits 2 n), h1, D_D]
  rw [← h2, Nat.ofDigits_digits]

/-- `a (2^k) = 1`. -/
private lemma a_two_pow (k : ℕ) : a (2 ^ k) = 1 := by
  rw [← ofDigits_e k, a_ofDigits _ (e_lt k) (by simp), D_e, ofDigits_e_rev]

/-- `a (2^(j+1)+1) = 2^(j+2) - 2`. -/
private lemma a_two_pow_add_one (j : ℕ) : a (2 ^ (j + 1) + 1) + 2 = 2 ^ (j + 2) := by
  have h1 : Nat.ofDigits 2 (1 :: (List.replicate j 0 ++ [1])) = 2 ^ (j + 1) + 1 := by
    rw [Nat.ofDigits_cons, ofDigits_e, pow_succ]
    ring
  rw [← h1, a_ofDigits _ (f_lt j) (by simp), D_f, List.reverse_append, List.reverse_replicate]
  simp only [List.reverse_singleton, List.singleton_append, Nat.ofDigits_cons]
  have := ofDigits_rep1 (j + 1)
  rw [pow_succ 2 (j + 1)]
  omega

/-- For `n ≥ 2` with `L` binary digits, `a n ≠ 2^L - 1`. -/
private lemma a_ne_all_ones (n : ℕ) (hn : 2 ≤ n) : a n + 1 ≠ 2 ^ (Nat.digits 2 n).length := by
  intro h
  obtain ⟨m, hm⟩ : ∃ m, (Nat.digits 2 n).length = m + 1 := ⟨(Nat.digits 2 n).length - 1, by
    have := (Nat.lt_digits_length_iff (b := 2) (k := 0) (by norm_num) n).mpr (by simp; omega)
    omega⟩
  rw [hm] at h
  have hD : D (1 :: List.replicate m 0) = List.replicate (m + 1) 1 := by
    rw [← D_rep1, D_D]
  have h' := eq_ofDigits_of_a_eq n (1 :: List.replicate m 0)
    (by
      intro x hx
      simp only [List.mem_cons, List.mem_replicate] at hx
      omega)
    (by simp [hm])
    (by
      rw [hD, List.reverse_replicate]
      have := ofDigits_rep1 (m + 1)
      omega)
  rw [Nat.ofDigits_cons, Nat.ofDigits_replicate_zero] at h'
  omega

/-- If `a n = 1` (`n ≥ 1`) then `n` is a power of two. -/
private lemma pow_of_a_eq_one (n : ℕ) (hn : 1 ≤ n) (h : a n = 1) : ∃ k, n = 2 ^ k := by
  obtain ⟨k, hk⟩ : ∃ k, (Nat.digits 2 n).length = k + 1 := ⟨(Nat.digits 2 n).length - 1, by
    have := (Nat.lt_digits_length_iff (b := 2) (k := 0) (by norm_num) n).mpr (by simpa using hn)
    omega⟩
  refine ⟨k, ?_⟩
  rw [eq_ofDigits_of_a_eq n (List.replicate k 0 ++ [1]) (e_lt k) (by simp [hk])
    (by rw [D_e, ofDigits_e_rev, h]), ofDigits_e]

/-- The record conjecture. -/
private lemma records : statement_records := by
  have ha1 : a 1 = 1 := by simpa using a_two_pow 0
  intro n
  constructor
  · rintro ⟨hn1, hrec⟩
    by_cases h1 : n = 1
    · exact Or.inl h1
    right
    have hn2 : 2 ≤ n := by omega
    have hL : 1 < (Nat.digits 2 n).length :=
      (Nat.lt_digits_length_iff (by norm_num) n).mpr (by simpa using hn2)
    obtain ⟨j, hj⟩ : ∃ j, (Nat.digits 2 n).length = j + 2 :=
      ⟨(Nat.digits 2 n).length - 2, by omega⟩
    have hlow : 2 ^ (j + 1) ≤ n := (Nat.lt_digits_length_iff (by norm_num) n).mp (by omega)
    refine ⟨j + 1, by omega, ?_⟩
    rcases Nat.lt_trichotomy n (2 ^ (j + 1) + 1) with hlt | heq | hgt
    · have hn' : n = 2 ^ (j + 1) := by omega
      have := hrec 1 le_rfl (by omega)
      rw [hn', a_two_pow, ha1] at this
      exact absurd this (lt_irrefl _)
    · exact heq
    · have h1 := hrec (2 ^ (j + 1) + 1) (Nat.le_add_left _ _) hgt
      have h2 := a_two_pow_add_one j
      have h3 := a_lt n
      have h4 := a_ne_all_ones n hn2
      rw [hj] at h3 h4
      omega
  · rintro (rfl | ⟨k, hk, rfl⟩)
    · exact ⟨le_rfl, fun m hm1 hm2 => absurd hm2 (by omega)⟩
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      refine ⟨Nat.le_add_left _ _, fun m hm1 hm2 => ?_⟩
      have h2 := a_two_pow_add_one j
      have hp : 2 ^ (j + 2) = 2 * 2 ^ (j + 1) := by ring
      have hp2 : 2 ≤ 2 ^ (j + 1) := by
        have := Nat.two_pow_pos j
        rw [pow_succ]
        omega
      rcases Nat.lt_or_ge m (2 ^ (j + 1)) with hlt | hge
      · have hlen : (Nat.digits 2 m).length ≤ j + 1 :=
          (Nat.digits_length_le_iff (by norm_num) m).mpr hlt
        have h3 := a_lt m
        have h4 : 2 ^ (Nat.digits 2 m).length ≤ 2 ^ (j + 1) :=
          Nat.pow_le_pow_right (by norm_num) hlen
        omega
      · have hm : m = 2 ^ (j + 1) := by omega
        rw [hm, a_two_pow]
        omega

/-- Both conjectures of A334595 hold. -/
theorem result : statement :=
  ⟨records, fun n hn => ⟨pow_of_a_eq_one n hn, fun ⟨k, hk⟩ => hk ▸ a_two_pow k⟩⟩

end Math0.Frontier.A334595

#math0_settles Math0.Frontier.A334595.result Math0.Statements.A334595.statement
