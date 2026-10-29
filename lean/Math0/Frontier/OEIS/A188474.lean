/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A188474
import Math0.Audit

/-!
# The row sums of the generalized Deutsch triangle A188474 are A137398

We prove Paul Barry's conjecture: for every `n`, `∑_{k=0}^{n} T(n,k) = A137398(n+2)`.

**A137398 as lattice walks.** Encode a subsequence `p` of `S = [0, …, 2m-1]` by its indicator
word `c ∈ {U, D}^{2m}` (`U` at the positions in `p`), a walk with steps `±1`; `|p| = m` means it
ends at height `0`. Writing `cp(y) = |p ∩ [0, y)|`, `cq(y) = |q ∩ [0, y)|` (so `cp + cq = y`)
and using `p(k) < y ↔ k < cp(y)`, the exchange of `p(i)` and `q(i)` keeps both lists increasing
iff `2i ≤ p(i), q(i) ≤ 2i+1`, iff `cp(2i) = i` and `cp(2i+2) = i+1`, i.e. iff the walk has a
*hump* `0 → ±1 → 0` at steps `2i, 2i+1`. So `A137398(m)` counts the walks of length `2m` from
`0` to `0`, starting with `U`, without humps. A transfer-matrix count over the absolute height
(`Y`) evaluates this as `g(2m-2, 2)`, where `g(L, a) = ∑_j 2^j FP(L-2j, a+2j)` and `FP(L, a)` is
the number of first-passage walks from height `a` to `0` of length `L`; both satisfy local
Pascal-type recursions, so no generating functions are needed.

**The row sums.** Swapping the two sums in `∑_k T(n,k)` and applying Vandermonde's identity
`∑_k C(N, n+1-k) C(N, k+1) = C(2N, n+2)` (for `N = n+2-j < n+2`) gives
`∑_k T(n,k) = ∑_{j≥1} 2^{j-1} (j/N) C(2N, N-j)`. The ballot formula
`(a+2d) FP(a+2d, a) = a C(a+2d, d)` identifies `(j/N) C(2N, N-j) = FP(2N, 2j)`, which is the
`j`-th term of `g(2n+2, 2)`.
-/

namespace Math0.Frontier.A188474
open Math0.Statements.A188474

/-- All Boolean lists of length `n`. -/
private def allLists : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allLists n).map (List.cons true) ++ (allLists n).map (List.cons false)

/-- Every list in `allLists n` has length `n`. -/
private lemma length_of_mem_allLists : ∀ {n : ℕ} {c : List Bool}, c ∈ allLists n → c.length = n
  | 0, c, h => by simp [allLists] at h; simp [h]
  | n + 1, c, h => by
    simp only [allLists, List.mem_append, List.mem_map] at h
    rcases h with ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩ <;> simp [length_of_mem_allLists hd]

/-- `decode a c` is the list of positions `a + x` with `c[x] = true`. -/
private def decode : ℕ → List Bool → List ℕ
  | _, [] => []
  | a, true :: c => a :: decode (a + 1) c
  | a, false :: c => decode (a + 1) c

/-- Counting over `allLists (n+1)` splits according to the first entry. -/
private lemma countP_allLists_succ (n : ℕ) (P : List Bool → Bool) :
    (allLists (n + 1)).countP P =
      (allLists n).countP (fun c => P (true :: c)) +
        (allLists n).countP (fun c => P (false :: c)) := by
  simp only [allLists, List.countP_append, List.countP_map]
  rfl

/-- Sublists of `[a, …, a+n-1]` of length `k` correspond to indicator words with `k` trues. -/
private lemma countP_sublistsLen : ∀ (n k a : ℕ) (P : List ℕ → Bool),
    ((List.range' a n).sublistsLen k).countP P =
      (allLists n).countP (fun c => decide (c.count true = k) && P (decode a c))
  | 0, 0, a, P => by simp [allLists, decode]
  | 0, k + 1, a, P => by simp [allLists]
  | n + 1, 0, a, P => by
    rw [countP_allLists_succ]
    have := countP_sublistsLen n 0 (a + 1) P
    simp only [List.sublistsLen_zero] at this ⊢
    rw [this]
    simp [decode]
  | n + 1, k + 1, a, P => by
    rw [countP_allLists_succ, List.range'_succ, List.sublistsLen_succ_cons, List.countP_append,
      List.countP_map, countP_sublistsLen n (k + 1) (a + 1) P,
      countP_sublistsLen n k (a + 1) (P ∘ List.cons a), Nat.add_comm]
    congr 1
    apply List.countP_congr
    intro c _
    simp [decode]

/-- The entries of `decode a c` lie in `[a, a + |c|)`. -/
private lemma mem_decode :
    ∀ {a : ℕ} {c : List Bool} {x : ℕ}, x ∈ decode a c → a ≤ x ∧ x < a + c.length
  | _, [], _, h => by simp [decode] at h
  | a, true :: c, x, h => by
    simp only [decode, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · have := mem_decode h; simp only [List.length_cons]; omega
  | a, false :: c, x, h => by
    simp only [decode] at h
    have := mem_decode h; simp only [List.length_cons]; omega

/-- `decode a c` is strictly increasing. -/
private lemma decode_pairwise : ∀ (a : ℕ) (c : List Bool), (decode a c).Pairwise (· < ·)
  | _, [] => by simp [decode]
  | a, true :: c => by
    simp only [decode, List.pairwise_cons]
    exact ⟨fun x hx => by have := mem_decode hx; omega, decode_pairwise (a + 1) c⟩
  | a, false :: c => by simpa [decode] using decode_pairwise (a + 1) c

/-- `decode a c` has one entry per `true` of `c`. -/
private lemma length_decode : ∀ (a : ℕ) (c : List Bool), (decode a c).length = c.count true
  | _, [] => by simp [decode]
  | a, true :: c => by simp [decode, length_decode (a + 1) c]
  | a, false :: c => by simp [decode, length_decode (a + 1) c]

/-- The complementary subsequence is decoded from the negated word. -/
private lemma filter_decode : ∀ (a : ℕ) (c : List Bool),
    (List.range' a c.length).filter (fun x => decide (x ∉ decode a c)) = decode a (c.map not)
  | _, [] => by simp [decode]
  | a, true :: c => by
    have ha : a ∉ decode (a + 1) c := fun h => by have := mem_decode h; omega
    have := filter_decode (a + 1) c
    simp only [List.length_cons, List.range'_succ, List.filter_cons, decode, List.map_cons,
      Bool.not_true, List.mem_cons, true_or, not_true_eq_false, decide_false]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← this]
    apply List.filter_congr
    intro x hx
    have := List.mem_range'_1.1 hx
    simp only [not_or, decide_eq_decide]
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨by omega, h⟩
  | a, false :: c => by
    have ha : a ∉ decode (a + 1) c := fun h => by have := mem_decode h; omega
    have := filter_decode (a + 1) c
    have e : decode a (false :: c) = decode (a + 1) c := rfl
    have e2 : decode a ((false :: c).map not) = a :: decode (a + 1) (c.map not) := rfl
    rw [e, e2, List.length_cons, List.range'_succ, List.filter_cons, ← this]
    simp [ha]

/-- The number of entries of `decode a c` below `a + y` is the number of trues among the
first `y` letters of `c`. -/
private lemma countP_decode : ∀ (a : ℕ) (c : List Bool) (y : ℕ),
    (decode a c).countP (fun x => decide (x < a + y)) = (c.take y).count true
  | _, [], _ => by simp [decode]
  | a, b :: c, 0 => by
    simp only [Nat.add_zero, List.take_zero, List.count_nil]
    rw [List.countP_eq_zero]
    intro x hx
    have := mem_decode hx
    simp only [decide_eq_true_eq, not_lt]
    omega
  | a, true :: c, y + 1 => by
    have := countP_decode (a + 1) c y
    simp only [decode, List.take_succ_cons, List.count_cons_self]
    rw [List.countP_cons, ← this]
    simp only [show a + 1 + y = a + (y + 1) by omega]
    simp
  | a, false :: c, y + 1 => by
    have := countP_decode (a + 1) c y
    simp only [decode, List.take_succ_cons, List.count_cons]
    rw [show a + (y + 1) = a + 1 + y by omega, this]
    simp

/-- In a strictly increasing list, `l[k] < y` iff `k` is below the number of entries `< y`. -/
private lemma getElem_lt_iff : ∀ (l : List ℕ), l.Pairwise (· < ·) → ∀ (k : ℕ) (hk : k < l.length)
    (y : ℕ), l[k] < y ↔ k < l.countP (fun x => decide (x < y))
  | [], _, k, hk, _ => by simp at hk
  | a :: l, hl, k, hk, y => by
    rw [List.pairwise_cons] at hl
    rw [List.countP_cons]
    by_cases hay : a < y
    · rcases k with _ | k
      · simp [hay]
      · have ih := getElem_lt_iff l hl.2 k (by simpa using hk) y
        simp [hay, ih]
    · have h0 : l.countP (fun x => decide (x < y)) = 0 := by
        rw [List.countP_eq_zero]; intro x hx; have := hl.1 x hx; simp; omega
      rcases k with _ | k
      · simp [hay, h0]
      · have hk' : k < l.length := by simpa using hk
        have : ¬ l[k] < y := by
          have := hl.1 _ (List.getElem_mem hk'); omega
        simp [hay, h0, this]

/-- Entries of a strictly increasing list compare like their indices. -/
private lemma getElem_lt_getElem_iff (l : List ℕ) (hl : l.Pairwise (· < ·)) (a b : ℕ)
    (ha : a < l.length) (hb : b < l.length) : l[a] < l[b] ↔ a < b := by
  rw [List.pairwise_iff_getElem] at hl
  constructor
  · intro h
    by_contra h'
    rcases Nat.lt_or_ge b a with h'' | h''
    · have := hl b a hb ha h''; omega
    · have : a = b := by omega
      subst this; omega
  · intro h; exact hl a b ha hb h

/-- When does changing one entry keep a strictly increasing list strictly increasing. -/
private lemma pairwise_set_iff (l : List ℕ) (hl : l.Pairwise (· < ·)) (i : ℕ) (hi : i < l.length)
    (x : ℕ) : (l.set i x).Pairwise (· < ·) ↔
      (∀ k (hk : k < l.length), k < i → l[k] < x) ∧
        (∀ k (hk : k < l.length), i < k → x < l[k]) := by
  rw [List.pairwise_iff_getElem] at hl ⊢
  simp only [List.length_set, List.getElem_set]
  constructor
  · intro h
    refine ⟨fun k hk hki => ?_, fun k hk hik => ?_⟩
    · have := h k i hk hi hki
      rwa [if_neg (by omega), if_pos rfl] at this
    · have := h i k hi hk hik
      rwa [if_pos rfl, if_neg (by omega)] at this
  · rintro ⟨h1, h2⟩ a b ha hb hab
    split_ifs with h3 h4 h4
    · omega
    · subst h3; exact h2 b hb hab
    · subst h4; exact h1 a ha hab
    · exact hl a b ha hb hab

/-- Negating a word swaps the counts of `true` and `false`. -/
private lemma count_map_not (c : List Bool) : (c.map not).count true = c.count false := by
  induction c with
  | nil => simp
  | cons b c ih => cases b <;> simp [ih]

/-- Two bounded naturals with the same initial segments below `m` are equal. -/
private lemma eq_of_forall_lt_iff {a b m : ℕ} (ha : a ≤ m) (hb : b ≤ m)
    (h : ∀ k < m, k < a ↔ k < b) : a = b := by
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · have := h a (by omega); omega
  · exact hab
  · have := h b (by omega); omega

/-- The exchange of `p(i)` and `q(i)` keeps both lists increasing exactly when the path has a
"hump" `0 → ±1 → 0` at positions `2i, 2i+1`. -/
private lemma swap_iff (m : ℕ) (c : List Bool) (hc : c.length = 2 * m) (hcnt : c.count true = m)
    (i : ℕ) (hi : i < m) :
    ((((decode 0 c).set i
        (((List.range (2 * m)).filter (· ∉ decode 0 c)).getD i 0)).Pairwise (· < ·) ∧
      (((List.range (2 * m)).filter (· ∉ decode 0 c)).set i ((decode 0 c).getD i 0)).Pairwise
        (· < ·))
    ↔ ((c.take (2 * i)).count true = i ∧ (c.take (2 * i + 2)).count true = i + 1)) := by
  set p := decode 0 c with hp
  set q := (List.range (2 * m)).filter (· ∉ p) with hq0
  have hq : q = decode 0 (c.map not) := by
    rw [hq0, List.range_eq_range', ← hc, hp]; exact filter_decode 0 c
  have hpP : p.Pairwise (· < ·) := decode_pairwise 0 c
  have hqP : q.Pairwise (· < ·) := hq ▸ decode_pairwise 0 _
  have hpl : p.length = m := by rw [hp, length_decode, hcnt]
  have hcf : c.count false = m := by
    have := List.count_true_add_count_false c; omega
  have hql : q.length = m := by rw [hq, length_decode, count_map_not, hcf]
  have hcp : ∀ y, p.countP (fun x => decide (x < y)) = (c.take y).count true := by
    intro y; have := countP_decode 0 c y; simpa using this
  have hcq : ∀ y, q.countP (fun x => decide (x < y)) = (c.take y).count false := by
    intro y; have := countP_decode 0 (c.map not) y
    rw [← hq] at this; simp only [Nat.zero_add] at this
    rw [this, ← List.map_take, count_map_not]
  have hsum : ∀ y ≤ 2 * m, (c.take y).count true + (c.take y).count false = y := by
    intro y hy; rw [List.count_true_add_count_false]; simp [hc]; omega
  have hcpm : ∀ y, (c.take y).count true ≤ m := by
    intro y; rw [← hcp, ← hpl]; exact List.countP_le_length
  have hcqm : ∀ y, (c.take y).count false ≤ m := by
    intro y; rw [← hcq, ← hql]; exact List.countP_le_length
  have hgp : ∀ k (hk : k < p.length) y, p[k] < y ↔ k < (c.take y).count true := by
    intro k hk y; rw [← hcp]; exact getElem_lt_iff p hpP k hk y
  have hgq : ∀ k (hk : k < q.length) y, q[k] < y ↔ k < (c.take y).count false := by
    intro k hk y; rw [← hcq]; exact getElem_lt_iff q hqP k hk y
  have hpi : i < p.length := by omega
  have hqi : i < q.length := by omega
  have hP2 : p[i] < 2 * m := by
    have := mem_decode (List.getElem_mem hpi); omega
  have hQ2 : q[i] < 2 * m := by
    have hmem : q[i] ∈ decode 0 (c.map not) := by rw [← hq]; exact List.getElem_mem hqi
    have := mem_decode hmem; simp at this; omega
  -- the ranks of `p[i]` and `q[i]`
  have rP : (c.take p[i]).count true = i := by
    apply eq_of_forall_lt_iff (hcpm _) (by omega)
    intro k hk
    rw [← hgp k (by omega), getElem_lt_getElem_iff p hpP k i (by omega) hpi]
  have rP1 : (c.take (p[i] + 1)).count true = i + 1 := by
    apply eq_of_forall_lt_iff (hcpm _) (by omega)
    intro k hk
    rw [← hgp k (by omega), Nat.lt_succ_iff, Nat.lt_succ_iff, ← not_lt, ← not_lt,
      getElem_lt_getElem_iff p hpP i k hpi (by omega)]
  have rQ : (c.take q[i]).count false = i := by
    apply eq_of_forall_lt_iff (hcqm _) (by omega)
    intro k hk
    rw [← hgq k (by omega), getElem_lt_getElem_iff q hqP k i (by omega) hqi]
  have rQ1 : (c.take (q[i] + 1)).count false = i + 1 := by
    apply eq_of_forall_lt_iff (hcqm _) (by omega)
    intro k hk
    rw [← hgq k (by omega), Nat.lt_succ_iff, Nat.lt_succ_iff, ← not_lt, ← not_lt,
      getElem_lt_getElem_iff q hqP i k hqi (by omega)]
  rw [pairwise_set_iff p hpP i hpi, pairwise_set_iff q hqP i hqi, List.getD_eq_getElem _ _ hqi,
    List.getD_eq_getElem _ _ hpi]
  have c1 : (∀ k (hk : k < p.length), k < i → p[k] < q[i]) ↔ i ≤ (c.take q[i]).count true := by
    constructor
    · intro h
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · omega
      · have := (hgp (i - 1) (by omega) q[i]).1 (h (i - 1) (by omega) (by omega)); omega
    · intro h k hk hki; exact (hgp k hk q[i]).2 (by omega)
  have c2 : (∀ k (hk : k < p.length), i < k → q[i] < p[k]) ↔
      (c.take (q[i] + 1)).count true ≤ i + 1 := by
    constructor
    · intro h
      by_contra hc
      have h1 := h (i + 1) (by have := hcpm (q[i] + 1); omega) (by omega)
      have h2 := (hgp (i + 1) (by have := hcpm (q[i] + 1); omega) (q[i] + 1)).2 (by omega)
      omega
    · intro h k hk hik
      by_contra hc
      have := (hgp k hk (q[i] + 1)).1 (by omega)
      omega
  have c3 : (∀ k (hk : k < q.length), k < i → q[k] < p[i]) ↔ i ≤ (c.take p[i]).count false := by
    constructor
    · intro h
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · omega
      · have := (hgq (i - 1) (by omega) p[i]).1 (h (i - 1) (by omega) (by omega)); omega
    · intro h k hk hki; exact (hgq k hk p[i]).2 (by omega)
  have c4 : (∀ k (hk : k < q.length), i < k → p[i] < q[k]) ↔
      (c.take (p[i] + 1)).count false ≤ i + 1 := by
    constructor
    · intro h
      by_contra hc
      have h1 := h (i + 1) (by have := hcqm (p[i] + 1); omega) (by omega)
      have h2 := (hgq (i + 1) (by have := hcqm (p[i] + 1); omega) (p[i] + 1)).2 (by omega)
      omega
    · intro h k hk hik
      by_contra hc
      have := (hgq k hk (p[i] + 1)).1 (by omega)
      omega
  rw [c1, c2, c3, c4]
  have s1 := hsum q[i] (by omega)
  have s2 := hsum (q[i] + 1) (by omega)
  have s3 := hsum p[i] (by omega)
  have s4 := hsum (p[i] + 1) (by omega)
  have s5 := hsum (2 * i) (by omega)
  have s6 := hsum (2 * i + 2) (by omega)
  have g1 := hgp i hpi (2 * i)
  have g2 := hgp i hpi (2 * i + 2)
  have g3 := hgq i hqi (2 * i)
  have g4 := hgq i hqi (2 * i + 2)
  omega

/-- The step of the walk: `+1` for `true`, `-1` for `false`. -/
private def stp (b : Bool) : ℤ := if b then 1 else -1

/-- `ok h f c`: the walk `c`, started at height `h` (with `f` recording that the height just
before was `0`), never makes a hump `0 → ±1 → 0` and ends at height `0`. -/
private def ok : ℤ → Bool → List Bool → Bool
  | h, _, [] => decide (h = 0)
  | h, f, b :: c => !(f && decide (h + stp b = 0)) && ok (h + stp b) (decide (h = 0)) c

/-- The height of the walk `c` after `x` steps. -/
private def H (c : List Bool) (x : ℕ) : ℤ := 2 * ((c.take x).count true : ℤ) - x

/-- The walk starts at height `0`. -/
private lemma H_zero (c : List Bool) : H c 0 = 0 := by simp [H]

/-- The height after `x+1` steps of `b :: c`. -/
private lemma H_cons_succ (b : Bool) (c : List Bool) (x : ℕ) :
    H (b :: c) (x + 1) = stp b + H c x := by
  cases b <;> simp [H, stp] <;> ring

/-- One step of the automaton `ok`. -/
private lemma ok_cons (h : ℤ) (f b : Bool) (c : List Bool) :
    ok h f (b :: c) = true ↔
      ¬ (f = true ∧ h + stp b = 0) ∧ ok (h + stp b) (decide (h = 0)) c = true := by
  cases f <;> simp [ok]

/-- What the automaton `ok` checks: final height `0`, no hump right at the start when `f`
holds, and no hump `0 → ±1 → 0` anywhere. -/
private lemma ok_iff : ∀ (c : List Bool) (h : ℤ) (f : Bool),
    ok h f c = true ↔ (h + H c c.length = 0 ∧ (f = true → 1 ≤ c.length → h + H c 1 ≠ 0) ∧
      ∀ x, x + 2 ≤ c.length → ¬ (h + H c x = 0 ∧ h + H c (x + 2) = 0))
  | [], h, f => by simp [ok, H]
  | b :: c, h, f => by
    rw [ok_cons, ok_iff c (h + stp b) (decide (h = 0))]
    simp only [List.length_cons, H_cons_succ, H_zero, decide_eq_true_eq]
    constructor
    · rintro ⟨hf, h1, h2, h3⟩
      refine ⟨by linarith, fun hf' _ => by intro h0; exact hf ⟨hf', by linarith⟩, ?_⟩
      intro x hx
      rcases x with _ | x
      · rintro ⟨h0, h0'⟩
        rw [H_zero] at h0
        exact h2 (by linarith) (by omega) (by simpa using (by linarith : h + stp b + H c 1 = 0))
      · rintro ⟨h0, h0'⟩
        rw [show x + 1 + 1 = x + 2 from rfl] at h0'
        rw [H_cons_succ] at h0
        exact h3 x (by omega) ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨fun ⟨hf, h0⟩ => h2 hf (by omega) (by linarith), by linarith, ?_, ?_⟩
      · intro h0 hc h0'
        have := h3 0 (by omega)
        rw [H_zero, Nat.zero_add] at this
        exact this ⟨by linarith, by linarith⟩
      · intro x hx ⟨h0, h0'⟩
        have := h3 (x + 1) (by omega)
        rw [show x + 1 + 1 = x + 2 from rfl, H_cons_succ] at this
        exact this ⟨by linarith, by linarith⟩

/-- The least element `0` is in `p` iff the walk starts with an up-step. -/
private lemma zero_mem_decode (c : List Bool) : 0 ∈ decode 0 c ↔ c.head? = some true := by
  rcases c with _ | ⟨_ | _, c⟩
  · simp [decode]
  · simp only [decode, List.head?_cons, Option.some.injEq, Bool.false_eq_true, iff_false]
    intro h; have := mem_decode h; omega
  · simp [decode]

/-- Humps can only start at even positions `2i`, where the height is `2 cp(2i) - 2i`. -/
private lemma hump_iff (M : ℕ) (c : List Bool) :
    (∀ x, x + 2 ≤ 2 * M → ¬ (0 + H c x = 0 ∧ 0 + H c (x + 2) = 0)) ↔
      ∀ i < M, ¬ ((c.take (2 * i)).count true = i ∧ (c.take (2 * i + 2)).count true = i + 1) := by
  simp only [H, zero_add]
  constructor
  · intro h i hi ⟨h1, h2⟩
    apply h (2 * i) (by omega)
    push_cast
    constructor <;> omega
  · intro h x hx ⟨h1, h2⟩
    have e : x = 2 * (c.take x).count true := by omega
    apply h ((c.take x).count true) (by omega)
    rw [← e]
    constructor <;> omega

/-- The definition of A137398 as a count of walks: `A137398 (m+1)` counts the walks of length
`2m+1` from height `1` (just after an up-step from `0`) to height `0` with no hump. -/
private lemma A137398_eq (m : ℕ) :
    A137398 (m + 1) = (allLists (2 * m + 1)).countP (ok 1 true) := by
  unfold A137398
  rw [show (List.range (2 * (m + 1))).sublistsLen (m + 1) =
      (List.range' 0 (2 * (m + 1))).sublistsLen (m + 1) by rw [List.range_eq_range'],
    countP_sublistsLen]
  have key : ∀ c ∈ allLists (2 * (m + 1)),
      (decide (c.count true = m + 1) && (fun p : List ℕ =>
        let q := (List.range (2 * (m + 1))).filter (· ∉ p)
        decide (0 ∈ p ∧ ∀ i < m + 1,
          ¬ ((p.set i (q.getD i 0)).Pairwise (· < ·) ∧ (q.set i (p.getD i 0)).Pairwise (· < ·))))
        (decode 0 c)) = true ↔
      (decide (c.head? = some true) && ok 0 false c) = true := by
    intro c hc
    have hl := length_of_mem_allLists hc
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [ok_iff, hl, zero_mem_decode]
    constructor
    · rintro ⟨hcnt, h0, hsw⟩
      refine ⟨h0, ?_, by simp, ?_⟩
      · simp only [H, zero_add, List.take_of_length_le (by omega : c.length ≤ 2 * (m + 1)), hcnt]
        push_cast; ring
      · rw [hump_iff]
        intro i hi
        rw [← swap_iff (m + 1) c hl hcnt i hi]
        exact hsw i hi
    · rintro ⟨h0, h1, -, h3⟩
      have hcnt : c.count true = m + 1 := by
        simp only [H, zero_add, List.take_of_length_le (by omega : c.length ≤ 2 * (m + 1))] at h1
        omega
      refine ⟨hcnt, h0, ?_⟩
      rw [hump_iff] at h3
      intro i hi
      rw [swap_iff (m + 1) c hl hcnt i hi]
      exact h3 i hi
  rw [List.countP_congr key, show 2 * (m + 1) = 2 * m + 1 + 1 by ring, countP_allLists_succ]
  simp [ok, stp]

/-- The number of hump-free walks of length `L` from absolute height `a` to `0`; the flag `f`
(relevant only at height `1`) forbids an immediate step down to `0`. -/
private def Y : ℕ → ℕ → Bool → ℕ
  | 0, a, _ => if a = 0 then 1 else 0
  | L + 1, 0, _ => 2 * Y L 1 true
  | L + 1, 1, f => Y L 2 false + (if f then 0 else Y L 0 false)
  | L + 1, a + 2, _ => Y L (a + 3) false + Y L (a + 1) false

/-- One step of the transfer-matrix count. -/
private lemma countP_ok_cons (L : ℕ) (h : ℤ) (f b : Bool) :
    (allLists L).countP (fun c => ok h f (b :: c)) =
      if f = true ∧ h + stp b = 0 then 0
      else (allLists L).countP (ok (h + stp b) (decide (h = 0))) := by
  split_ifs with hc
  · rw [List.countP_eq_zero]; intro c _; simp [ok, hc.1, hc.2]
  · apply List.countP_congr; intro c _
    have : (f && decide (h + stp b = 0)) = false := by
      cases f <;> simp_all
    simp [ok, this]

/-- The automaton count depends only on the absolute height, and equals `Y`. -/
private lemma countP_ok (L : ℕ) :
    ∀ (h : ℤ) (f : Bool), (allLists L).countP (ok h f) = Y L h.natAbs f := by
  induction L with
  | zero =>
    intro h f
    simp only [allLists, List.countP_cons, List.countP_nil, ok, Y, Int.natAbs_eq_zero]
    split_ifs <;> simp_all
  | succ L ih =>
    intro h f
    rw [countP_allLists_succ, countP_ok_cons, countP_ok_cons, ih, ih]
    simp only [stp, if_true, Bool.false_eq_true, if_false]
    obtain ⟨a, rfl | rfl⟩ := Int.eq_nat_or_neg h
    · rcases a with _ | _ | a
      · simp [Y]; ring
      · cases f <;> simp [Y]
      · have e1 : ((((a + 2 : ℕ) : ℤ) + 1)).natAbs = a + 3 := by omega
        have e2 : ((((a + 2 : ℕ) : ℤ) + -1)).natAbs = a + 1 := by omega
        have e3 : (((a + 2 : ℕ) : ℤ)).natAbs = a + 2 := by omega
        rw [e1, e2, e3]
        have n1 : ¬ ((a : ℤ) + 1 + 1 + 1 = 0) := by omega
        have n2 : ¬ ((a : ℤ) + 1 + 1 = 0) := by omega
        have n3 : ¬ ((a : ℤ) + 1 = 0) := by omega
        simp [Y, n1, n2, n3]
    · rcases a with _ | _ | a
      · simp [Y]; ring
      · cases f <;> simp [Y, add_comm]
      · have e1 : ((-((a + 2 : ℕ) : ℤ) + 1)).natAbs = a + 1 := by omega
        have e2 : ((-((a + 2 : ℕ) : ℤ) + -1)).natAbs = a + 3 := by omega
        have e3 : (-((a + 2 : ℕ) : ℤ)).natAbs = a + 2 := by omega
        rw [e1, e2, e3]
        rw [if_neg (show ¬ (f = true ∧ -((a + 2 : ℕ) : ℤ) + 1 = 0) from
            fun h => absurd h.2 (by omega)),
          if_neg (show ¬ (f = true ∧ -((a + 2 : ℕ) : ℤ) + -1 = 0) from
            fun h => absurd h.2 (by omega)),
          decide_eq_false (show ¬ (-((a + 2 : ℕ) : ℤ) = 0) by omega)]
        simp only [Y, add_comm]

/-- First-passage numbers: walks of length `L` from height `a` that reach `0` only at the end. -/
private def FP : ℕ → ℕ → ℕ
  | 0, a => if a = 0 then 1 else 0
  | _ + 1, 0 => 0
  | L + 1, a + 1 => FP L (a + 2) + FP L a

/-- `g L a = ∑_j 2^j FP (L - 2j) (a + 2j)`, defined by its recursion. -/
private def g : ℕ → ℕ → ℕ
  | 0, a => FP 0 a
  | 1, a => FP 1 a
  | L + 2, a => FP (L + 2) a + 2 * g L (a + 2)

/-- The Pascal-type recursion of `g` away from height `0`. -/
private lemma g_succ : ∀ L a, g (L + 1) (a + 1) = g L (a + 2) + g L a
  | 0, a => by simp [g, FP]
  | 1, a => by simp [g, FP]
  | L + 2, a => by
    rw [g, g_succ L (a + 2), g, g, FP]
    ring

/-- Without the flag, `Y` is given by `g`. -/
private lemma Y_eq_g (L : ℕ) : ∀ a, Y L a false = g L a := by
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro a
    rcases L with _ | L
    · simp [Y, g, FP]
    · rcases a with _ | _ | a
      · rcases L with _ | L
        · simp [Y, g, FP]
        · rw [Y, Y, ih L (by omega), g, FP]
          simp
      · rw [Y, ih L (by omega), ih L (by omega), g_succ]
        simp
      · rw [Y, ih L (by omega), ih L (by omega), g_succ]

/-- `g` as an explicit sum. -/
private lemma g_two_mul : ∀ (t a : ℕ),
    g (2 * t) a = ∑ i ∈ Finset.range (t + 1), 2 ^ i * FP (2 * t - 2 * i) (a + 2 * i)
  | 0, a => by simp [g]
  | t + 1, a => by
    rw [show 2 * (t + 1) = 2 * t + 2 by ring, g, g_two_mul t (a + 2),
      Finset.sum_range_succ' (fun i => 2 ^ i * FP (2 * t + 2 - 2 * i) (a + 2 * i)) (t + 1),
      Finset.mul_sum]
    simp only [pow_zero, one_mul, Nat.mul_zero, Nat.sub_zero, Nat.add_zero]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [show 2 * t + 2 - 2 * (i + 1) = 2 * t - 2 * i by omega,
      show a + 2 * (i + 1) = a + 2 + 2 * i by ring, pow_succ]
    ring

/-- A first passage from height `a` needs at least `a` steps. -/
private lemma FP_eq_zero : ∀ (L a : ℕ), L < a → FP L a = 0
  | 0, a, h => by simp [FP]; omega
  | L + 1, 0, h => by omega
  | L + 1, a + 1, h => by rw [FP, FP_eq_zero L (a + 2) (by omega), FP_eq_zero L a (by omega)]

/-- The only first passage of length `a` from height `a` goes straight down. -/
private lemma FP_self : ∀ a, FP a a = 1
  | 0 => by simp [FP]
  | a + 1 => by rw [FP, FP_eq_zero a (a + 2) (by omega), FP_self a]

/-- The ballot formula `(a + 2d) · FP (a + 2d) a = a · C(a + 2d, d)`. -/
private lemma FP_mul : ∀ (d a : ℕ), FP (a + 2 * d) a * (a + 2 * d) = a * (a + 2 * d).choose d
  | 0, a => by simp [FP_self]
  | d + 1, 0 => by
    rw [show 0 + 2 * (d + 1) = (2 * d + 1) + 1 by ring, FP]; simp
  | d + 1, a + 1 => by
    have hX := FP_mul d (a + 2)
    have hY := FP_mul (d + 1) a
    have hv := Nat.choose_succ_right_eq (a + 2 * d + 2) d
    have hp := Nat.choose_succ_succ' (a + 2 * d + 2) d
    rw [show a + 1 + 2 * (d + 1) = (a + 2 * d + 2) + 1 by ring, FP,
      show a + 2 * d + 2 = a + 2 + 2 * d by ring]
    rw [show a + 2 * d + 2 = a + 2 + 2 * d by ring] at hv hp
    rw [show a + 2 * (d + 1) = a + 2 + 2 * d by ring] at hY
    rw [show a + 2 + 2 * d - d = a + d + 2 by omega] at hv
    rw [hp]
    apply Nat.eq_of_mul_eq_mul_left (show 0 < a + 2 + 2 * d by omega)
    zify at hX hY hv ⊢
    linear_combination ((a : ℤ) + 2 + 2 * d + 1) * hX + ((a : ℤ) + 2 + 2 * d + 1) * hY - 2 * hv

/-- Vandermonde's identity in the form needed for the row sums. -/
private lemma vandermonde_aux (n N : ℕ) (hN : N < n + 2) :
    ∑ k ∈ Finset.range (n + 1), N.choose (n - k + 1) * N.choose (k + 1) =
      (2 * N).choose (n + 2) := by
  rw [two_mul, Nat.add_choose_eq,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun u v => N.choose u * N.choose v),
    Finset.sum_range_succ (fun u => N.choose u * N.choose (n + 2 - u)) (n + 2),
    Finset.sum_range_succ' (fun u => N.choose u * N.choose (n + 2 - u)) (n + 1)]
  simp only [Nat.choose_eq_zero_of_lt hN, zero_mul, mul_zero, add_zero, Nat.sub_zero]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [mul_comm, show n + 1 + 1 - (k + 1) = n - k + 1 by omega]

/-- The row sum after swapping the sums and applying Vandermonde's identity. -/
private lemma rowSum_eq (n : ℕ) : ∑ k ∈ Finset.range (n + 1), T n k =
    ∑ j ∈ Finset.range (n + 2), (j : ℚ) / ((n : ℚ) + 2 - j) * (2 : ℚ) ^ ((j : ℤ) - 1) *
      ((2 * (n + 2 - j)).choose (n + 2) : ℚ) := by
  have h1 : ∀ k ∈ Finset.range (n + 1), T n k = ∑ j ∈ Finset.range (n + 2),
      (j : ℚ) / ((n : ℚ) + 2 - j) * ((n + 2 - j).choose (n - k + 1) : ℚ) *
        ((n + 2 - j).choose (k + 1) : ℚ) * (2 : ℚ) ^ ((j : ℤ) - 1) := by
    intro k hk
    rw [Finset.mem_range] at hk
    unfold T
    apply Finset.sum_subset
    · intro j hj; simp only [Finset.mem_range] at hj ⊢; omega
    · intro j hj hj'
      simp only [Finset.mem_range, not_lt] at hj hj'
      rw [Nat.choose_eq_zero_of_lt (show n + 2 - j < k + 1 by omega)]
      simp
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  · rw [← vandermonde_aux n (n + 2 - j) (by omega), Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring

/-- `A137398 (n + 2)` as an explicit sum of first-passage numbers. -/
private lemma A137398_sum (n : ℕ) : A137398 (n + 2) =
    ∑ i ∈ Finset.range (n + 2), 2 ^ i * FP (2 * (n + 1) - 2 * i) (2 + 2 * i) := by
  rw [A137398_eq (n + 1), countP_ok, ← g_two_mul, ← Y_eq_g]
  simp [Y]

/-- The `i`-th terms agree. -/
private lemma term_eq (n i : ℕ) (hi : i < n + 2) :
    ((2 ^ i * FP (2 * (n + 1) - 2 * i) (2 + 2 * i) : ℕ) : ℚ) =
      ((i + 1 : ℕ) : ℚ) / ((n : ℚ) + 2 - ((i + 1 : ℕ) : ℚ)) *
        (2 : ℚ) ^ (((i + 1 : ℕ) : ℤ) - 1) * ((2 * (n + 2 - (i + 1))).choose (n + 2) : ℚ) := by
  have hz : (((i + 1 : ℕ) : ℤ) - 1) = (i : ℤ) := by push_cast; ring
  rw [hz, zpow_natCast]
  rcases Nat.lt_or_ge (n + 1 - i) (i + 1) with hlt | hge
  · -- the walk cannot reach `0`
    rw [FP_eq_zero _ _ (by omega), Nat.choose_eq_zero_of_lt (by omega)]
    simp
  · obtain ⟨d, hd⟩ : ∃ d, n + 1 - i = i + 1 + d := ⟨n + 1 - i - (i + 1), by omega⟩
    have hF := FP_mul d (2 + 2 * i)
    rw [show 2 + 2 * i + 2 * d = 2 * (n + 1) - 2 * i by omega] at hF
    have hc : (2 * (n + 2 - (i + 1))).choose (n + 2) = (2 * (n + 1) - 2 * i).choose d := by
      rw [show 2 * (n + 2 - (i + 1)) = 2 * (n + 1) - 2 * i by omega]
      exact Nat.choose_symm_of_eq_add (by omega)
    rw [hc]
    have hN : ((n : ℚ) + 2 - ((i + 1 : ℕ) : ℚ)) = ((n + 1 - i : ℕ) : ℚ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hN]
    have hF' : (FP (2 * (n + 1) - 2 * i) (2 + 2 * i) : ℚ) * (2 * ((n + 1 - i : ℕ) : ℚ)) =
        (2 + 2 * (i : ℚ)) * ((2 * (n + 1) - 2 * i).choose d : ℚ) := by
      have := congrArg (fun x : ℕ => (x : ℚ)) hF
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at this
      rw [← this, show 2 * (n + 1) - 2 * i = 2 * (n + 1 - i) by omega]
      push_cast; ring
    have hpos : ((n + 1 - i : ℕ) : ℚ) ≠ 0 := by
      have : 0 < n + 1 - i := by omega
      positivity
    field_simp
    push_cast
    linear_combination ((2 : ℚ) ^ i / 2) * hF'

/-- Paul Barry's conjecture: the row sums of A188474 are `A137398(n+2)`. -/
theorem result : statement := by
  intro n
  rw [rowSum_eq, A137398_sum, Nat.cast_sum,
    Finset.sum_range_succ
      (fun i => ((2 ^ i * FP (2 * (n + 1) - 2 * i) (2 + 2 * i) : ℕ) : ℚ)) (n + 1),
    Finset.sum_range_succ' _ (n + 1)]
  have hlast : FP (2 * (n + 1) - 2 * (n + 1)) (2 + 2 * (n + 1)) = 0 := FP_eq_zero _ _ (by omega)
  rw [hlast]
  simp only [mul_zero, add_zero, CharP.cast_eq_zero, zero_div, zero_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [term_eq n i (by simp only [Finset.mem_range] at hi; omega)]

end Math0.Frontier.A188474

#math0_settles Math0.Frontier.A188474.result Math0.Statements.A188474.statement
