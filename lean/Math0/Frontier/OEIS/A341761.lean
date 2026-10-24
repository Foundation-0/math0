/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A341761
import Math0.Audit

/-!
# The subword complexity polynomial `S(n, x)` has leading coefficient `n(n+1)/2`

We prove Shiyao Guo's conjecture from OEIS A341761: `S(n, x)`, the sum of the subword
complexities of all words of length `n` over an `x`-letter alphabet, is a polynomial in `x`
whose coefficient of `x^n` is `n(n+1)/2`.

**Patterns.** For a word `w : Fin n → α`, let `pat w i` be the first position carrying the same
letter as position `i`. Then `pat w i = pat w j ↔ w i = w j`, so `pat (pat w) = pat w`, and
`w = w ∘ pat w` with `w` injective on the letters of `pat w`. Since an injective relabelling of the
letters does not change the set of factors up to a bijection, `complexity w = complexity (pat w)`.

**Counting fibres.** For a pattern `p` (a fixed point `pat p = p`) with `k` fixed points
(first occurrences), the words `w : Fin n → Fin x` with `pat w = p` are in bijection with the
injections from the `k` first-occurrence positions into `Fin x`, so there are
`x(x-1)⋯(x-k+1)` of them. Hence
`S(n, x) = ∑_{p = pat p} complexity(p) · x.descFactorial (#fix p)`, which is the value at `x` of
the polynomial `P = ∑_{p = pat p} complexity(p) · descPochhammer ℚ (#fix p)`.

**Leading coefficient.** `descPochhammer ℚ k` is monic of degree `k ≤ n`; `k = n` only for the
identity pattern. Its word `0 1 ⋯ (n-1)` has pairwise distinct letters, so its `n(n+1)/2`
nonempty factors are pairwise distinct (by induction: the nonempty prefixes of `a :: l` start with
`a ∉ l` and are disjoint from the factors of `l`). So `P.coeff n = n(n+1)/2`.
-/

namespace Math0.Frontier.A341761
open Math0.Statements.A341761
open Polynomial Finset

/-- The canonical pattern of a word: each position is sent to the first position carrying the
same letter. -/
private def pat {n : ℕ} {α : Type*} [DecidableEq α] (w : Fin n → α) (i : Fin n) : Fin n :=
  (univ.filter fun j => w j = w i).min' ⟨i, by simp⟩

/-- Position `pat w i` carries the same letter as position `i`. -/
private lemma pat_spec {n : ℕ} {α : Type*} [DecidableEq α] (w : Fin n → α) (i : Fin n) :
    w (pat w i) = w i := by
  have := Finset.min'_mem (univ.filter fun j => w j = w i) ⟨i, by simp⟩
  exact (Finset.mem_filter.1 this).2

/-- `pat w` depends only on which positions of `w` carry equal letters. -/
private lemma pat_congr {n : ℕ} {α β : Type*} [DecidableEq α] [DecidableEq β]
    (w : Fin n → α) (v : Fin n → β) (h : ∀ i j, w i = w j ↔ v i = v j) : pat w = pat v := by
  funext i
  unfold pat
  congr 1
  ext j
  simp [h]

/-- Two positions have the same first occurrence iff they carry the same letter. -/
private lemma pat_eq_iff {n : ℕ} {α : Type*} [DecidableEq α] (w : Fin n → α) (i j : Fin n) :
    pat w i = pat w j ↔ w i = w j := by
  constructor
  · intro hij
    rw [← pat_spec w i, hij, pat_spec w j]
  · intro hij
    unfold pat
    congr 1
    ext k
    simp [hij]

/-- `pat` is idempotent. -/
private lemma pat_pat {n : ℕ} {α : Type*} [DecidableEq α] (w : Fin n → α) :
    pat (pat w) = pat w :=
  pat_congr _ _ (fun i j => pat_eq_iff w i j)

/-- The identity word is its own pattern. -/
private lemma pat_id (n : ℕ) : pat (id : Fin n → Fin n) = id := by
  funext i
  exact pat_spec id i

/-- Mapping by a function injective on a set `s` is injective on lists with letters in `s`. -/
private lemma map_injOn_lists {α β : Type*} (f : α → β) (s : Set α) (hf : Set.InjOn f s) :
    ∀ u v : List α, (∀ a ∈ u, a ∈ s) → (∀ a ∈ v, a ∈ s) → u.map f = v.map f → u = v
  | [], [], _, _, _ => rfl
  | [], b :: v, _, _, h => by simp at h
  | a :: u, [], _, _, h => by simp at h
  | a :: u, b :: v, hu, hv, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hf (hu a (by simp)) (hv b (by simp)) h.1,
      map_injOn_lists f s hf u v (fun c hc => hu c (by simp [hc]))
        (fun c hc => hv c (by simp [hc])) h.2]

/-- Relabelling the letters of a word injectively does not change its subword complexity. -/
private lemma complexity_map {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β)
    (l : List α) (hf : Set.InjOn f {a | a ∈ l}) : complexity (l.map f) = complexity l := by
  unfold complexity
  have : factors (l.map f) = (factors l).image (List.map f) := by
    ext u
    simp only [mem_factors, Finset.mem_image]
    constructor
    · rintro ⟨hu, hinf⟩
      obtain ⟨v, hv, rfl⟩ := List.infix_map_iff.1 hinf
      exact ⟨v, ⟨by simpa using hu, hv⟩, rfl⟩
    · rintro ⟨v, ⟨hv, hinf⟩, rfl⟩
      exact ⟨by simpa using hv, hinf.map f⟩
  rw [this, Finset.card_image_of_injOn]
  intro u hu v hv huv
  rw [Finset.mem_coe, mem_factors] at hu hv
  exact map_injOn_lists f _ hf u v (fun a ha => hu.2.subset ha) (fun a ha => hv.2.subset ha) huv

/-- A word has the same subword complexity as its pattern. -/
private lemma complexity_pat {n x : ℕ} (w : Fin n → Fin x) :
    complexity (List.ofFn w) = complexity (List.ofFn (pat w)) := by
  have h1 : List.ofFn w = (List.ofFn (pat w)).map w := by
    rw [List.map_ofFn]
    congr 1
    funext i
    exact (pat_spec w i).symm
  rw [h1, complexity_map]
  intro a ha b hb hab
  simp only [Set.mem_ofPred_eq, List.mem_ofFn] at ha hb
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  rw [pat_spec w i, pat_spec w j] at hab
  exact (pat_eq_iff w i j).2 hab

/-- For a pattern `p`, `p (p i) = p i`. -/
private lemma pat_idem_apply {n : ℕ} (p : Fin n → Fin n) (hp : pat p = p) (i : Fin n) :
    p (p i) = p i := by
  have := pat_spec p i
  rwa [hp] at this

/-- Words with pattern `p` correspond to injections of the first-occurrence positions of `p`
into the alphabet. -/
private def fiberEquiv {n x : ℕ} (p : Fin n → Fin n) (hp : pat p = p) :
    {w : Fin n → Fin x // pat w = p} ≃ ({i : Fin n // p i = i} ↪ Fin x) where
  toFun w := ⟨fun i => w.1 i.1, by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    apply Subtype.ext
    have := (pat_eq_iff w.1 i j).2 h
    rw [w.2] at this
    exact hi.symm.trans (this.trans hj)⟩
  invFun e := ⟨fun i => e ⟨p i, pat_idem_apply p hp i⟩, by
    calc pat (fun i => e ⟨p i, pat_idem_apply p hp i⟩) = pat p :=
          pat_congr _ _ (fun i j => by rw [e.injective.eq_iff, Subtype.mk.injEq])
      _ = p := hp⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    have := pat_spec w.1 i
    rw [w.2] at this
    exact this
  right_inv e := by
    refine Function.Embedding.ext fun ⟨i, hi⟩ => ?_
    show e ⟨p i, _⟩ = e ⟨i, hi⟩
    exact congrArg e (Subtype.ext hi)

/-- There are `x.descFactorial k` words over `Fin x` with pattern `p`, where `k` is the number
of first-occurrence positions of `p`. -/
private lemma card_fiber {n x : ℕ} (p : Fin n → Fin n) (hp : pat p = p) :
    (univ.filter fun w : Fin n → Fin x => pat w = p).card =
      x.descFactorial (univ.filter fun i => p i = i).card := by
  rw [← Fintype.card_subtype, Fintype.card_congr (fiberEquiv p hp), Fintype.card_embedding_eq,
    Fintype.card_fin, Fintype.card_subtype]

/-- `S(n, x)` as a sum over patterns of complexity times a falling factorial in `x`. -/
private lemma S_eq (n x : ℕ) : S n x = ∑ p : Fin n → Fin n,
    if pat p = p then complexity (List.ofFn p) * x.descFactorial (univ.filter fun i => p i = i).card
    else 0 := by
  unfold S
  rw [← Finset.sum_fiberwise (univ : Finset (Fin n → Fin x)) pat]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => complexity (List.ofFn p)) (fun w hw => by
    rw [complexity_pat w, (Finset.mem_filter.1 hw).2])]
  rw [Finset.sum_const, smul_eq_mul]
  split_ifs with hp
  · rw [card_fiber p hp, mul_comm]
  · have : (univ.filter fun w : Fin n → Fin x => pat w = p) = ∅ := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hw
      apply hp
      rw [← hw, pat_pat]
    rw [this, Finset.card_empty, zero_mul]

/-- `toFinset` of a mapped list is the image of the `toFinset`. -/
private lemma toFinset_map' {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β)
    (L : List α) : (L.map f).toFinset = L.toFinset.image f := by
  ext; simp

/-- A list of length `m` has `m + 1` distinct prefixes. -/
private lemma card_inits {α : Type*} [DecidableEq α] :
    ∀ l : List α, l.inits.toFinset.card = l.length + 1
  | [] => by simp
  | a :: l => by
    rw [List.inits_cons, List.toFinset_cons, toFinset_map', Finset.card_insert_of_notMem,
      Finset.card_image_of_injective _ List.cons_injective, card_inits l, List.length_cons]
    simp

/-- A list of length `m` has `m` distinct nonempty prefixes. -/
private lemma card_inits_tail {α : Type*} [DecidableEq α] :
    ∀ l : List α, l.inits.tail.toFinset.card = l.length
  | [] => by simp
  | a :: l => by
    rw [List.inits_cons, List.tail_cons, toFinset_map',
      Finset.card_image_of_injective _ List.cons_injective, card_inits l, List.length_cons]

/-- A word of length `m` with pairwise distinct letters has `m(m+1)/2` distinct nonempty
factors. -/
private lemma complexity_nodup {α : Type*} [DecidableEq α] :
    ∀ l : List α, l.Nodup → 2 * complexity l = l.length * (l.length + 1)
  | [], _ => by simp [complexity, factors]
  | a :: l, h => by
    have hfac : factors (a :: l) = (a :: l).inits.tail.toFinset ∪ factors l := by
      simp only [factors, List.tails_cons, List.flatMap_cons, List.toFinset_append]
    have hdisj : Disjoint (a :: l).inits.tail.toFinset (factors l) := by
      rw [Finset.disjoint_left]
      intro u hu hu'
      rw [List.mem_toFinset, mem_inits_tail] at hu
      rw [mem_factors] at hu'
      obtain ⟨hne, hpre⟩ := hu
      rcases u with _ | ⟨b, v⟩
      · exact hne rfl
      · obtain ⟨rfl, _⟩ := List.cons_prefix_cons.1 hpre
        exact (List.nodup_cons.1 h).1 (hu'.2.subset (List.mem_cons_self ..))
    have ih := complexity_nodup l (List.nodup_cons.1 h).2
    unfold complexity at ih ⊢
    rw [hfac, Finset.card_union_of_disjoint hdisj, card_inits_tail, mul_add, ih, List.length_cons]
    ring

/-- The number of first-occurrence positions (fixed points) of a pattern. -/
private def nfix {n : ℕ} (p : Fin n → Fin n) : ℕ := (univ.filter fun i => p i = i).card

/-- **Guo's conjecture (A341761).** For every `n`, `S(n, x)` is given by a polynomial in `x`
whose coefficient of `x^n` is `n(n+1)/2`. -/
theorem result : statement := by
  intro n
  refine ⟨∑ p : Fin n → Fin n, if pat p = p then
      C (complexity (List.ofFn p) : ℚ) * descPochhammer ℚ (nfix p) else 0, ?_, ?_⟩
  · intro x
    rw [S_eq, eval_finsetSum]
    push_cast
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs
    · rw [eval_mul, eval_C, descPochhammer_eval_eq_descFactorial]
      rfl
    · simp
  · rw [finsetSum_coeff, Finset.sum_eq_single (id : Fin n → Fin n)]
    · rw [if_pos (pat_id n), coeff_C_mul]
      have hk : nfix (id : Fin n → Fin n) = n := by simp [nfix]
      have h1 : (descPochhammer ℚ n).coeff n = 1 := by
        have := (monic_descPochhammer ℚ n).coeff_natDegree
        rwa [descPochhammer_natDegree] at this
      rw [hk, h1, mul_one]
      have h2 := complexity_nodup (List.ofFn (id : Fin n → Fin n))
        (List.nodup_ofFn.2 Function.injective_id)
      rw [List.length_ofFn] at h2
      have h3 : (2 : ℚ) * (complexity (List.ofFn (id : Fin n → Fin n)) : ℚ) = n * (n + 1) := by
        exact_mod_cast h2
      linarith
    · intro p _ hp
      split_ifs with hpp
      · rw [coeff_C_mul]
        obtain ⟨i, hi⟩ := Function.ne_iff.1 hp
        have hlt : nfix p < n := by
          have hss : (univ.filter fun j => p j = j) ⊂ univ :=
            Finset.filter_ssubset.2 ⟨i, Finset.mem_univ i, hi⟩
          have := Finset.card_lt_card hss
          simpa [nfix] using this
        rw [coeff_eq_zero_of_natDegree_lt (by rwa [descPochhammer_natDegree]), mul_zero]
      · simp
    · intro h
      exact absurd (Finset.mem_univ _) h

end Math0.Frontier.A341761

#math0_settles Math0.Frontier.A341761.result Math0.Statements.A341761.statement
