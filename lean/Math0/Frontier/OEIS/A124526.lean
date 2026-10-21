/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A124526
import Math0.Audit

/-!
# Hanna's conjecture A124418(n,k) = k! · A124526(n,k) (mixed-parity blocks)

We prove Paul D. Hanna's conjecture (2006): the number of set partitions of `{1, …, n}` with
exactly `k` blocks containing both an odd and an even entry equals
`k! · A049020(⌊n/2⌋, k) · A049020(⌈n/2⌉, k)`, where `A049020(m,k) = ∑ᵢ S2(m,i) C(i,k)`.

**Refined count.** Fix a predicate `c` on `ℕ` and a finset `s` with `o` elements satisfying `c`
and `e` elements satisfying `¬ c`. For a partition `P` of `s` let `nC P`, `nN P`, `nM P` be the
numbers of parts meeting `c`, meeting `¬ c`, and meeting both. We show that the number
`cnt s i j k` of partitions with `(nC, nN, nM) = (i, j, k)` is
`F(o,e,i,j,k) = S2(o,i) · S2(e,j) · C(i,k) · C(j,k) · k!`.

**Induction by insertion.** Every partition of `insert a s` (`a ∉ s`) arises in exactly one
way from a partition `P` of `s`, either by adding the singleton `{a}` or by adding `a` to a part
`b` of `P` (`ins`, proved bijective using `recP`, which deletes `a`). If `c a`, the singleton
raises `nC` by one; adding `a` to a part meeting `c` changes nothing (`nC P` choices); adding
`a` to a part not meeting `c` raises `nC` and `nM` by one (`nN P - nM P` choices). This gives
`cnt(insert a s; i+1, j, k+1) = cnt(s; i, j, k+1) + (i+1) cnt(s; i+1, j, k+1)
  + (j-k) cnt(s; i, j, k)` (and the degenerate cases), which `F` satisfies by
`S2(o+1,i+1) = (i+1) S2(o,i+1) + S2(o,i)`, Pascal's rule and `C(j,k+1)(k+1) = C(j,k)(j-k)`.
The case `¬ c a` follows by exchanging `c` and `¬ c`.

**Specialisation.** Take `c = Odd`, `s = {1, …, n}` (so `o = ⌈n/2⌉`, `e = ⌊n/2⌋`) and sum over
`i, j ≤ n`: the double sum factors as `k! · A049020(⌈n/2⌉,k) · A049020(⌊n/2⌋,k)`.
-/

namespace Math0.Frontier.A124526
open Math0.Statements.A124526 Finset

/-! ### Inserting a new element into a partition -/

section Insert

variable {a : ℕ} {t : Finset ℕ}

/-- Parts of the partition obtained by inserting `a` into `P`: as a new singleton (`none`), or
into an existing part `b` (`some b`). -/
private def insP (a : ℕ) (P : Finpartition t) : Option P.parts → Finset (Finset ℕ)
  | none => insert {a} P.parts
  | some b => insert (insert a b.1) (P.parts.erase b.1)

/-- An element outside `t` lies in no part of a partition of `t`. -/
private lemma notMem_part (ha : a ∉ t) (P : Finpartition t) {p : Finset ℕ} (hp : p ∈ P.parts) :
    a ∉ p := fun h => ha (P.subset hp h)

/-- Inserting `a ∉ t` into a partition of `t`, as a new singleton part or into an existing
part. -/
private def ins (ha : a ∉ t) (P : Finpartition t) (x : Option P.parts) :
    Finpartition (insert a t) :=
  Finpartition.ofExistsUnique (insP a P x)
    (by
      intro p hp
      cases x with
      | none =>
        simp only [insP, mem_insert] at hp
        rcases hp with rfl | hp
        · simp
        · exact (P.subset hp).trans (subset_insert _ _)
      | some b =>
        simp only [insP, mem_insert, mem_erase] at hp
        rcases hp with rfl | ⟨-, hp⟩
        · exact insert_subset_insert _ (P.subset b.2)
        · exact (P.subset hp).trans (subset_insert _ _))
    (by
      intro y hy
      rw [mem_insert] at hy
      cases x with
      | none =>
        rcases hy with hy | hy
        · refine ⟨{a}, ⟨by simp [insP], by simp [hy]⟩, ?_⟩
          rintro p ⟨hp, hyp⟩
          simp only [insP, mem_insert] at hp
          rcases hp with rfl | hp
          · rfl
          · exact absurd (hy ▸ hyp) (notMem_part ha P hp)
        · refine ⟨P.part y, ⟨by simp [insP, hy], P.mem_part hy⟩, ?_⟩
          rintro p ⟨hp, hyp⟩
          simp only [insP, mem_insert] at hp
          rcases hp with rfl | hp
          · simp only [mem_singleton] at hyp; subst hyp; exact absurd hy ha
          · exact (P.part_eq_of_mem hp hyp).symm
      | some b =>
        rcases hy with hy | hy
        · refine ⟨insert a b.1, ⟨by simp [insP], by simp [hy]⟩, ?_⟩
          rintro p ⟨hp, hyp⟩
          simp only [insP, mem_insert, mem_erase] at hp
          rcases hp with rfl | ⟨-, hp⟩
          · rfl
          · exact absurd (hy ▸ hyp) (notMem_part ha P hp)
        · by_cases hyb : y ∈ b.1
          · refine ⟨insert a b.1, ⟨by simp [insP], mem_insert_of_mem hyb⟩, ?_⟩
            rintro p ⟨hp, hyp⟩
            simp only [insP, mem_insert, mem_erase] at hp
            rcases hp with rfl | ⟨hpb, hp⟩
            · rfl
            · exact absurd (P.eq_of_mem_parts hp b.2 hyp hyb) hpb
          · have hq : P.part y ≠ b.1 := fun h => hyb (h ▸ P.mem_part hy)
            refine ⟨P.part y, ⟨by simp [insP, hy, hq], P.mem_part hy⟩, ?_⟩
            rintro p ⟨hp, hyp⟩
            simp only [insP, mem_insert, mem_erase] at hp
            rcases hp with rfl | ⟨-, hp⟩
            · rcases mem_insert.1 hyp with rfl | h
              · exact absurd hy ha
              · exact absurd h hyb
            · exact (P.part_eq_of_mem hp hyp).symm)
    (by
      cases x with
      | none =>
        simp only [insP, mem_insert, not_or]
        exact ⟨fun h => by simpa using congrArg (a ∈ ·) h.symm, P.empty_notMem_parts⟩
      | some b =>
        simp only [insP, mem_insert, mem_erase, not_or, not_and]
        exact ⟨fun h => by simpa using congrArg (a ∈ ·) h.symm,
          fun _ => P.empty_notMem_parts⟩)

/-- The parts of `ins ha P x`. -/
private lemma ins_parts (ha : a ∉ t) (P : Finpartition t) (x : Option P.parts) :
    (ins ha P x).parts = insP a P x := rfl

/-- The parts of `P` can be recovered from those of `ins ha P x`: delete `a` from every part and
discard the empty set. -/
private lemma rec_insP (ha : a ∉ t) (P : Finpartition t) (x : Option P.parts) :
    ((insP a P x).image (·.erase a)).erase ∅ = P.parts := by
  have himg : ∀ S ⊆ P.parts, S.image (·.erase a) = S := fun S hS => by
    ext p
    simp only [mem_image]
    constructor
    · rintro ⟨q, hq, rfl⟩
      rwa [erase_eq_of_notMem (notMem_part ha P (hS hq))]
    · intro hp
      exact ⟨p, hp, erase_eq_of_notMem (notMem_part ha P (hS hp))⟩
  cases x with
  | none =>
    rw [insP, image_insert, himg _ subset_rfl, erase_singleton, erase_insert_eq_erase,
      erase_eq_of_notMem P.empty_notMem_parts]
  | some b =>
    rw [insP, image_insert, himg _ (erase_subset _ _), erase_insert (notMem_part ha P b.2),
      insert_erase b.2]
    exact erase_eq_of_notMem P.empty_notMem_parts

/-- Inserting as a new singleton never gives the same parts as inserting into an old part. -/
private lemma insP_none_ne_some (ha : a ∉ t) (P : Finpartition t) (b : P.parts) :
    insP a P none ≠ insP a P (some b) := by
  intro h
  have h1 : ({a} : Finset ℕ) ∈ insP a P (some b) := by rw [← h]; simp [insP]
  simp only [insP, mem_insert, mem_erase] at h1
  rcases h1 with h1 | ⟨-, h1⟩
  · obtain ⟨y, hy⟩ := P.nonempty_of_mem_parts b.2
    have hy' : y ∈ ({a} : Finset ℕ) := h1 ▸ mem_insert_of_mem hy
    rw [mem_singleton] at hy'
    subst hy'
    exact notMem_part ha P b.2 hy
  · exact notMem_part ha P h1 (mem_singleton_self a)

/-- Insertion is injective on pairs (partition of `t`, choice). -/
private lemma ins_injective (ha : a ∉ t) :
    Function.Injective fun σ : (Σ P : Finpartition t, Option P.parts) => ins ha σ.1 σ.2 := by
  rintro ⟨P, x⟩ ⟨P', x'⟩ h
  have hparts : insP a P x = insP a P' x' := congrArg Finpartition.parts h
  have hPP : P = P' := Finpartition.ext (by rw [← rec_insP ha P x, hparts, rec_insP ha P' x'])
  subst hPP
  cases x with
  | none =>
    cases x' with
    | none => rfl
    | some b' => exact absurd hparts (insP_none_ne_some ha P b')
  | some b =>
    cases x' with
    | none => exact absurd hparts.symm (insP_none_ne_some ha P b)
    | some b' =>
      have h1 : insert a b.1 ∈ insP a P (some b') := by rw [← hparts]; simp [insP]
      simp only [insP, mem_insert, mem_erase] at h1
      rcases h1 with h1 | ⟨-, h1⟩
      · have h2 := congrArg (·.erase a) h1
        simp only [erase_insert (notMem_part ha P b.2),
          erase_insert (notMem_part ha P b'.2)] at h2
        obtain rfl : b = b' := Subtype.ext h2
        rfl
      · exact absurd (mem_insert_self a b.1) (notMem_part ha P h1)

/-- Deleting `a` from a partition of `insert a t`. -/
private def recP (ha : a ∉ t) (R : Finpartition (insert a t)) : Finpartition t :=
  Finpartition.ofExistsUnique ((R.parts.image (·.erase a)).erase ∅)
    (by
      intro p hp
      simp only [mem_erase, mem_image] at hp
      obtain ⟨-, q, hq, rfl⟩ := hp
      intro y hy
      rw [mem_erase] at hy
      exact (mem_insert.1 (R.subset hq hy.2)).resolve_left hy.1)
    (by
      intro y hy
      have hy' : y ∈ insert a t := mem_insert_of_mem hy
      have hya : y ≠ a := fun h => ha (h ▸ hy)
      have hmem : y ∈ (R.part y).erase a := mem_erase.2 ⟨hya, R.mem_part hy'⟩
      refine ⟨(R.part y).erase a, ⟨?_, hmem⟩, ?_⟩
      · simp only [mem_erase, mem_image]
        exact ⟨ne_empty_of_mem hmem, _, R.part_mem.2 hy', rfl⟩
      · rintro p ⟨hp, hyp⟩
        simp only [mem_erase, mem_image] at hp
        obtain ⟨-, q, hq, rfl⟩ := hp
        rw [R.part_eq_of_mem hq (mem_of_mem_erase hyp)])
    (by simp)

/-- The parts of `recP ha R`. -/
private lemma recP_parts (ha : a ∉ t) (R : Finpartition (insert a t)) :
    (recP ha R).parts = (R.parts.image (·.erase a)).erase ∅ := rfl

/-- Every partition of `insert a t` arises by insertion. -/
private lemma ins_surjective (ha : a ∉ t) :
    Function.Surjective fun σ : (Σ P : Finpartition t, Option P.parts) => ins ha σ.1 σ.2 := by
  intro R
  have haR : a ∈ insert a t := mem_insert_self a t
  have hBR : R.part a ∈ R.parts := R.part_mem.2 haR
  have haB : a ∈ R.part a := R.mem_part haR
  by_cases hBa : R.part a = {a}
  · refine ⟨⟨recP ha R, none⟩, ?_⟩
    apply Finpartition.ext
    show insP a (recP ha R) none = R.parts
    ext p
    simp only [insP, recP_parts, mem_insert, mem_erase, mem_image]
    constructor
    · rintro (rfl | ⟨hp0, q, hq, rfl⟩)
      · rw [← hBa]; exact hBR
      · by_cases haq : a ∈ q
        · have hqB := R.eq_of_mem_parts hq hBR haq haB
          rw [hqB, hBa] at hp0
          simp at hp0
        · rwa [erase_eq_of_notMem haq]
    · intro hp
      by_cases hap : a ∈ p
      · left; rw [← hBa]; exact R.eq_of_mem_parts hp hBR hap haB
      · right; exact ⟨R.ne_empty hp, p, hp, erase_eq_of_notMem hap⟩
  · have hb0 : (R.part a).erase a ≠ ∅ := by
      rw [Ne, erase_eq_empty_iff, not_or]
      exact ⟨ne_empty_of_mem haB, hBa⟩
    have hb : (R.part a).erase a ∈ (recP ha R).parts := by
      rw [recP_parts, mem_erase, mem_image]
      exact ⟨hb0, _, hBR, rfl⟩
    refine ⟨⟨recP ha R, some ⟨_, hb⟩⟩, ?_⟩
    apply Finpartition.ext
    show insP a (recP ha R) (some ⟨_, hb⟩) = R.parts
    ext p
    simp only [insP, recP_parts, insert_erase haB, mem_insert, mem_erase, mem_image]
    constructor
    · rintro (rfl | ⟨hpb, hp0, q, hq, rfl⟩)
      · exact hBR
      · by_cases haq : a ∈ q
        · exact (hpb (by rw [R.eq_of_mem_parts hq hBR haq haB])).elim
        · rwa [erase_eq_of_notMem haq]
    · intro hp
      by_cases hap : a ∈ p
      · left; exact R.eq_of_mem_parts hp hBR hap haB
      · right
        refine ⟨?_, R.ne_empty hp, p, hp, erase_eq_of_notMem hap⟩
        intro hpe
        obtain ⟨y, hy⟩ := nonempty_iff_ne_empty.2 hb0
        have hyp : y ∈ p := by rw [hpe]; exact hy
        have hpB := R.eq_of_mem_parts hp hBR hyp (mem_of_mem_erase hy)
        rw [hpB] at hap
        exact hap haB

/-- Counting partitions of `insert a t` via insertion. -/
private lemma card_filter_ins (ha : a ∉ t) (f : Finpartition (insert a t) → Prop)
    [DecidablePred f] :
    #(univ.filter f) =
      ∑ P : Finpartition t, #(univ.filter fun x : Option P.parts => f (ins ha P x)) := by
  rw [← card_sigma]
  symm
  refine card_bij (fun σ _ => ins ha σ.1 σ.2) ?_ ?_ ?_
  · intro σ hσ
    simp only [mem_sigma, mem_filter, mem_univ, true_and] at hσ
    simpa using hσ
  · intro σ₁ _ σ₂ _ h
    exact ins_injective ha h
  · intro R hR
    obtain ⟨σ, hσ⟩ := ins_surjective ha R
    refine ⟨σ, ?_, hσ⟩
    simp only [mem_sigma, mem_filter, mem_univ, true_and]
    simp only at hσ
    rw [hσ]
    simpa using hR

/-- Filtered cardinality of the parts after inserting as a singleton. -/
private lemma card_filter_insP_none (ha : a ∉ t) (P : Finpartition t) (p : Finset ℕ → Prop)
    [DecidablePred p] :
    #((insP a P none).filter p) = #(P.parts.filter p) + if p {a} then 1 else 0 := by
  have hn : ({a} : Finset ℕ) ∉ P.parts := fun h => notMem_part ha P h (mem_singleton_self a)
  rw [insP, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (fun h' => hn (mem_filter.1 h').1)]
  · rw [add_zero]

/-- Filtered cardinality of the parts after inserting into the part `b`. -/
private lemma card_filter_insP_some (ha : a ∉ t) (P : Finpartition t) (b : P.parts)
    (p : Finset ℕ → Prop) [DecidablePred p] :
    #((insP a P (some b)).filter p) + (if p b.1 then 1 else 0) =
      #(P.parts.filter p) + if p (insert a b.1) then 1 else 0 := by
  have hn : insert a b.1 ∉ (P.parts.filter p).erase b.1 := fun h =>
    notMem_part ha P (mem_filter.1 (mem_of_mem_erase h)).1 (mem_insert_self a b.1)
  rw [insP, filter_insert, filter_erase]
  by_cases h1 : p b.1 <;> by_cases h2 : p (insert a b.1)
  · rw [if_pos h1, if_pos h2, if_pos h2, card_insert_of_notMem hn,
      card_erase_add_one (mem_filter.2 ⟨b.2, h1⟩)]
  · rw [if_pos h1, if_neg h2, if_neg h2, card_erase_add_one (mem_filter.2 ⟨b.2, h1⟩), add_zero]
  · have hb : b.1 ∉ P.parts.filter p := fun h => h1 (mem_filter.1 h).2
    rw [if_neg h1, if_pos h2, if_pos h2, erase_eq_of_notMem hb,
      card_insert_of_notMem (by rwa [erase_eq_of_notMem hb] at hn)]
  · have hb : b.1 ∉ P.parts.filter p := fun h => h1 (mem_filter.1 h).2
    rw [if_neg h1, if_neg h2, if_neg h2, erase_eq_of_notMem hb]

/-- If `p` does not distinguish `b` from `insert a b`, the filtered count is unchanged. -/
private lemma card_filter_insP_some_eq (ha : a ∉ t) (P : Finpartition t) (b : P.parts)
    (p : Finset ℕ → Prop) [DecidablePred p] (h : p (insert a b.1) ↔ p b.1) :
    #((insP a P (some b)).filter p) = #(P.parts.filter p) := by
  have := card_filter_insP_some ha P b p
  by_cases hb : p b.1
  · rw [if_pos hb, if_pos (h.2 hb)] at this; omega
  · rw [if_neg hb, if_neg (mt h.1 hb)] at this; omega

/-- If `p` holds for `insert a b` but not for `b`, the filtered count goes up by one. -/
private lemma card_filter_insP_some_succ (ha : a ∉ t) (P : Finpartition t) (b : P.parts)
    (p : Finset ℕ → Prop) [DecidablePred p] (h1 : p (insert a b.1)) (h2 : ¬ p b.1) :
    #((insP a P (some b)).filter p) = #(P.parts.filter p) + 1 := by
  have := card_filter_insP_some ha P b p
  rw [if_pos h1, if_neg h2] at this; omega

end Insert

/-! ### Statistics of a partition relative to a predicate `c` -/

section Stats

variable (c : ℕ → Prop) [DecidablePred c]

/-- Number of parts meeting `c`. -/
private def nC {s : Finset ℕ} (P : Finpartition s) : ℕ := #(P.parts.filter fun b => ∃ x ∈ b, c x)

/-- Number of parts meeting `¬ c`. -/
private def nN {s : Finset ℕ} (P : Finpartition s) : ℕ :=
  #(P.parts.filter fun b => ∃ x ∈ b, ¬ c x)

/-- Number of parts meeting both `c` and `¬ c` (mixed parts). -/
private def nM {s : Finset ℕ} (P : Finpartition s) : ℕ :=
  #(P.parts.filter fun b => (∃ x ∈ b, c x) ∧ ∃ x ∈ b, ¬ c x)

/-- The number of partitions of `s` with `i` parts meeting `c`, `j` parts meeting `¬ c` and `k`
mixed parts. -/
private def cnt (s : Finset ℕ) (i j k : ℕ) : ℕ :=
  #(univ.filter fun P : Finpartition s => nC c P = i ∧ nN c P = j ∧ nM c P = k)

/-- The closed form `S(o,i) S(e,j) C(i,k) C(j,k) k!` of `cnt`. -/
private def F (o e i j k : ℕ) : ℕ :=
  Nat.stirlingSecond o i * Nat.stirlingSecond e j * (i.choose k * j.choose k * k.factorial)

/-- Parts not meeting `c` are exactly the non-mixed parts meeting `¬ c`. -/
private lemma card_filter_not_C {s : Finset ℕ} (P : Finpartition s) :
    #(P.parts.filter fun b => ¬ ∃ x ∈ b, c x) = nN c P - nM c P := by
  have h := card_filter_add_card_filter_not (s := P.parts.filter fun b => ∃ x ∈ b, ¬ c x)
    (fun b => ∃ x ∈ b, c x)
  rw [filter_filter, filter_filter] at h
  have e1 : (P.parts.filter fun b => (∃ x ∈ b, ¬ c x) ∧ ∃ x ∈ b, c x) =
      P.parts.filter fun b => (∃ x ∈ b, c x) ∧ ∃ x ∈ b, ¬ c x :=
    filter_congr fun b _ => and_comm
  have e2 : (P.parts.filter fun b => (∃ x ∈ b, ¬ c x) ∧ ¬ ∃ x ∈ b, c x) =
      P.parts.filter fun b => ¬ ∃ x ∈ b, c x := by
    refine filter_congr fun b hb => ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    obtain ⟨y, hy⟩ := P.nonempty_of_mem_parts hb
    exact ⟨y, hy, fun hy' => h ⟨y, hy, hy'⟩⟩
  rw [e1, e2] at h
  unfold nN nM
  omega

variable {c}
variable {a : ℕ} {t : Finset ℕ}

/-- Statistics after inserting `a` (with `c a`) as a singleton. -/
private lemma stats_none (ha : a ∉ t) (hc : c a) (P : Finpartition t) :
    nC c (ins ha P none) = nC c P + 1 ∧ nN c (ins ha P none) = nN c P ∧
      nM c (ins ha P none) = nM c P := by
  simp only [nC, nN, nM, ins_parts, card_filter_insP_none ha]
  simp [hc]

omit [DecidablePred c] in
/-- `∃ x ∈ insert a b, ¬ c x ↔ ∃ x ∈ b, ¬ c x` when `c a`. -/
private lemma exists_not_insert (hc : c a) (b : Finset ℕ) :
    (∃ x ∈ insert a b, ¬ c x) ↔ ∃ x ∈ b, ¬ c x := by
  constructor
  · rintro ⟨x, hx, hcx⟩
    rcases mem_insert.1 hx with rfl | hx
    · exact absurd hc hcx
    · exact ⟨x, hx, hcx⟩
  · rintro ⟨x, hx, hcx⟩
    exact ⟨x, mem_insert_of_mem hx, hcx⟩

/-- Statistics after inserting `a` (with `c a`) into a part meeting `c`. -/
private lemma stats_some_C (ha : a ∉ t) (hc : c a) (P : Finpartition t) (b : P.parts)
    (hb : ∃ x ∈ b.1, c x) :
    nC c (ins ha P (some b)) = nC c P ∧ nN c (ins ha P (some b)) = nN c P ∧
      nM c (ins ha P (some b)) = nM c P := by
  have e1 : ∃ x ∈ insert a b.1, c x := ⟨a, mem_insert_self _ _, hc⟩
  simp only [nC, nN, nM, ins_parts]
  refine ⟨?_, ?_, ?_⟩
  · exact card_filter_insP_some_eq ha P b (fun b => ∃ x ∈ b, c x) (iff_of_true e1 hb)
  · exact card_filter_insP_some_eq ha P b (fun b => ∃ x ∈ b, ¬ c x) (exists_not_insert hc b.1)
  · exact card_filter_insP_some_eq ha P b (fun b => (∃ x ∈ b, c x) ∧ ∃ x ∈ b, ¬ c x)
      (and_congr (iff_of_true e1 hb) (exists_not_insert hc b.1))

/-- Statistics after inserting `a` (with `c a`) into a part not meeting `c`. -/
private lemma stats_some_N (ha : a ∉ t) (hc : c a) (P : Finpartition t) (b : P.parts)
    (hb : ¬ ∃ x ∈ b.1, c x) :
    nC c (ins ha P (some b)) = nC c P + 1 ∧ nN c (ins ha P (some b)) = nN c P ∧
      nM c (ins ha P (some b)) = nM c P + 1 := by
  have e1 : ∃ x ∈ insert a b.1, c x := ⟨a, mem_insert_self _ _, hc⟩
  have hN : ∃ x ∈ b.1, ¬ c x := by
    obtain ⟨y, hy⟩ := P.nonempty_of_mem_parts b.2
    exact ⟨y, hy, fun hy' => hb ⟨y, hy, hy'⟩⟩
  simp only [nC, nN, nM, ins_parts]
  refine ⟨?_, ?_, ?_⟩
  · exact card_filter_insP_some_succ ha P b (fun b => ∃ x ∈ b, c x) e1 hb
  · exact card_filter_insP_some_eq ha P b (fun b => ∃ x ∈ b, ¬ c x) (exists_not_insert hc b.1)
  · exact card_filter_insP_some_succ ha P b (fun b => (∃ x ∈ b, c x) ∧ ∃ x ∈ b, ¬ c x)
      ⟨e1, (exists_not_insert hc b.1).2 hN⟩ (fun h => hb h.1)

/-- The number of ways to insert `a` (with `c a`) into `P` reaching given statistics. -/
private lemma card_choices (ha : a ∉ t) (hc : c a) (P : Finpartition t) (i j k : ℕ) :
    #(univ.filter fun x : Option P.parts =>
        nC c (ins ha P x) = i ∧ nN c (ins ha P x) = j ∧ nM c (ins ha P x) = k) =
      (if nC c P + 1 = i ∧ nN c P = j ∧ nM c P = k then 1 else 0) +
      (nC c P * (if nC c P = i ∧ nN c P = j ∧ nM c P = k then 1 else 0) +
      (nN c P - nM c P) * (if nC c P + 1 = i ∧ nN c P = j ∧ nM c P + 1 = k then 1 else 0)) := by
  rw [card_filter, Fintype.sum_option]
  obtain ⟨h1, h2, h3⟩ := stats_none ha hc P
  rw [h1, h2, h3]
  congr 1
  let g : Finset ℕ → ℕ := fun b => if ∃ x ∈ b, c x then
    (if nC c P = i ∧ nN c P = j ∧ nM c P = k then 1 else 0) else
    (if nC c P + 1 = i ∧ nN c P = j ∧ nM c P + 1 = k then 1 else 0)
  have hsum : ∀ b : P.parts, (if nC c (ins ha P (some b)) = i ∧ nN c (ins ha P (some b)) = j ∧
      nM c (ins ha P (some b)) = k then 1 else 0) = g b.1 := by
    intro b
    by_cases hb : ∃ x ∈ b.1, c x
    · obtain ⟨e1, e2, e3⟩ := stats_some_C ha hc P b hb
      simp only [g, if_pos hb, e1, e2, e3]
    · obtain ⟨e1, e2, e3⟩ := stats_some_N ha hc P b hb
      simp only [g, if_neg hb, e1, e2, e3]
  rw [Fintype.sum_congr _ _ hsum, Finset.sum_coe_sort (s := P.parts) (f := g)]
  simp only [g]
  rw [sum_ite, sum_const, sum_const, smul_eq_mul, smul_eq_mul, card_filter_not_C c P]
  rfl

/-- The insertion recurrence, before evaluating the sums. -/
private lemma cnt_insert (ha : a ∉ t) (hc : c a) (i j k : ℕ) :
    cnt c (insert a t) i j k =
      ∑ P : Finpartition t, (if nC c P + 1 = i ∧ nN c P = j ∧ nM c P = k then 1 else 0) +
      (∑ P : Finpartition t, nC c P * (if nC c P = i ∧ nN c P = j ∧ nM c P = k then 1 else 0) +
      ∑ P : Finpartition t, (nN c P - nM c P) *
        (if nC c P + 1 = i ∧ nN c P = j ∧ nM c P + 1 = k then 1 else 0)) := by
  rw [cnt, card_filter_ins ha, ← sum_add_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun P _ => card_choices ha hc P i j k

/-- First sum of the recurrence, `i = 0`. -/
private lemma sum1_zero (j k : ℕ) :
    ∑ P : Finpartition t, (if nC c P + 1 = 0 ∧ nN c P = j ∧ nM c P = k then 1 else 0) = 0 :=
  sum_eq_zero fun _ _ => if_neg fun h => Nat.succ_ne_zero _ h.1

/-- First sum of the recurrence. -/
private lemma sum1_succ (i j k : ℕ) :
    ∑ P : Finpartition t, (if nC c P + 1 = i + 1 ∧ nN c P = j ∧ nM c P = k then 1 else 0) =
      cnt c t i j k := by
  rw [cnt, card_filter]
  exact sum_congr rfl fun P _ => by simp only [Nat.add_right_cancel_iff]

/-- Second sum of the recurrence. -/
private lemma sum2 (i j k : ℕ) :
    ∑ P : Finpartition t, nC c P * (if nC c P = i ∧ nN c P = j ∧ nM c P = k then 1 else 0) =
      i * cnt c t i j k := by
  rw [cnt, card_filter, mul_sum]
  refine sum_congr rfl fun P _ => ?_
  split_ifs with h
  · rw [h.1]
  · simp

/-- Third sum of the recurrence, `i = 0`. -/
private lemma sum3_zero_left (j k : ℕ) :
    ∑ P : Finpartition t, (nN c P - nM c P) *
      (if nC c P + 1 = 0 ∧ nN c P = j ∧ nM c P + 1 = k then 1 else 0) = 0 :=
  sum_eq_zero fun P _ => by rw [if_neg fun h => Nat.succ_ne_zero _ h.1, mul_zero]

/-- Third sum of the recurrence, `k = 0`. -/
private lemma sum3_zero_right (i j : ℕ) :
    ∑ P : Finpartition t, (nN c P - nM c P) *
      (if nC c P + 1 = i ∧ nN c P = j ∧ nM c P + 1 = 0 then 1 else 0) = 0 :=
  sum_eq_zero fun P _ => by rw [if_neg fun h => Nat.succ_ne_zero _ h.2.2, mul_zero]

/-- Third sum of the recurrence. -/
private lemma sum3_succ (i j k : ℕ) :
    ∑ P : Finpartition t, (nN c P - nM c P) *
      (if nC c P + 1 = i + 1 ∧ nN c P = j ∧ nM c P + 1 = k + 1 then 1 else 0) =
      (j - k) * cnt c t i j k := by
  rw [cnt, card_filter, mul_sum]
  refine sum_congr rfl fun P _ => ?_
  simp only [Nat.add_right_cancel_iff]
  split_ifs with h
  · rw [h.2.1, h.2.2]
  · simp

/-- The insertion step: if the closed form holds for `t`, it holds for `insert a t` (`c a`). -/
private lemma step (ha : a ∉ t) (hc : c a)
    (IH : ∀ i j k, cnt c t i j k = F #(t.filter c) #(t.filter fun x => ¬ c x) i j k)
    (i j k : ℕ) :
    cnt c (insert a t) i j k = F (#(t.filter c) + 1) #(t.filter fun x => ¬ c x) i j k := by
  rw [cnt_insert ha hc]
  rcases i with _ | i
  · rw [sum1_zero, sum2, sum3_zero_left, F, Nat.stirlingSecond_succ_zero]
    simp
  · rw [sum1_succ, sum2]
    rcases k with _ | k
    · rw [sum3_zero_right, IH, IH]
      simp only [F, Nat.stirlingSecond_succ_succ, Nat.choose_zero_right, Nat.factorial_zero]
      ring
    · rw [sum3_succ, IH, IH, IH]
      simp only [F, Nat.stirlingSecond_succ_succ, Nat.choose_succ_succ', Nat.factorial_succ]
      have hj := Nat.choose_succ_right_eq j k
      generalize j - k = d at hj ⊢
      generalize #(t.filter c) = o
      generalize #(t.filter fun x => ¬ c x) = e
      zify at hj ⊢
      linear_combination (-((Nat.stirlingSecond o i : ℤ) * (Nat.stirlingSecond e j : ℤ) *
        (i.choose k : ℤ) * (k.factorial : ℤ))) * hj

variable (c)

/-- Swapping `c` and `¬ c` swaps the first two statistics. -/
private lemma cnt_not (s : Finset ℕ) (i j k : ℕ) :
    cnt (fun x => ¬ c x) s i j k = cnt c s j i k := by
  unfold cnt
  congr 1
  apply filter_congr
  intro P _
  have e1 : nC (fun x => ¬ c x) P = nN c P := rfl
  have e2 : nN (fun x => ¬ c x) P = nC c P := by
    unfold nN nC
    congr 1
    exact filter_congr fun b _ => by simp only [not_not]
  have e3 : nM (fun x => ¬ c x) P = nM c P := by
    unfold nM
    congr 1
    exact filter_congr fun b _ => by simp only [not_not]; exact and_comm
  rw [e1, e2, e3]
  tauto

/-- `F` is symmetric. -/
private lemma F_comm (o e i j k : ℕ) : F o e i j k = F e o j i k := by
  unfold F; ring

/-- The refined count: `cnt c s i j k = S(o,i) S(e,j) C(i,k) C(j,k) k!`, where `o`, `e` are the
numbers of elements of `s` satisfying `c`, `¬ c`. -/
private theorem cnt_eq (s : Finset ℕ) :
    ∀ i j k, cnt c s i j k = F #(s.filter c) #(s.filter fun x => ¬ c x) i j k := by
  induction s using Finset.induction_on with
  | empty =>
    intro i j k
    have hP : ∀ P : Finpartition (∅ : Finset ℕ), P.parts = ∅ := fun P => by
      ext b
      simp only [notMem_empty, iff_false]
      intro hb
      exact P.ne_empty hb (subset_empty.1 (P.subset hb))
    have hcard : Fintype.card (Finpartition (∅ : Finset ℕ)) = 1 := by
      rw [Fintype.card_eq_one_iff]
      exact ⟨⊥, fun P => Finpartition.ext (by rw [hP, hP])⟩
    simp only [cnt, nC, nN, nM, hP, filter_empty, card_empty]
    rcases i with _ | i <;> rcases j with _ | j <;> rcases k with _ | k <;>
      simp [F, hcard, Nat.stirlingSecond_zero_succ]
  | insert a t ha IH =>
    intro i j k
    by_cases hc : c a
    · have h1 : #((insert a t).filter c) = #(t.filter c) + 1 := by
        rw [filter_insert, if_pos hc, card_insert_of_notMem (fun h => ha (mem_filter.1 h).1)]
      have h2 : #((insert a t).filter fun x => ¬ c x) = #(t.filter fun x => ¬ c x) := by
        rw [filter_insert, if_neg (not_not.2 hc)]
      rw [h1, h2]
      exact step ha hc IH i j k
    · have IH' : ∀ i j k, cnt (fun x => ¬ c x) t i j k =
          F #(t.filter fun x => ¬ c x) #(t.filter fun x => ¬ ¬ c x) i j k := by
        intro i j k
        rw [cnt_not, IH, F_comm]
        congr 2
        exact filter_congr fun x _ => not_not.symm
      have h1 : #((insert a t).filter c) = #(t.filter c) := by
        rw [filter_insert, if_neg hc]
      have h2 : #((insert a t).filter fun x => ¬ c x) = #(t.filter fun x => ¬ c x) + 1 := by
        rw [filter_insert, if_pos hc, card_insert_of_notMem (fun h => ha (mem_filter.1 h).1)]
      have h3 := step (c := fun x => ¬ c x) ha hc IH' j i k
      rw [cnt_not] at h3
      rw [h3, h1, h2, F_comm]
      congr 2
      exact filter_congr fun x _ => not_not

end Stats

/-! ### Specialisation to `{1, …, n}` and parity -/

/-- `{1, …, n}` has `⌈n/2⌉` odd and `⌊n/2⌋` even elements. -/
private lemma card_odd (n : ℕ) :
    #((Icc 1 n).filter Odd) = (n + 1) / 2 ∧ #((Icc 1 n).filter fun x => ¬ Odd x) = n / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega : 1 ≤ n + 1), filter_insert,
      filter_insert]
    have hn : n + 1 ∉ Icc 1 n := by simp
    by_cases h : Odd (n + 1)
    · rw [if_pos h, if_neg (not_not.2 h),
        card_insert_of_notMem (fun h' => hn (mem_filter.1 h').1)]
      obtain ⟨m, hm⟩ := h
      omega
    · rw [if_neg h, if_pos h, card_insert_of_notMem (fun h' => hn (mem_filter.1 h').1)]
      rw [Nat.not_odd_iff_even] at h
      obtain ⟨m, hm⟩ := h
      omega

/-- Summing `S(m,i) C(i,k)` over a longer range gives `A049020 m k`. -/
private lemma sum_eq_A049020 {m N : ℕ} (h : m ≤ N) (k : ℕ) :
    ∑ i ∈ range (N + 1), Nat.stirlingSecond m i * i.choose k = A049020 m k := by
  unfold A049020
  symm
  apply sum_subset (range_subset_range.2 (by omega))
  intro i hi hi'
  rw [mem_range] at hi'
  rw [Nat.stirlingSecond_eq_zero_of_lt (by omega), zero_mul]

/-- Hanna's conjecture: `A124418(n,k) = k! · A049020(⌊n/2⌋,k) · A049020(⌈n/2⌉,k)`. -/
theorem result : statement := by
  intro n k _
  have hmix : ∀ P : Finpartition (Icc 1 n), #(P.parts.filter IsMixed) = nM Odd P := fun P => by
    unfold nM
    congr 1
    exact filter_congr fun b _ => by simp only [IsMixed, Nat.not_odd_iff_even]
  have hle : ∀ (P : Finpartition (Icc 1 n)) (p : Finset ℕ → Prop) [DecidablePred p],
      #(P.parts.filter p) < n + 1 := fun P p _ => by
    have h1 := card_filter_le P.parts p
    have h2 := P.card_parts_le_card
    simp only [Nat.card_Icc] at h2
    omega
  have hfib : A124418 n k = ∑ ij ∈ range (n + 1) ×ˢ range (n + 1),
      cnt Odd (Icc 1 n) ij.1 ij.2 k := by
    rw [A124418]
    simp only [hmix]
    rw [card_eq_sum_card_fiberwise (f := fun P => (nC Odd P, nN Odd P))
      (t := range (n + 1) ×ˢ range (n + 1))]
    · refine sum_congr rfl fun ij _ => ?_
      rw [cnt, filter_filter]
      congr 1
      apply filter_congr
      intro P _
      simp only [Prod.ext_iff]
      tauto
    · intro P _
      simp only [mem_coe, mem_product, mem_range]
      exact ⟨hle P _, hle P _⟩
  rw [hfib, sum_product]
  obtain ⟨ho, he⟩ := card_odd n
  simp only [cnt_eq Odd (Icc 1 n), ho, he, F]
  rw [T, ← sum_eq_A049020 (by omega : n / 2 ≤ n) k,
    ← sum_eq_A049020 (by omega : (n + 1) / 2 ≤ n) k, sum_mul_sum, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  ring

end Math0.Frontier.A124526

#math0_settles Math0.Frontier.A124526.result Math0.Statements.A124526.statement
