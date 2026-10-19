/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A397315
import Math0.Audit

/-!
# A397315: a 14-point blackout of the 5 × 8 grid refutes `T(n,m) = n + m`

The conjecture in OEIS A397315 asserts `T(n, m) = n + m` for `min(n, m) ≥ 4` apart from
`T(4,4) = 7` and `T(4,5) = T(5,4) = 8`. In particular it predicts `T 5 8 = 13`. We refute it by
exhibiting a valid blackout of the `5 × 8` grid (`n = 5` rows `y < 5`, `k = 8` columns `x < 8`)
with 14 points, so `T 5 8 ≥ 14`.

The blacked-out points `(x, y)` are
`(0,1), (0,4), (1,0), (1,1), (2,0), (2,3), (3,0), (4,0), (5,1), (5,2), (6,2), (6,3), (7,3), (7,4)`;
with the statement's numbering `i = 5 x + y` they form the bitmask `Bw = 837721039986`.

Validity is checked as follows, without letting the kernel evaluate `rects 5 8` directly (that
computation uses too much memory).
* `rectMask_eq`: `rectMask? n k a b c` agrees with `fastMask n k a b c`, which computes the same
  thing with natural-number arithmetic only (the dot product condition is rearranged so that no
  subtraction is needed). This is a general proof, not a computation.
* `chkA a = true` for every `a < 40` (40 separate `decide +kernel` checks): for all `b, c < 40`,
  whenever `fastMask 5 8 a b c = some r`, the mask `r` occurs in the explicit list `Lr` of 364
  rectangle masks. Hence every element of `rects 5 8` lies in `Lr`.
* `dist`: the visible parts `R \ Bw` for `R ∈ Lr` are pairwise distinct (`decide +kernel`).
* `rects 5 8` has no duplicates (it is an `eraseDups`), so `R ↦ R \ Bw` is injective on it, i.e.
  `isValidBlackout 5 8 Bw = true`. Since `Bw` has 14 bits, `T 5 8 ≥ 14 > 13`.
-/

namespace Math0.Frontier.A397315
open Math0.Statements.A397315

/-- `rectMask?` with natural-number arithmetic only: the coordinates are `(i / n, i % n)`, the
right-angle condition `(A - B) · (C - B) = 0` is written as `A·C + B·B = A·B + B·C`, and
`D = A + C - B` lies in the grid iff `B ≤ A + C < (k, n) + B` coordinatewise. -/
private def fastMask (n k a b c : ℕ) : Option ℕ :=
  if a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
     (a/n)*(c/n) + (b/n)*(b/n) + (a%n)*(c%n) + (b%n)*(b%n) =
       (a/n)*(b/n) + (b/n)*(c/n) + (a%n)*(b%n) + (b%n)*(c%n) ∧
     b/n ≤ a/n + c/n ∧ a/n + c/n < k + b/n ∧ b%n ≤ a%n + c%n ∧ a%n + c%n < n + b%n
  then some (2^a ||| 2^b ||| 2^c ||| 2^((a/n + c/n - b/n)*n + (a%n + c%n - b%n)))
  else none

/-- `rectMask?` and `fastMask` agree everywhere. -/
private theorem rectMask_eq (n k a b c : ℕ) : rectMask? n k a b c = fastMask n k a b c := by
  unfold rectMask? fastMask pt inGrid idx
  generalize a / n = ax, a % n = ay, b / n = bx, b % n = by', c / n = cx, c % n = cy
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Bool.and_eq_true,
    decide_eq_true_eq]
  have hdot : ((ax : ℤ) - bx) * ((cx : ℤ) - bx) + ((ay : ℤ) - by') * ((cy : ℤ) - by') = 0 ↔
      ax * cx + bx * bx + ay * cy + by' * by' = ax * bx + bx * cx + ay * by' + by' * cy := by
    constructor
    · intro h
      have : ((ax * cx + bx * bx + ay * cy + by' * by' : ℕ) : ℤ) =
          ((ax * bx + bx * cx + ay * by' + by' * cy : ℕ) : ℤ) := by
        push_cast; linear_combination h
      exact_mod_cast this
    · intro h
      have := congrArg (fun x : ℕ => (x : ℤ)) h
      push_cast at this
      linear_combination this
  by_cases h : a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      ax * cx + bx * bx + ay * cy + by' * by' = ax * bx + bx * cx + ay * by' + by' * cy ∧
      bx ≤ ax + cx ∧ ax + cx < k + bx ∧ by' ≤ ay + cy ∧ ay + cy < n + by'
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
    rw [if_pos ⟨h1, h2, h3, hdot.mpr h4, by omega⟩, if_pos ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩]
    have e1 : ((ax : ℤ) + cx - bx).toNat = ax + cx - bx := by omega
    have e2 : ((ay : ℤ) + cy - by').toNat = ay + cy - by' := by omega
    rw [e1, e2]
  · rw [if_neg h, if_neg]
    rintro ⟨h1, h2, h3, h4, h5⟩
    exact h ⟨h1, h2, h3, hdot.mp h4, by omega, by omega, by omega, by omega⟩

/-- The 364 rectangle vertex sets of the `5 × 8` grid, as bitmasks (sorted). -/
private def Lr : List ℕ := [
  99, 165, 198, 297, 330, 396, 561, 594,
  660, 792, 2210, 3075, 3168, 4420, 5125, 5280,
  6150, 6336, 8840, 9225, 9504, 10250, 10560, 12300,
  12672, 17425, 17952, 18450, 19008, 20500, 21120, 24600,
  25344, 66820, 70720, 73764, 98307, 98400, 101376, 132354,
  133640, 139298, 141440, 147528, 163845, 164000, 168960, 196614,
  196800, 202752, 264708, 278596, 282880, 294921, 295200, 304128,
  327690, 328000, 337920, 393228, 393600, 405504, 557073, 557600,
  574464, 589842, 590400, 608256, 655380, 656000, 675840, 786456,
  787200, 811008, 2130440, 2138240, 2263040, 2360448, 2621480, 3145731,
  3145824, 3148800, 3244032, 4211716, 4235328, 4276480, 4457536, 4526080,
  4720896, 5242885, 5243040, 5248000, 5406720, 6291462, 6291648, 6297600,
  6488064, 8421890, 8470656, 8912930, 8915072, 9052160, 9437193, 9437472,
  9446400, 9732096, 10485770, 10486080, 10496000, 10813440, 12582924, 12583296,
  12595200, 12976128, 17825809, 17826336, 17843200, 18382848, 18874386, 18874944,
  18892800, 19464192, 20971540, 20972160, 20992000, 21626880, 25165848, 25166592,
  25190400, 25952256, 68174080, 68423680, 72417280, 75534336, 83887360, 100663299,
  100663392, 100666368, 100761600, 103809024, 134774912, 135266820, 135530496, 136847360,
  142641152, 144834560, 150994980, 151068672, 167772165, 167772320, 167777280, 167936000,
  173015040, 201326598, 201326784, 201332736, 201523200, 207618048, 269500480, 271060992,
  285213760, 285282304, 289669120, 301989897, 301990176, 301999104, 302284800, 311427072,
  335544330, 335544640, 335554560, 335872000, 346030080, 402653196, 402653568, 402665472,
  403046400, 415236096, 570425361, 570425888, 570442752, 570982400, 588251136, 603979794,
  603980352, 603998208, 604569600, 622854144, 671088660, 671089280, 671109120, 671744000,
  692060160, 805306392, 805307136, 805330944, 806092800, 830472192, 2181570560, 2189557760,
  2317352960, 2417098752, 2684395520, 3221225475, 3221225568, 3221228544, 3221323776, 3224371200,
  3321888768, 4312797184, 4328538240, 4336975872, 4379115520, 4564516864, 4634705920, 4831839360,
  4834197504, 5368709125, 5368709280, 5368714240, 5368872960, 5373952000, 5536481280, 6442450950,
  6442451136, 6442457088, 6442647552, 6448742400, 6643777536, 8624015360, 8673951744, 9126840320,
  9129033728, 9269411840, 9663676425, 9663676704, 9663685632, 9663971328, 9673113600, 9965666304,
  10737418250, 10737418560, 10737428480, 10737745920, 10747904000, 11072962560, 12884901900, 12884902272,
  12884914176, 12885295104, 12897484800, 13287555072, 18253611025, 18253611552, 18253628416, 18254168064,
  18271436800, 18824036352, 19327352850, 19327353408, 19327371264, 19327942656, 19346227200, 19931332608,
  21474836500, 21474837120, 21474856960, 21475491840, 21495808000, 22145925120, 25769803800, 25769804544,
  25769828352, 25770590208, 25794969600, 26575110144, 69810257920, 70065848320, 74155294720, 77347160064,
  85900656640, 103079215107, 103079215200, 103079218176, 103079313408, 103082360832, 103179878400, 106300440576,
  138009509888, 138513223680, 138783227904, 140131696640, 146064539648, 148310589440, 154618859520, 154694320128,
  171798691845, 171798692000, 171798696960, 171798855680, 171803934720, 171966464000, 177167400960, 206158430214,
  206158430400, 206158436352, 206158626816, 206164721664, 206359756800, 212600881152, 275968491520, 277566455808,
  292058890240, 292129079296, 296621178880, 309237645321, 309237645600, 309237654528, 309237940224, 309247082496,
  309539635200, 318901321728, 343597383690, 343597384000, 343597393920, 343597711360, 343607869440, 343932928000,
  354334801920, 412316860428, 412316860800, 412316872704, 412317253632, 412329443328, 412719513600, 425201762304,
  584115552273, 584115552800, 584115569664, 584116109312, 584133378048, 584685977600, 602369163264, 618475290642,
  618475291200, 618475309056, 618475880448, 618494164992, 619079270400, 637802643456, 687194767380, 687194768000,
  687194787840, 687195422720, 687215738880, 687865856000, 708669603840, 824633720856, 824633721600, 824633745408,
  824634507264, 824658886656, 825439027200, 850403524608]

/-- The witness blackout: the 14 points listed in the module docstring, as a bitmask. -/
private def Bw : ℕ := 837721039986

/-- `scan r l = true` iff `r` occurs in `l` (linear scan with `Nat.beq`). -/
private def scan (r : ℕ) (l : List ℕ) : Bool := l.rec false fun y _ ih => Nat.beq r y || ih

/-- `memL r = true` iff `r` occurs in `Lr`. -/
private def memL (r : ℕ) : Bool := scan r Lr

/-- The per-triple check: if `(a, b, c)` spans a rectangle of the `5 × 8` grid, its mask is in
`Lr`. -/
private def F (a b c : ℕ) : Bool :=
  match fastMask 5 8 a b c with
  | none => true
  | some r => memL r

/-- `F a b c` for all `b, c < 40`. -/
private def chkA (a : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun b ihb =>
    Nat.rec (motive := fun _ => Bool) true (fun c ihc => F a b c && ihc) 40 && ihb) 40

/-- Kernel check of `chkA 0`. -/
private theorem chk_0 : chkA 0 = true := by decide +kernel
/-- Kernel check of `chkA 1`. -/
private theorem chk_1 : chkA 1 = true := by decide +kernel
/-- Kernel check of `chkA 2`. -/
private theorem chk_2 : chkA 2 = true := by decide +kernel
/-- Kernel check of `chkA 3`. -/
private theorem chk_3 : chkA 3 = true := by decide +kernel
/-- Kernel check of `chkA 4`. -/
private theorem chk_4 : chkA 4 = true := by decide +kernel
/-- Kernel check of `chkA 5`. -/
private theorem chk_5 : chkA 5 = true := by decide +kernel
/-- Kernel check of `chkA 6`. -/
private theorem chk_6 : chkA 6 = true := by decide +kernel
/-- Kernel check of `chkA 7`. -/
private theorem chk_7 : chkA 7 = true := by decide +kernel
/-- Kernel check of `chkA 8`. -/
private theorem chk_8 : chkA 8 = true := by decide +kernel
/-- Kernel check of `chkA 9`. -/
private theorem chk_9 : chkA 9 = true := by decide +kernel
/-- Kernel check of `chkA 10`. -/
private theorem chk_10 : chkA 10 = true := by decide +kernel
/-- Kernel check of `chkA 11`. -/
private theorem chk_11 : chkA 11 = true := by decide +kernel
/-- Kernel check of `chkA 12`. -/
private theorem chk_12 : chkA 12 = true := by decide +kernel
/-- Kernel check of `chkA 13`. -/
private theorem chk_13 : chkA 13 = true := by decide +kernel
/-- Kernel check of `chkA 14`. -/
private theorem chk_14 : chkA 14 = true := by decide +kernel
/-- Kernel check of `chkA 15`. -/
private theorem chk_15 : chkA 15 = true := by decide +kernel
/-- Kernel check of `chkA 16`. -/
private theorem chk_16 : chkA 16 = true := by decide +kernel
/-- Kernel check of `chkA 17`. -/
private theorem chk_17 : chkA 17 = true := by decide +kernel
/-- Kernel check of `chkA 18`. -/
private theorem chk_18 : chkA 18 = true := by decide +kernel
/-- Kernel check of `chkA 19`. -/
private theorem chk_19 : chkA 19 = true := by decide +kernel
/-- Kernel check of `chkA 20`. -/
private theorem chk_20 : chkA 20 = true := by decide +kernel
/-- Kernel check of `chkA 21`. -/
private theorem chk_21 : chkA 21 = true := by decide +kernel
/-- Kernel check of `chkA 22`. -/
private theorem chk_22 : chkA 22 = true := by decide +kernel
/-- Kernel check of `chkA 23`. -/
private theorem chk_23 : chkA 23 = true := by decide +kernel
/-- Kernel check of `chkA 24`. -/
private theorem chk_24 : chkA 24 = true := by decide +kernel
/-- Kernel check of `chkA 25`. -/
private theorem chk_25 : chkA 25 = true := by decide +kernel
/-- Kernel check of `chkA 26`. -/
private theorem chk_26 : chkA 26 = true := by decide +kernel
/-- Kernel check of `chkA 27`. -/
private theorem chk_27 : chkA 27 = true := by decide +kernel
/-- Kernel check of `chkA 28`. -/
private theorem chk_28 : chkA 28 = true := by decide +kernel
/-- Kernel check of `chkA 29`. -/
private theorem chk_29 : chkA 29 = true := by decide +kernel
/-- Kernel check of `chkA 30`. -/
private theorem chk_30 : chkA 30 = true := by decide +kernel
/-- Kernel check of `chkA 31`. -/
private theorem chk_31 : chkA 31 = true := by decide +kernel
/-- Kernel check of `chkA 32`. -/
private theorem chk_32 : chkA 32 = true := by decide +kernel
/-- Kernel check of `chkA 33`. -/
private theorem chk_33 : chkA 33 = true := by decide +kernel
/-- Kernel check of `chkA 34`. -/
private theorem chk_34 : chkA 34 = true := by decide +kernel
/-- Kernel check of `chkA 35`. -/
private theorem chk_35 : chkA 35 = true := by decide +kernel
/-- Kernel check of `chkA 36`. -/
private theorem chk_36 : chkA 36 = true := by decide +kernel
/-- Kernel check of `chkA 37`. -/
private theorem chk_37 : chkA 37 = true := by decide +kernel
/-- Kernel check of `chkA 38`. -/
private theorem chk_38 : chkA 38 = true := by decide +kernel
/-- Kernel check of `chkA 39`. -/
private theorem chk_39 : chkA 39 = true := by decide +kernel

/-- The visible parts of the rectangles in `Lr` under the blackout `Bw` are pairwise distinct. -/
private theorem dist : pairwiseDistinct (Lr.map (visible · Bw)) = true := by decide +kernel

/-- The witness has 14 points. -/
private theorem card_Bw : card (5 * 8) Bw = 14 := by decide +kernel

/-- A `Nat.rec` conjunction loop that evaluates to `true` gives `f c = true` for each `c < m`. -/
private theorem loop_spec (f : ℕ → Bool) (m : ℕ)
    (h : Nat.rec (motive := fun _ => Bool) true (fun c ih => f c && ih) m = true) :
    ∀ c < m, f c = true := by
  induction m with
  | zero => intro c hc; omega
  | succ m ih =>
    intro c hc
    change (f m && Nat.rec (motive := fun _ => Bool) true (fun c ih => f c && ih) m) = true at h
    rw [Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | rfl
    · exact ih h.2 c hc
    · exact h.1

/-- `chkA a = true` for all `a < 40`. -/
private theorem chk_all (a : ℕ) (ha : a < 40) : chkA a = true := by
  interval_cases a
  exacts [chk_0, chk_1, chk_2, chk_3, chk_4, chk_5, chk_6, chk_7, chk_8, chk_9, chk_10, chk_11, chk_12, chk_13, chk_14, chk_15, chk_16, chk_17, chk_18, chk_19, chk_20, chk_21, chk_22, chk_23, chk_24, chk_25, chk_26, chk_27, chk_28, chk_29, chk_30, chk_31, chk_32, chk_33, chk_34, chk_35, chk_36, chk_37, chk_38, chk_39]

/-- `F a b c = true` for all `a, b, c < 40`. -/
private theorem F_true (a b c : ℕ) (ha : a < 40) (hb : b < 40) (hc : c < 40) :
    F a b c = true :=
  loop_spec (F a b) 40 (loop_spec (fun b =>
    Nat.rec (motive := fun _ => Bool) true (fun c ihc => F a b c && ihc) 40) 40
      (chk_all a ha) b hb) c hc

/-- Soundness of a `Nat.beq` linear scan. -/
private theorem mem_of_scan (r : ℕ) (l : List ℕ) (h : scan r l = true) : r ∈ l := by
  induction l with
  | nil => exact absurd (h : false = true) Bool.false_ne_true
  | cons y ys ih =>
    change (Nat.beq r y || scan r ys) = true at h
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · exact List.mem_cons.mpr (Or.inl (Nat.eq_of_beq_eq_true h))
    · exact List.mem_cons_of_mem _ (ih h)

/-- Every rectangle of the `5 × 8` grid is in `Lr`. -/
private theorem mem_rects {r : ℕ} (h : r ∈ rects 5 8) : r ∈ Lr := by
  unfold rects at h
  rw [List.mem_eraseDups] at h
  simp only [List.mem_flatMap, List.mem_filterMap, List.mem_range] at h
  obtain ⟨a, ha, b, hb, c, hc, hr⟩ := h
  rw [rectMask_eq] at hr
  have hF : memL r = true := by
    have h1 := F_true a b c (by omega) (by omega) (by omega)
    unfold F at h1
    rw [hr] at h1
    exact h1
  exact mem_of_scan r Lr hF

/-- `notMem x l = true` iff `x ∉ l`. -/
private theorem notMem_iff (x : ℕ) (l : List ℕ) : notMem x l = true ↔ x ∉ l := by
  induction l with
  | nil => exact ⟨fun _ => List.not_mem_nil, fun _ => rfl⟩
  | cons y ys ih =>
    change (!(Nat.beq x y) && notMem x ys) = true ↔ _
    have hb : Nat.beq x y = false ↔ ¬ x = y :=
      ⟨Nat.ne_of_beq_eq_false, fun h => Bool.eq_false_iff.mpr fun h' => h (Nat.eq_of_beq_eq_true h')⟩
    rw [Bool.and_eq_true, ih, List.mem_cons, not_or, Bool.not_eq_true', hb]

/-- `pairwiseDistinct l = true` iff `l.Nodup`. -/
private theorem pd_iff (l : List ℕ) : pairwiseDistinct l = true ↔ l.Nodup := by
  induction l with
  | nil => exact ⟨fun _ => List.nodup_nil, fun _ => rfl⟩
  | cons x xs ih =>
    change (notMem x xs && pairwiseDistinct xs) = true ↔ _
    rw [Bool.and_eq_true, notMem_iff, ih, List.nodup_cons]

/-- `eraseDups` produces a list without duplicates. -/
private theorem nodup_eraseDups' (l : List ℕ) : l.eraseDups.Nodup := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ m ih =>
    cases l with
    | nil => exact List.nodup_nil
    | cons x xs =>
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · rw [List.mem_eraseDups, List.mem_filter]
        simp
      · have := List.length_filter_le (fun b => !b == x) xs
        simp only [List.length_cons] at h
        exact ih _ (by omega) _ rfl

/-- The witness is a valid blackout of the `5 × 8` grid. -/
private theorem valid : isValidBlackout 5 8 Bw = true := by
  unfold isValidBlackout
  rw [pd_iff]
  have hL : (Lr.map (visible · Bw)).Nodup := (pd_iff _).mp dist
  have hR : (rects 5 8).Nodup := by
    unfold rects
    exact nodup_eraseDups' _
  exact hR.map_on fun x hx y hy hxy =>
    List.inj_on_of_nodup_map hL (mem_rects hx) (mem_rects hy) hxy

/-- The maximum in a `foldr`-of-`max` is at least each value. -/
private theorem le_foldr (f : ℕ → ℕ) (l : List ℕ) (x : ℕ) (hx : x ∈ l) :
    f x ≤ l.foldr (fun B m => max (f B) m) 0 := by
  induction l with
  | nil => exact absurd hx List.not_mem_nil
  | cons y ys ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

/-- `T 5 8 ≥ 14`. -/
private theorem T_5_8_ge : 14 ≤ T 5 8 := by
  have hmem : Bw ∈ (List.range (2 ^ (5 * 8))).filter (isValidBlackout 5 8) := by
    rw [List.mem_filter, List.mem_range]
    exact ⟨by norm_num [Bw], valid⟩
  have h := le_foldr (card (5 * 8)) _ _ hmem
  rw [card_Bw] at h
  unfold T
  exact h

/-- The conjecture of A397315 is false: it predicts `T 5 8 = 5 + 8 = 13`, but `T 5 8 ≥ 14`. -/
theorem result : ¬ statement := by
  intro h
  have h58 := h 5 8 (by norm_num)
  have h14 := T_5_8_ge
  rw [h58] at h14
  norm_num at h14

end Math0.Frontier.A397315

#math0_settles Math0.Frontier.A397315.result Math0.Statements.A397315.statement
