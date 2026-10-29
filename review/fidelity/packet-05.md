# Fidelity review packet 05 of 11

Prepared on 29 Oct 2026 by an adversarial reviewing agent, not by a person. It is meant to make a human review of these statements quick: for each one it quotes the OEIS conjecture and the frozen Lean statement, restates the Lean in plain words, and lists anything a reviewer should look at. See [the index](README.md).

Statements in this packet: A182617, A188474, A195249, A201060, A209802, A211343, A215010, A223395, A229159, A242396.

## A182617: The toothpick spiral around n hexagonal cells (A182617): a(n) = 2n + ceil(sqrt(12n - 3))

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a182617](../../results/oeis-a182617/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A182617.lean`](../../lean/Math0/Statements/OEIS/A182617.lean).

**The conjecture as stated in OEIS**

> %F A182617 Conjecture: a(n) = 2*n + ceiling(sqrt(12*n - 3)), for n > 0. - _Vincenzo Librandi_, Sep 20 2017  (Name: "Number of toothpicks in a toothpick spiral around n cells on hexagonal net." Comments: a cell is "ON" if its 6 vertices are covered by toothpicks; the walk spirals round the centre hexagon (5 edges), then steps out and goes round each successive ring; "interrupt counting the total number of toothpicks each time one of the hexagons has six vertices covered." Offset 0, a(0)=0, a(1)=5, a(2)=9, a(3)=12.)

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ n : ℕ, 0 < n → a n = 2 * n + ⌈Real.sqrt (12 * (n : ℝ) - 3)⌉₊

-- dependencies (abridged)
abbrev Pt := ℤ × ℤ
def nbrs (v : Pt) : Pt × Pt × Pt :=
  if (v.1 + v.2) % 2 = 0 then ((v.1 + 1, v.2), (v.1, v.2 + 1), (v.1 - 1, v.2))
  else ((v.1 + 1, v.2), (v.1 - 1, v.2), (v.1, v.2 - 1))
def turns (p v : Pt) : Pt × Pt :=
  let (n0, n1, n2) := nbrs v
  if p = n0 then (n2, n1) else if p = n1 then (n0, n2) else (n1, n0)
def step : List Pt → List Pt
  | v :: p :: rest => let w := v :: p :: rest; let (l, r) := turns p v
      if l ∉ w then l :: w else if r ∉ w then r :: w else w
  | w => w
def walk : ℕ → List Pt
  | 0 => [(0, 0)]
  | t + 1 => step^[t] [(1, 0), (0, 0)]
def cellVerts (c : Pt) : List Pt := [(c.1, c.2), (c.1 + 1, c.2), (c.1 + 2, c.2),
    (c.1, c.2 + 1), (c.1 + 1, c.2 + 1), (c.1 + 2, c.2 + 1)]
def onCells (w : List Pt) : Finset Pt :=
  w.toFinset.filter (fun c => (c.1 + c.2) % 2 = 0 ∧ ∀ u ∈ cellVerts c, u ∈ w)
def onCount (t : ℕ) : ℕ := (onCells (walk t)).card
def a (n : ℕ) : ℕ :=
  ((List.range (6 * n + 1)).find? (fun t => n ≤ onCount t)).getD (6 * n + 1)
```

**What the Lean statement says**

Model the hexagonal net as the brick-wall graph on ℤ² and its hexagonal cells as 2×1 bricks. A self-avoiding walk starts with the edge (0,0)→(1,0). At each vertex it turns left if that neighbour is unvisited, and otherwise turns right. A cell is ON once all six of its vertices have been visited. a(n) is the least number t of walk edges (toothpicks) after which at least n cells are ON, with the search capped at 6n (returning 6n+1 beyond the cap). The claim is that for every n ≥ 1, a(n) = 2n + ⌈√(12n−3)⌉. statement_iff proves this equivalent to the same claim with "least t" taken with no cap.

**What the kernel checks against the OEIS data**

a_data kernel-checks all 40 listed terms a(0..39). That covers cell rings 0–3 completely (37 cells) and the start of ring 4, which pins the walk rule, the cell model and the "least t" reading on the listed range. I also simulated the Lean walk independently in Python. It never gets stuck, it never turns two cells ON with one toothpick (so "least t with ≥ n ON" is exactly the moment the n-th cell turns ON), and it matches 2n + ⌈√(12n−3)⌉ for every 1 ≤ n ≤ 29,700.

**Points for the reviewer**

- *Note.* The spiral is the formalizer's operationalization of a verbal description: brick-wall coordinates plus a greedy rule ("left if unvisited, else right"). The brick faces are exactly the hexagons of the net, and the left/right turns are computed correctly from the counterclockwise neighbour order. The 40 kernel-checked terms and the simulation to n ≈ 29,700 strongly support that this is the intended spiral. A reviewer should still know that the theorem is about this explicit model, as the catalog summary says ("encoded as in Math0.Statements.A182617").
- *Note.* The 6n search cap cannot create a spurious proof. For n ≥ 1 the conjectured value is ≤ 6n (proved in statement_iff), so a capped-out value of 6n+1 would make the statement false, not vacuously true. ⌈√(12n−3)⌉₊ is the ordinary ceiling because 12n−3 > 0 for n ≥ 1. The range n > 0 matches the conjecture.

## A188474: The row sums of the generalized Deutsch triangle A188474 are A137398

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a188474](../../results/oeis-a188474/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A188474.lean`](../../lean/Math0/Statements/OEIS/A188474.lean).

**The conjecture as stated in OEIS**

> %C A188474 Row sums are A137398(n+1) (conjecture). Diagonal sums are A188476.  [_Paul Barry_, Apr 01 2011]  (%F A188474 T(n,k)=sum{j=0..n-k+1, (j/(n+2-j))*C(n+2-j,n-k+1)*C(n+2-j,k+1)*2^(j-1)}. Offset 0, tabl. A137398 is now offset 1 with data 0,1,2,7,22,74,252,...; its %E: "Offset, a(15), a(18) corrected by and more terms from _Georg Fischer_, Jun 07 2021".)

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ n : ℕ, ∑ k ∈ range (n + 1), T n k = (A137398 (n + 2) : ℚ)

-- dependencies
def T (n k : ℕ) : ℚ :=
  ∑ j ∈ range (n - k + 2),
    (j : ℚ) / ((n : ℚ) + 2 - j) * ((n + 2 - j).choose (n - k + 1) : ℚ) *
      ((n + 2 - j).choose (k + 1) : ℚ) * (2 : ℚ) ^ ((j : ℤ) - 1)
def A137398 (m : ℕ) : ℕ :=
  ((List.range (2 * m)).sublistsLen m).countP fun p =>
    let q := (List.range (2 * m)).filter (· ∉ p)
    decide (0 ∈ p ∧ ∀ i < m,
      ¬ ((p.set i (q.getD i 0)).Pairwise (· < ·) ∧ (q.set i (p.getD i 0)).Pairwise (· < ·)))
```

**What the Lean statement says**

Let T(n,k) = Σ_{j=0}^{n−k+1} (j/(n+2−j))·C(n+2−j, n−k+1)·C(n+2−j, k+1)·2^{j−1}, computed exactly in ℚ. Let A(m) be the number of length-m subsequences p of (0,1,…,2m−1) with 0 ∈ p for which no index i < m has the following property: swapping p(i) with q(i), where q is the complementary subsequence, leaves both p and q strictly increasing. The claim is that for every n ≥ 0, Σ_{k=0}^{n} T(n,k) = A(n+2).

**What the kernel checks against the OEIS data**

a_data kernel-checks all 66 listed triangle terms (rows 0–10), which pins T. A137398_data kernel-checks A137398(1..6) = 0,1,2,7,22,74 from the combinatorial definition. rowSum_data kernel-checks row sums n = 0..10 = 1,2,7,…,142278, the A137398 terms from the second on, which fixes the index shift. statement_check verifies the statement for n ≤ 4. Independently, a Python brute force of the Lean A137398 definition matches the OEIS data for m ≤ 11, and the row sums of T equal A137398(n+2) (OEIS data) for every n ≤ 27. All T(n,k) are integers for n < 30.

**Points for the reviewer**

- *Minor.* The index is deliberately shifted from the literal "A137398(n+1)" to A137398(n+2). The reason is that A137398's offset was corrected in 2021: the old offset was 0, and the current one is 1. The listed numbers fix the shift unambiguously, since the row sums 1,2,7,22,74 are A137398's terms from the second on. The literal reading in today's offset is false at n = 0 (1 ≠ 0). This is the intended reading, but the Lean text departs from the verbatim OEIS text, so a reviewer should confirm it.
- *Note.* A137398 is encoded through its combinatorial name, reading "monotonic" as strictly increasing. Barry most likely matched the numbers or the g.f. instead. The two agree on everything checked: 6 terms in the kernel and 11 in Python. The reading of "monotonic" is forced for m ≥ 3 and fixed by a(2) = 1 at m = 2. A proof from the combinatorial definition is at least as strong as one about the numbers, so this is not weaker than intended.
- *Note.* Only the first sentence of the comment is formalized. "Diagonal sums are A188476" is the definition of A188476, not a conjecture, so excluding it is correct. There are no junk values in T: n+2−j ≥ k+1 ≥ 1 on the summation range, the natural subtraction n+2−j is exact, and 2^(j−1) with j = 0 is multiplied by j = 0.
- *Note.* Metadata only: the catalog tags this Riordan-type triangle identity as area "Discrete geometry".

## A195249: 3 × 3 lower triangles with neighbours differing by at most two: a(n) = 1047 n - 1459 for n > 2 (A195249)

Verdict of the pre-review: **faithful**. Result: [oeis-a195249](../../results/oeis-a195249/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A195249.lean`](../../lean/Math0/Statements/OEIS/A195249.lean).

**The conjecture as stated in OEIS**

> %F A195249 Empirical: a(n) = 1047*n - 1459 for n>2.  [R. H. Hardin, Sep 13 2011]  (Name: "Number of lower triangles of a 3 X 3 0..n array with each element differing from all of its diagonal, vertical, antidiagonal and horizontal neighbors by two or less." Offset 1. Also in %F: "Conjectures from _Colin Barker_, May 06 2018: G.f.: x*(64 + 601*x + 288*x^2 + 94*x^3) / (1 - x)^2. a(n) = 2*a(n-1) - a(n-2) for n>4.")

**The frozen Lean statement**

```lean
def statement : Prop := ∀ n : ℕ, 2 < n → (a n : ℤ) = 1047 * n - 1459

-- dependencies
def cell : Fin 6 → ℕ × ℕ := ![(0, 0), (1, 0), (1, 1), (2, 0), (2, 1), (2, 2)]
def Adj (p q : ℕ × ℕ) : Prop :=
  p ≠ q ∧ p.1 ≤ q.1 + 1 ∧ q.1 ≤ p.1 + 1 ∧ p.2 ≤ q.2 + 1 ∧ q.2 ≤ p.2 + 1
def near (x y : ℕ) : Prop := x ≤ y + 2 ∧ y ≤ x + 2
def Valid (v : Fin 6 → ℕ) : Prop := ∀ i j : Fin 6, Adj (cell i) (cell j) → near (v i) (v j)
def a (n : ℕ) : ℕ :=
  ∑ x0 ∈ range (n + 1), ∑ x1 ∈ range (n + 1), ∑ x2 ∈ range (n + 1), ∑ x3 ∈ range (n + 1),
    ∑ x4 ∈ range (n + 1), ∑ x5 ∈ range (n + 1), if Valid ![x0, x1, x2, x3, x4, x5] then 1 else 0
(Barker's g.f. and recurrence are separate defs statementBarkerGF / statementBarkerRec, not part of `statement`.)
```

**What the Lean statement says**

Fill the six cells (i,j), j ≤ i < 3, of the lower triangle of a 3×3 array with integers in {0,…,n}. Call a filling valid if any two distinct cells whose row indices and column indices each differ by at most 1 (king-adjacent) hold entries differing by at most 2. The claim is that for every n ≥ 3, the number of valid fillings is 1047n − 1459, as an equality in ℤ.

**What the kernel checks against the OEIS data**

a_data kernel-checks all 38 listed terms a(1..38) through the pruned evaluator aL (proved equal to a). a_small evaluates a(1) = 64 and a(2) = 729 directly from the definition. image_cell and cell_injective confirm the six positions, and valid_iff makes the ten adjacent pairs explicit. Thirty-six of the checked terms lie in the range n > 2, so any other adjacency or triangle shape would show up as a different slope or intercept. The definitions are pinned.

**Points for the reviewer**

- *Note.* Only Hardin's formula is in `statement`. Barker's g.f. and recurrence are recorded as separate Props. Both follow from Hardin's formula together with a(1) = 64 and a(2) = 729, which are kernel-checked (the g.f. coefficients give 64, 729, 1682, 2729, then slope 1047). Settling `statement` therefore leaves no part of the entry's conjectural content unsettled.
- *Note.* Only adjacencies inside the triangle are constrained, which is the natural reading of counting "lower triangles". The range n > 2 and the integer target 1047n − 1459 in ℤ match the text exactly, with no truncated subtraction.

## A201060: Repdigits with repdigit digital product are repunits from a(16) = 1111 on (A201060)

Verdict of the pre-review: **faithful**. Result: [oeis-a201060](../../results/oeis-a201060/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A201060.lean`](../../lean/Math0/Statements/OEIS/A201060.lean).

**The conjecture as stated in OEIS**

> %C A201060 Conjecture: a(n) is repunit for n >= 16. (_Jaroslav Krizek_, Nov 26 2011). Name: "Repdigit numbers with repdigit digital product." Offset 1; data 0,1,2,...,9,11,22,33,111,222,1111,11111,...,1111111111111111111 (31 terms). Local mirror (#11, Mar 30 2012) is identical to oeisdata main.

**The frozen Lean statement**

```lean
def statement : Prop := ∀ n : ℕ, 16 ≤ n → IsRepunit (a n)

where
def IsRepdigit (m : ℕ) : Prop := ∀ x ∈ Nat.digits 10 m, ∀ y ∈ Nat.digits 10 m, x = y
def digitProd (m : ℕ) : ℕ := if m = 0 then 0 else (Nat.digits 10 m).prod
def IsTerm (m : ℕ) : Prop := IsRepdigit m ∧ IsRepdigit (digitProd m)
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)
def IsRepunit (m : ℕ) : Prop := ∀ d ∈ Nat.digits 10 m, d = 1
```

**What the Lean statement says**

List, in increasing order and starting at index 1, the natural numbers m (0 included) all of whose decimal digits are equal and whose product of decimal digits (taken to be 0 for m = 0) also has all decimal digits equal. Then for every index n >= 16, the n-th number in this list has all decimal digits equal to 1.

**What the kernel checks against the OEIS data**

a_data checks all 31 listed terms a(1..31) in the kernel. It shows that the repdigits below 10^19 are exactly 0 and rep d k (isRepdigit_iff_mem_repList), filters them, and transfers the result to Nat.nth (map_nth_eq_of_filter). infinite_isTerm proves the set is infinite, so Nat.nth is the genuine increasing enumeration. The check confirms the offset (a 1 = 0, a 16 = 1111), that 0 counts as a repdigit, and the digit-product convention. IsRepunit is not data-checked, but it is a direct transcription.

**Points for the reviewer**

- *Note.* digitProd 0 = 0, not the empty product 1. Both values are repdigits, so the sequence does not change, and a_data confirms a(1) = 0.
- *Note.* IsRepunit 0 holds vacuously because Nat.digits 10 0 = []. This cannot matter: a n >= a 16 = 1111 for n >= 16, and a is strictly increasing because the set is infinite.
- *Note.* Since every repunit is a term, the statement amounts to saying that no repdigit d...d (2 <= d <= 9) with >= 4 digits has a repdigit digit product d^k. That is the intended content, and the Lean statement is exactly 'all terms from index 16 on are repunits', with no extra hypotheses.

## A209802: Positivity of the exponential Mertens function (A209802)

Verdict of the pre-review: **faithful**. Result: [oeis-a209802](../../results/oeis-a209802/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A209802.lean`](../../lean/Math0/Statements/OEIS/A209802.lean).

**The conjecture as stated in OEIS**

> %C A209802 Analog of Mertens's function, A002321; conjecture: a(n) > 0.  [_Reinhard Zumkeller_, Mar 13 2012; %N Partial sums of exponential Möbius function, A166234; %O 1,2. A166234: Multiplicative, a(p^e) = mu(e) for any prime power p^e (e>=1)]

**The frozen Lean statement**

```lean
def statement : Prop := ∀ n : ℕ, 1 ≤ n → 0 < a n

where
def muE (n : ℕ) : ℤ := n.factorization.prod fun _ e => moebius e
def a (n : ℕ) : ℤ := ∑ k ∈ Icc 1 n, muE k
```

**What the Lean statement says**

Let mu_e be the multiplicative function with mu_e(p^e) = mu(e) for every prime power p^e with e >= 1, so mu_e(1) = 1. Then for every n >= 1, the partial sum mu_e(1) + ... + mu_e(n) is strictly positive.

**What the kernel checks against the OEIS data**

muE_data checks the 91 listed terms of A166234. a_data checks all 72 listed terms of A209802, and a_ten_hundred checks a(10) = 4 and a(100) = 34 from the Greathouse comment. All run by decide +kernel through a trial-division copy aC that is proved equal to a (a_eq_aC), so the checks apply to the frozen definition itself. The muE data include the zero value at 16 = 2^4 (mu(4) = 0) and negative values at squares, so mu applied to exponents is pinned.

**Points for the reviewer**

- *Note.* a is Z-valued, so there is no truncation, and the empty sum a 0 = 0 is excluded by 1 <= n, matching offset 1. muE 0 = 1 is junk but is never used, since the sum runs over Icc 1 n. The statement is exactly 'a(n) > 0 for every term'.

## A211343: A211343: positive entries are smallest parts of consecutive-part partitions; last positive column is A109814(n)

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a211343](../../results/oeis-a211343/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A211343.lean`](../../lean/Math0/Statements/OEIS/A211343.lean).

**The conjecture as stated in OEIS**

> %C A211343 From _Omar E. Pol_, Apr 30 2017: (Start) Conjecture 1: T(n,k) is the smallest part of the partition of n into k consecutive parts, if T(n,k) > 0. Conjecture 2: the last positive integer in the row n is in the column A109814(n). (End). Name: "Triangle read by rows: T(n,k), n >= 1, k >= 1, in which column k lists the positive integers interleaved with k-1 zeros, and the first element of column k is in row k(k+1)/2." A109814: "a(n) is the largest k such that n can be written as sum of k consecutive positive integers."

**The frozen Lean statement**

```lean
def statement : Prop :=
  (∀ n k : ℕ, 1 ≤ n → InRow n k → 0 < T n k →
    (∃ p : n.Partition, HasConsecutiveParts k p) ∧
    ∀ p : n.Partition, HasConsecutiveParts k p → IsLeast {x | x ∈ p.parts} (T n k)) ∧
  (∀ n : ℕ, 1 ≤ n → IsGreatest {k | InRow n k ∧ 0 < T n k} (A109814 n))

where
def column (k j : ℕ) : ℕ := if j % k = 0 then j / k + 1 else 0
def InRow (n k : ℕ) : Prop := 1 ≤ k ∧ k * (k + 1) / 2 ≤ n
def T (n k : ℕ) : ℕ := if InRow n k then column k (n - k * (k + 1) / 2) else 0
def HasConsecutiveParts {n : ℕ} (k : ℕ) (p : n.Partition) : Prop :=
  ∃ m, p.parts = (Multiset.range k).map (fun i => m + i)
def IsConsecSumBdd (n k : ℕ) : Prop := ∃ m ∈ Finset.Icc 1 n, ∑ i ∈ Finset.range k, (m + i) = n
def A109814 (n : ℕ) : ℕ := Nat.findGreatest (IsConsecSumBdd n) n
```

**What the Lean statement says**

Let T(n,k), for k >= 1 and k(k+1)/2 <= n, be ((n - k(k+1)/2)/k) + 1 when k divides n - k(k+1)/2, and 0 otherwise. (1) For every n >= 1 and every such k with T(n,k) > 0, n has a partition into the k consecutive parts m, m+1, ..., m+k-1, and T(n,k) is the smallest part of every such partition. (2) For every n >= 1, the largest k with k(k+1)/2 <= n and T(n,k) > 0 equals A109814(n), the largest k such that n is a sum of k consecutive positive integers.

**What the kernel checks against the OEIS data**

a_data checks all 94 listed terms (rows 1..24) of the flattened triangle in the kernel, and row_data checks the same rows row by row against the %e example. A109814_data checks the first 40 listed A109814 terms. A109814_isGreatest proves that, for n >= 1, the bounded findGreatest equals the unbounded OEIS definition. Together these pin down T (including column start rows and zero interleaving) and A109814. HasConsecutiveParts is not data-checked, but it is a direct transcription; positivity of parts comes from Nat.Partition.

**Points for the reviewer**

- *Note.* Conjecture 1 is encoded only in the stated direction: T(n,k) > 0 implies a k-consecutive-part partition exists with smallest part T(n,k). The converse (T(n,k) = 0 implies no such partition) is not claimed. This follows the wording 'if T(n,k) > 0'.
- *Note.* 'The partition' is read as existence plus 'every such partition has smallest part T(n,k)'. This is equivalent to the uniqueness-flavoured reading, because a partition into k consecutive parts is determined by n and k.
- *Note.* Conjecture 2 is read as 'A109814(n) is the greatest column of row n with a positive entry'. That matches 'the last positive integer in the row n is in the column A109814(n)'. T's junk value 0 outside the triangle is never used, because InRow is required everywhere.

## A215010: An equiangular decagon with sides in arithmetic progression (A215010)

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a215010](../../results/oeis-a215010/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A215010.lean`](../../lean/Math0/Statements/OEIS/A215010.lean).

**The conjecture as stated in OEIS**

> %C A215010 Conjecture: hexagons are the only simple convex polygons with equal interior angles with such property, due to the fact that cos(Pi/3) = 1/2.  [_Robin Garcia_, Jul 31 2012; %N Integer side lengths in arithmetic progression of simple convex hexagons with equal interior angles. Sequence gives the values of m for sides of lengths t+m*d, counterclockwise, for the two primitive solutions. %e t = d = 1 gives (1, 6, 2, 4, 3, 5) and (1, 6, 3, 2, 5, 4)]

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ (N t d : ℕ), 1 ≤ d → ∀ σ : Equiv.Perm (Fin N),
    IsEquiangularPolygon N (fun k => t + (σ k : ℕ) * d) → N = 6

where
noncomputable def edgeDir (N k : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * k / N)
def IsEquiangularPolygon (N : ℕ) (s : Fin N → ℕ) : Prop :=
  3 ≤ N ∧ (∀ k, 0 < s k) ∧ ∑ k : Fin N, (s k : ℂ) * edgeDir N k = 0
```

**What the Lean statement says**

Suppose N >= 3, t >= 0 and d >= 1 are integers, and the N numbers t, t+d, ..., t+(N-1)d, all positive, are arranged in some order as consecutive side lengths s_0, ..., s_{N-1}. If the edge vectors s_k * exp(2*pi*i*k/N) sum to zero, so that these sides close up into an equiangular convex N-gon, then N = 6.

**What the kernel checks against the OEIS data**

a_data checks all 12 listed terms by computing the closing orderings m of 0..5 for N = 6 (via hexCloses), keeping those in the normal form m0 = 0, m1 > m5, in lexicographic order. primitiveSolutions_length shows there are exactly 2. hexCloses_iff proves that hexCloses is equivalent to the closing condition of IsEquiangularPolygon at N = 6, and an example checks the entry's hexagon (1,6,2,4,3,5) against IsEquiangularPolygon. The data therefore pin the N = 6 case of the polygon predicate and the reading 'm is a permutation of 0..N-1'. They do not test the predicate for N != 6, the case the refutation uses (N = 10). The general-N predicate is the standard characterization, justified in the docstring but not proved in the file.

**Points for the reviewer**

- *Minor.* 'Simple convex polygon with equal interior angles' is encoded through the edge-vector characterization: positive sides, sum of s_k * zeta^k = 0, zeta = exp(2*pi*i/N), N >= 3. It is not encoded as a geometric definition. The refutation needs only the direction 'predicate implies a genuine polygon', and that direction holds: positive sides whose direction turns by 2*pi/N at each vertex, with total turning 2*pi, form a strictly convex simple polygon with every interior angle (N-2)*pi/N. The data check validates the predicate only at N = 6. I numerically confirmed the decagon witness (1,4,5,8,9,2,3,6,7,10) used by the result: |sum| ~ 5e-15.
- *Note.* 'Such property' is read as: the side lengths are the N terms t + m*d, m = 0..N-1, of an integer arithmetic progression, in some order. The entry's own m-lists (permutations of 0..5) support this reading. Requiring the sides in progression order would make the property impossible for every N, so that reading cannot be the intended one. d >= 1 rightly excludes d = 0, under which regular polygons would make the conjecture trivially false and a refutation vacuous. Negative d is equivalent to reading the polygon in the other direction, and t >= 1 is forced by positivity. Restricting to natural t and d only narrows the universal claim, so a counterexample in N also refutes the integer version.
- *Note.* The refuting witness (N = 10, t = d = 1, sides a permutation of 1..10) lies squarely inside the author's setting. The known theorem (Ball 2002; Woeginger, Amer. Math. Monthly 2013; OEIS A118887) says such polygons exist exactly when N has at least two distinct prime factors. So the result refutes the conjecture as meant, not some degenerate reading.

## A223395: A223395: walks on the 4 x 4 grid graph satisfy Hardin's recurrence, Barker's g.f. and closed form

Verdict of the pre-review: **faithful**. Result: [oeis-a223395](../../results/oeis-a223395/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A223395.lean`](../../lean/Math0/Statements/OEIS/A223395.lean).

**The conjecture as stated in OEIS**

> %F A223395 Empirical: a(n) = 3*a(n-1) + 2*a(n-2) - 4*a(n-3). (R. H. Hardin, Mar 19 2013) %F A223395 Conjectures from _Colin Barker_, Aug 20 2018: (Start) G.f.: 8*x*(2 - 3*x^2) / ((1 - x)*(1 - 2*x - 4*x^2)). a(n) = (8 + (11-5*sqrt(5))*(1-sqrt(5))^n + (1+sqrt(5))^n*(11+5*sqrt(5))) / 5. (End). Name: "4 X 4 square grid graph coloring a rectangular array: number of n X 1 0..15 arrays where 0..15 label nodes of the square grid graph and every array movement to a horizontal or vertical neighbor moves along an edge of this graph." Offset 1.

**The frozen Lean statement**

```lean
def statementRec : Prop :=
  ∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 3 * a (n - 1) + 2 * a (n - 2) - 4 * a (n - 3)
def statementGF : Prop :=
  (1 - PowerSeries.X) * (1 - 2 * PowerSeries.X - 4 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) =
    8 * PowerSeries.X * (2 - 3 * PowerSeries.X ^ 2)
def statementClosedForm : Prop :=
  ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
    (8 + (11 - 5 * Real.sqrt 5) * (1 - Real.sqrt 5) ^ n +
      (1 + Real.sqrt 5) ^ n * (11 + 5 * Real.sqrt 5)) / 5
def statement : Prop := statementRec ∧ statementGF ∧ statementClosedForm

where
def Adj (i j : Fin 16) : Prop :=
  (i.val / 4 = j.val / 4 ∧ (i.val % 4 + 1 = j.val % 4 ∨ j.val % 4 + 1 = i.val % 4)) ∨
    (i.val % 4 = j.val % 4 ∧ (i.val / 4 + 1 = j.val / 4 ∨ j.val / 4 + 1 = i.val / 4))
def Valid {n : ℕ} (f : Fin n → Fin 16) : Prop := ∀ i j : Fin n, i.val + 1 = j.val → Adj (f i) (f j)
def a (n : ℕ) : ℕ := Fintype.card {f : Fin n → Fin 16 // Valid f}
```

**What the Lean statement says**

Let a(n) be the number of sequences of n nodes of the 4x4 grid graph in which each pair of consecutive nodes is joined by an edge (that is, walks with n vertices). Then (i) a(n) = 3a(n-1) + 2a(n-2) - 4a(n-3) for every n >= 4. (ii) In Z[[x]], (1-x)(1-2x-4x^2) * sum_{n>=1} a(n) x^n = 8x(2-3x^2). (iii) a(n) = (8 + (11-5√5)(1-√5)^n + (1+√5)^n(11+5√5))/5 for every n >= 1.

**What the kernel checks against the OEIS data**

adj_iff_entry checks in the kernel that Adj equals the neighbour list printed in the entry's EXAMPLE section (so the graph has no loops and the labelling matches). a_data checks all 24 listed terms a(1..24) through the transfer-matrix version aL, which a_eq_ancomputes is proved equal to a for every n (a_eq_aL). a(1)=16 and a(2)=48 confirm that loops are excluded and walks are directed. The definitions are fully pinned down.

**Points for the reviewer**

- *Note.* Hardin's recurrence gives no range. The Lean statement takes n >= 4, the first n for which a(n-3) is a term at offset 1. Natural-number subtraction is safe here, and the identity is stated in Z.
- *Note.* The g.f. is read as sum_{n>=1} a(n) x^n, masking the junk a 0 = 1. The denominator is cleared, which is an equivalent form since its constant term is 1, making it a unit in Z[[x]]. The coefficients match Barker's text exactly.
- *Note.* statement is the conjunction of all three claims, which is the strongest reading. Given the 24 checked terms, the three are mutually equivalent, so a proof settles each one.

## A229159: Every odd prime is a side of a Heronian triangle (A229159)

Verdict of the pre-review: **faithful**. Result: [oeis-a229159](../../results/oeis-a229159/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A229159.lean`](../../lean/Math0/Statements/OEIS/A229159.lean).

**The conjecture as stated in OEIS**

> %C A229159 "Conjecture: for all prime p > 2 there exists an integer-sided triangle with integer area where at least one side is of length p." (_Michel Lagneau_, Sep 17 2013; entry name: "Smallest integer areas of integer-sided triangles where at least one side is of length prime(n).", offset 1, a(1)=0)

**The frozen Lean statement**

```lean
def IsIntTriangle (x y z A : ℕ) : Prop :=
  x < y + z ∧ y < x + z ∧ z < x + y ∧
    16 * (A : ℤ) ^ 2 =
      ((x : ℤ) + y + z) * (-(x : ℤ) + y + z) * ((x : ℤ) - y + z) * ((x : ℤ) + y - z)

def statement : Prop :=
  ∀ p : ℕ, p.Prime → 2 < p →
    ∃ x y z A : ℕ, IsIntTriangle x y z A ∧ (x = p ∨ y = p ∨ z = p)

(Auxiliary, not used by statement: areas m = {A | ∃ x y z, IsIntTriangle x y z A ∧ (x = m ∨ y = m ∨ z = m)}, prime n = Nat.nth Nat.Prime (n - 1), a n = sInf (areas (prime n)).)
```

**What the Lean statement says**

For every prime p > 2 there are natural numbers x, y, z, A such that x, y, z satisfy the strict triangle inequalities (a non-degenerate triangle, so all sides are at least 1), the Heron identity 16A^2 = (x+y+z)(-x+y+z)(x-y+z)(x+y-z) holds over the integers (that is, the area is the natural number A), and one of x, y, z equals p.

**What the kernel checks against the OEIS data**

a_one proves a(1) = 0 by hand (no Heronian triangle has a side of length 2). table_ok/a_table/a_data kernel-check a(1..19) = 0, 6, 6, 42, 66, 24, 36, 114, 966, 60, 930, 114, 126, 1290, 4230, 90, 1770, 330, 2814. Each value has a witness triangle and a certified exhaustive lower-bound search (lbCheck, proved sound by scan_spec/lbCheck_spec), so the check really determines the minimum. oeis_errata proves a(20) ≤ 11928, a(25) ≤ 396, a(29) ≤ 330, a(32) ≤ 6288 and a(40) ≤ 2970, all below the listed values. These checks run through `a`, which is built from the same IsIntTriangle the statement uses, so they pin down the triangle/area predicate, including the exclusion of degenerate triangles that a(1) = 0 requires. The statement itself does not mention `a`.

**Points for the reviewer**

- *Note.* The conjecture is a pure existence claim and the Lean statement matches it exactly: the same quantifier, the same range p > 2, and 'at least one side' encoded as x = p ∨ y = p ∨ z = p. Requiring non-degenerate triangles agrees with the entry's a(1) = 0. Dropping that requirement would not change the content, since (p, p, 2p) would then also satisfy the claim trivially.
- *Note.* The claim follows at once from the classical right triangle (p, (p^2-1)/2, (p^2+1)/2), whose area p(p^2-1)/4 is an integer for odd p. The catalogue correctly classes it as a known result.
- *Note.* Several listed OEIS terms (a(20), a(25), a(29), a(32), a(40)) are not minimal: the Maple program only searches sides up to 500 and returns the first triangle it finds. This affects the listed data only, not the conjecture, and it is why the kernel data check stops at n = 19.

## A242396: Stephan's conjectured g.f. for A242396 is false (first failure at n = 97)

Verdict of the pre-review: **faithful**. Result: [oeis-a242396](../../results/oeis-a242396/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A242396.lean`](../../lean/Math0/Statements/OEIS/A242396.lean).

**The conjecture as stated in OEIS**

> %F A242396 G.f., conjectured: (-2*x^14 + 4*x^13 + 2*x^12 + 2*x^11 + 2*x^10 + 2*x^9 + 2*x^8 + 4*x^7 + 2*x^6 + 2*x^5 + 2*x^4 + 2*x^3 + 2*x^2 + 4*x)/(x^14 - x^13 - x + 1). - _Ralf Stephan_, May 18 2014. (Also: %F Asymptotics from g.f.: a(n) ~ 30/13 * n. - _Ralf Stephan_, May 18 2014.) Name: "Number of rows of equilateral triangles (sides length = 1) that intersect the circumference of a circle of radius n centered at (0,0) or (1/2,0)." Offset 1. Author's Small Basic program: r6 = n*sin(30°)/(√3/2); a = 4*round(r6) if frac(r6) > 0.5 else 2*(2*round(r6)+1).

**The frozen Lean statement**

```lean
open PowerSeries in
def statement : Prop :=
  PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (X ^ 14 - X ^ 13 - X + 1) =
    -2 * X ^ 14 + 4 * X ^ 13 + 2 * X ^ 12 + 2 * X ^ 11 + 2 * X ^ 10 + 2 * X ^ 9 + 2 * X ^ 8 +
      4 * X ^ 7 + 2 * X ^ 6 + 2 * X ^ 5 + 2 * X ^ 4 + 2 * X ^ 3 + 2 * X ^ 2 + 4 * X

where
def RowMeets (c : ℝ) (n : ℕ) (j : ℤ) : Prop :=
  ∃ x y : ℝ, (x - c) ^ 2 + y ^ 2 = (n : ℝ) ^ 2 ∧ (j : ℝ) * (√3 / 2) ≤ y ∧ y ≤ ((j : ℝ) + 1) * (√3 / 2)
def MeetsInt (n : ℕ) (j : ℤ) : Prop :=
  (j ≤ 0 ∨ 3 * j ^ 2 ≤ 4 * (n : ℤ) ^ 2) ∧ (0 ≤ j + 1 ∨ 3 * (j + 1) ^ 2 ≤ 4 * (n : ℤ) ^ 2)
def a (n : ℕ) : ℕ :=
  ((Finset.range (4 * n + 5)).filter (fun i : ℕ => MeetsInt n ((i : ℤ) - (2 * n + 2)))).card
-- theorem a_eq_ncard (c : ℝ) (n : ℕ) : a n = {j : ℤ | RowMeets c n j}.ncard
-- (statement_asymptotic, a(n) ~ 30/13 n, is defined separately and is NOT part of statement)
```

**What the Lean statement says**

Let a(n) be the number of integers j such that the closed horizontal strip j·√3/2 <= y <= (j+1)·√3/2 meets the circle of radius n centred on the x-axis. a_eq_ncard proves this count is independent of the centre's x-coordinate, and it equals 2⌊2n/√3⌋ + 2. The statement asserts the power-series identity (sum_{n>=1} a(n) x^n)·(x^14 - x^13 - x + 1) = -2x^14 + 4x^13 + 2x^12 + ... + 2x^2 + 4x in Z[[x]], which is equivalent to sum a(n) x^n = N(x)/D(x). The result proves this identity false.

**What the kernel checks against the OEIS data**

a_data checks all 61 listed terms a(1..61) in the kernel. a_eq_ncard proves that a n is the number of rows of the closed strip tiling that meet the circle centred at (c,0), for every real c (so for both (0,0) and (1/2,0)). The data does not reach the refuting index: the g.f. fits all 61 terms, and the first failure is at n = 97, where a(97) = 226 and the g.f. predicts 224. So fidelity beyond the data rests on the definition itself. I checked independently that the Lean count equals 2⌊2n/√3⌋+2 and equals the author's Small Basic program for every n (algebraically; numerically for n <= 399 with no mismatch), and that the g.f. coefficients first disagree at n = 97 (then 110, 123, ...).

**Points for the reviewer**

- *Note.* The refutation is at n = 97, beyond the 61 data terms, so the data check alone cannot pin it down. It does not depend on a Lean-only artefact, however: the Lean a(n) = 2⌊2n/√3⌋+2 coincides for every n with the author's own program (4·round(n/√3) if frac(n/√3) > 1/2, else 4·round(n/√3)+2). The values at n = 83, 84, 96, 97 are far from any floating-point rounding threshold (2·84/√3 = 96.995, 2·97/√3 = 112.006).
- *Note.* The geometric choices are fixed by the program and the sibling entries A242394/A242395: horizontal rows of height √3/2 with a boundary line through the centre, and closed strips. Closed vs open strips is immaterial for n >= 1 because 2n/√3 is irrational (no tangency). The centre ambiguity '(0,0) or (1/2,0)' is harmless, since the count is proved independent of the centre's x-coordinate.
- *Note.* Only the g.f. is formalized in statement. The derived claim 'a(n) ~ 30/13 n' is recorded separately as statement_asymptotic and is not refuted by the result. It is also false, since a(n) ~ (4/√3) n ≈ 2.3094 n versus 30/13 ≈ 2.3077, but it is a consequence of the g.f. rather than a separate conjecture.
- *Note.* The g.f. is read with offset 1 (sum_{n>=1} a(n) x^n, junk a 0 = 2 masked). The numerator is divisible by x and reproduces a(1) = 4, so this reading is correct. Clearing the denominator (constant term 1, a unit in Z[[x]]) is equivalent. In any case the true sequence is not eventually of the form a(n+13) = a(n) + 30 under any offset.
