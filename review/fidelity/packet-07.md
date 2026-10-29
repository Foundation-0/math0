# Fidelity review packet 07 of 11

Prepared on 29 Oct 2026 by an adversarial reviewing agent, not by a person. It is meant to make a human review of these statements quick: for each one it quotes the OEIS conjecture and the frozen Lean statement, restates the Lean in plain words, and lists anything a reviewer should look at. See [the index](README.md).

Statements in this packet: A300789, A308107, A308121, A308222, A308359, A320099, A323695, A326407, A326602, A328202.

## A300789: Domino-tileable Young diagrams are exactly the colour-balanced ones (A300789)

Verdict of the pre-review: **faithful**. Result: [oeis-a300789](../../results/oeis-a300789/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A300789.lean`](../../lean/Math0/Statements/OEIS/A300789.lean).

**The conjecture as stated in OEIS**

> %C A300789 "This sequence is conjectured to be the Heinz numbers of integer partitions in which the odd parts appear as many times in even as in odd positions." (_Gus Wiseman_, Mar 12 2018; name: "Heinz numbers of integer partitions whose Young diagram can be tiled by dominos.", offset 1; "The Heinz number of an integer partition (y_1,...,y_k) is prime(y_1)*...*prime(y_k).")

**The frozen Lean statement**

```lean
def parts (k : ℕ) : List ℕ := (k.primeFactorsList.map Nat.primeCounting).reverse
def youngDiagram (y : List ℕ) : Set (ℕ × ℕ) := {c | c.1 < y.length ∧ c.2 < y.getD c.1 0}
def IsDomino (d : Set (ℕ × ℕ)) : Prop := ∃ i j : ℕ, d = {(i, j), (i + 1, j)} ∨ d = {(i, j), (i, j + 1)}
def DominoTileable (S : Set (ℕ × ℕ)) : Prop :=
  ∃ D : Set (Set (ℕ × ℕ)), (∀ d ∈ D, IsDomino d) ∧ D.PairwiseDisjoint id ∧ ⋃₀ D = S
def IsTerm (k : ℕ) : Prop := 0 < k ∧ DominoTileable (youngDiagram (parts k))
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)
def OddPartsBalanced (y : List ℕ) : Prop :=
  ((Finset.range y.length).filter fun i => Even (i + 1) ∧ Odd (y.getD i 0)).card =
    ((Finset.range y.length).filter fun i => Odd (i + 1) ∧ Odd (y.getD i 0)).card
def IsConjTerm (k : ℕ) : Prop := 0 < k ∧ OddPartsBalanced (parts k)
noncomputable def b (n : ℕ) : ℕ := Nat.nth IsConjTerm (n - 1)

def statement : Prop := ∀ n : ℕ, 1 ≤ n → a n = b n
```

**What the Lean statement says**

Write each k ≥ 1 as the Heinz number of the partition whose parts are the prime indices of k (π(p) for each prime factor p, with multiplicity), listed in weakly decreasing order. Let a(n) be the n-th smallest such k whose Young diagram can be partitioned into disjoint dominoes (1×2 or 2×1). Let b(n) be the n-th smallest such k whose partition has as many odd parts in even positions as in odd positions (positions 1..m). The statement says a(n) = b(n) for every n ≥ 1. Both predicates require k > 0, so this is equivalent to: for every k ≥ 1, the Young diagram is domino-tileable iff the odd parts are balanced between even and odd positions.

**What the kernel checks against the OEIS data**

a_data and b_data kernel-check all 63 listed terms (1, 3, 4, …, 131) for both a and b, by a kernel-checked List.filter over 0..131 transferred to Nat.nth (map_nth_eq_of_filter). Tileability is decided by tileL, which isTerm_iff_isTermB proves equivalent to the set-theoretic DominoTileable, so the check is on the real definition. parts_example checks the entry's %e list of partitions for the first 15 terms, which pins down `parts` (π indexing with prime(1)=2, multiplicity, decreasing order). The definitions are pinned down well.

**Points for the reviewer**

- *Note.* Positions are counted with the parts in decreasing order. The entry's Maple and Mathematica programs use increasing order. Reversing a list of length m maps position i to m+1-i, which either keeps every parity (m odd) or swaps every parity (m even). The equality of the two counts is symmetric, so the condition is the same in both orders.
- *Note.* 'This sequence is conjectured to be [those] Heinz numbers' is encoded as equality of the two increasing enumerations a(n) = b(n) for all n ≥ 1. Both predicates exclude 0, so this equality is equivalent to equality of the two sets of terms, whether or not the sets are infinite. It therefore captures both directions of the intended characterization.
- *Note.* The Young diagram uses the English convention with rows y_1 ≥ y_2 ≥ …. Domino tileability does not depend on the drawing convention.

## A308107: A308107: Barker's rational generating function and order-15 recurrence for the sum of smallest sides of scalene integer triangles

Verdict of the pre-review: **faithful**. Result: [oeis-a308107](../../results/oeis-a308107/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A308107.lean`](../../lean/Math0/Statements/OEIS/A308107.lean).

**The conjecture as stated in OEIS**

> %F A308107 Conjectures from _Colin Barker_, May 13 2019: (Start)
> %F A308107 G.f.: x^9*(2 + 2*x + 2*x^2 + x^3) / ((1 - x)^4*(1 + x)^3*(1 + x^2)^2*(1 + x + x^2)^2).
> %F A308107 a(n) = -a(n-1) + 2*a(n-3) + 4*a(n-4) + 2*a(n-5) - a(n-6) - 5*a(n-7) - 5*a(n-8) - a(n-9) + 2*a(n-10) + 4*a(n-11) + 2*a(n-12) - a(n-14) - a(n-15) for n>15.
> %F A308107 (End)
> (Entry: "Sum of the smallest side lengths of all integer-sided scalene triangles with perimeter n.", _Wesley Ivan Hurt_, May 13 2019, offset 1. Entry unchanged on GitHub oeisdata, #14 Sep 12 2021.)

**The frozen Lean statement**

```lean
def statement : Prop :=
  (PowerSeries.mk (fun n => (a n : ℚ)) =
    X ^ 9 * (2 + 2 * X + 2 * X ^ 2 + X ^ 3) *
      ((1 - X) ^ 4 * (1 + X) ^ 3 * (1 + X ^ 2) ^ 2 * (1 + X + X ^ 2) ^ 2)⁻¹) ∧
  (∀ n : ℕ, 15 < n →
    (a n : ℤ) = -(a (n - 1) : ℤ) + 2 * (a (n - 3) : ℤ) + 4 * (a (n - 4) : ℤ) +
      2 * (a (n - 5) : ℤ) - (a (n - 6) : ℤ) - 5 * (a (n - 7) : ℤ) - 5 * (a (n - 8) : ℤ) -
      (a (n - 9) : ℤ) + 2 * (a (n - 10) : ℤ) + 4 * (a (n - 11) : ℤ) + 2 * (a (n - 12) : ℤ) -
      (a (n - 14) : ℤ) - (a (n - 15) : ℤ))

def a (n : ℕ) : ℕ :=
  ∑ t ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
      (fun t : ℕ × ℕ × ℕ => t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.2.2 < t.1 + t.2.1 ∧
        t.1 + t.2.1 + t.2.2 = n),
    t.1
```

**What the Lean statement says**

Let a(n) be the sum of k over all integer triples k < i < j with j < k + i and k + i + j = n, that is, the sum of the smallest sides of all scalene integer triangles of perimeter n (a(0) = 0). Then (1) Σ_{n>=0} a(n) x^n equals x^9(2+2x+2x^2+x^3)/((1-x)^4(1+x)^3(1+x^2)^2(1+x+x^2)^2) as formal power series over Q, and (2) for every n > 15 the stated order-15 linear recurrence holds in Z.

**What the kernel checks against the OEIS data**

a_data: all 61 listed terms a(1..61), computed through aFast, which a_eq_aFast proves equal to a for every n. The check is therefore about the stated definition. recurrence_data: the listed terms satisfy the recurrence for 16 <= n <= 61 (a transcription check). den_eq: the stated denominator expands to the recurrence's characteristic polynomial. genFun_iff: the g.f. clause is equivalent to A(x)·D(x) = x^9(2+2x+2x^2+x^3), because constantCoeff D = 1. The definition matches the entry's double-sum formula term for term: i from k+1 to floor((n-k-1)/2) gives i < j, and sign(floor((i+k)/(j+1))) = 1 iff j < i+k. I also checked the g.f. against a brute-force a(n) for n < 150.

**Points for the reviewer**

- *Note.* The value a(0) = 0 is outside the offset but harmless: the g.f. has zero constant term, and the recurrence for n > 15 uses only indices >= 1.
- *Note.* The order-15 recurrence follows from the g.f., since the numerator has degree 12 < 15. The conjunction is therefore exactly as strong as the g.f. claim, which matches Barker's pair of conjectures.

## A308121: A308121: for odd n > 1, row 2n is row n with its halves swapped

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a308121](../../results/oeis-a308121/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A308121.lean`](../../lean/Math0/Statements/OEIS/A308121.lean).

**The conjecture as stated in OEIS**

> %C A308121 From _Charlie Neder_, Jun 05 2019: "Conjecture: If n is odd, then row 2n can be obtained from row n by interchanging the first and second halves." (Entry by _Jamie Morken_, May 13 2019: "Irregular triangle read by rows: T(n,k) = A109395(n)*k-A076512(n)*A038566(n,k).", offset 1, "Row n has length A000010(n).")

**The frozen Lean statement**

```lean
def totatives (n : ℕ) : List ℕ := (List.range' 1 n).filter (fun r => Nat.Coprime r n)
def A109395 (n : ℕ) : ℕ := ((Nat.totient n : ℚ) / n).den
def A076512 (n : ℕ) : ℤ := ((Nat.totient n : ℚ) / n).num
def T (n k : ℕ) : ℤ := (A109395 n : ℤ) * k - A076512 n * ((totatives n).getD (k - 1) 0 : ℕ)
def row (n : ℕ) : List ℤ := (List.range (Nat.totient n)).map (fun i => T n (i + 1))

def statement : Prop :=
  ∀ n : ℕ, Odd n → 1 < n →
    ∃ A B : List ℤ, row n = A ++ B ∧ A.length = B.length ∧ row (2 * n) = B ++ A
```

**What the Lean statement says**

For n ≥ 1, let r_1 < … < r_φ(n) be the integers in [1, n] coprime to n. Let φ(n)/n = u/v in lowest terms. Define row n as the integer list (v·k − u·r_k), k = 1..φ(n). The claim: for every odd n > 1, row n splits into two halves A, B of equal length (row n = A ++ B), and row 2n equals B ++ A.

**What the kernel checks against the OEIS data**

a_data kernel-checks that rows 1..15 concatenated equal all 72 listed terms (%S/%T/%U). T_210_2 checks the entry's worked example T(210,2) = 35·2 − 8·11 = −18, which exercises the signed (ℤ) values and the reduced fraction at a composite n. statement_check_7 and statement_check_15 check rows 7/14 and 15/30 explicitly. The listed rows include non-squarefree and composite n (4, 6, 8, 9, 10, 12, 14, 15), so the num/den-of-reduced-fraction definitions of A076512/A109395 and the A038566 row convention (row 1 = [1]) are pinned down.

**Points for the reviewer**

- *Minor.* Reading choice on the range: the OEIS text says 'If n is odd', which includes n = 1, but the Lean statement requires 1 < n. At n = 1 the literal claim fails under any reading: row 1 = [0] has odd length and no halves, and row 2 = [1] is not a rearrangement of [0]. For odd n ≥ 3, φ(n) is even, so the halves are well defined. The file documents this exclusion, and it is the only reading under which the conjecture is meaningful. Still, the result settles the conjecture for odd n > 1 and not the literal 'all odd n' wording, which is (trivially) false at n = 1. A reviewer should accept this reading explicitly.
- *Note.* A109395 and A076512 are defined literally as Rat.den and Rat.num of φ(n)/n, as their OEIS names and comments say (A076512: 'Numerator of phi(n)/n', formula A000010/A009195). The getD default 0 in T is never reached, because row only uses k ≤ φ(n) = length of totatives n.

## A308222: Perimeters of primitive Heronian isosceles triangles: A308222(n) = 2 · A096033(n + 2)

Verdict of the pre-review: **faithful**. Result: [oeis-a308222](../../results/oeis-a308222/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A308222.lean`](../../lean/Math0/Statements/OEIS/A308222.lean).

**The conjecture as stated in OEIS**

> %F A308222 "a(n) = 2*A096033(n+2) (conjectured)." (Entry by _Peter Kagey_, May 16 2019; name: "Numbers that are the perimeter of a primitive Heronian isosceles triangle.", offset 1; comment: "A primitive Heronian triangle is a triangle with integer sides and area, where the side lengths do not share a common divisor." A096033: "Difference between leg and hypotenuse in primitive Pythagorean triangles.", offset 1: 1, 2, 8, 9, 18, …)

**The frozen Lean statement**

```lean
def heron (x y z : ℤ) : ℤ := (x + y + z) * (-x + y + z) * (x - y + z) * (x + y - z)
def IsHeronian (x y z : ℕ) : Prop :=
  x < y + z ∧ y < x + z ∧ z < x + y ∧ ∃ A : ℕ, 16 * (A : ℤ) ^ 2 = heron x y z
def IsPrimitive (x y z : ℕ) : Prop := Nat.gcd (Nat.gcd x y) z = 1
def IsIsosceles (x y z : ℕ) : Prop := x = y ∨ y = z ∨ x = z
def IsPerimeter (P : ℕ) : Prop :=
  ∃ x y z : ℕ, IsHeronian x y z ∧ IsPrimitive x y z ∧ IsIsosceles x y z ∧ x + y + z = P
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsPerimeter (n - 1)
def IsLegHypDiff (d : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ x ^ 2 + y ^ 2 = z ^ 2 ∧ Nat.gcd x y = 1 ∧ z = x + d
noncomputable def A096033 (n : ℕ) : ℕ := Nat.nth IsLegHypDiff (n - 1)

def statement : Prop := ∀ n : ℕ, 1 ≤ n → a n = 2 * A096033 (n + 2)
```

**What the Lean statement says**

Let a(n) be the n-th smallest number P (offset 1, each value counted once) that is the perimeter of a non-degenerate triangle with natural-number sides, gcd of the three sides equal to 1, integer area (16A^2 = Heron product for some natural A), and two equal sides. Let D(n) be the n-th smallest d (offset 1) such that some primitive Pythagorean triple (x, y, z), with x, y ≥ 1 and gcd(x, y) = 1, has z = x + d. The claim: a(n) = 2·D(n+2) for all n ≥ 1, i.e. the set of perimeters equals twice the set of leg–hypotenuse differences other than 1 and 2.

**What the kernel checks against the OEIS data**

a_data kernel-checks all 46 listed terms of A308222 (16, …, 3136) through a decision procedure (perimB) that perimB_iff proves equivalent to IsPerimeter. A096033_data kernel-checks the 52 listed terms of A096033 (1, 2, 8, 9, 18, …, 1849), using legHypB, which isLegHypDiff_iff/legHypB_iff prove equivalent to the definition. Together these pin down both definitions and the index shift: A096033(3) = 8 gives 16 = a(1), and A096033(4) = 9 gives 18 = a(2).

**Points for the reviewer**

- *Note.* Equilateral triangles count as isosceles here, but none has integer area, so this changes nothing. 'Primitive' is gcd(gcd(x,y),z) = 1, which matches the entry's comment. Perimeters arising from several triangles (e.g. 50) are counted once, which matches the listed data.
- *Note.* A096033 is encoded by its defining property (difference between a leg and the hypotenuse of a primitive Pythagorean triangle), not by Weimholt's characterization (odd squares and 2j^2). The characterization is proved in the file only for decidability. The statement is a pointwise equality of two increasing enumerations, which is equivalent to the set identity above.

## A308359: Fixed polyominoes with n cells and width n-2: T(n,n-2) = 8n^2 - 51n + 86 (A308359)

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a308359](../../results/oeis-a308359/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A308359.lean`](../../lean/Math0/Statements/OEIS/A308359.lean).

**The conjecture as stated in OEIS**

> %F A308359 "Conjecture: T(n,n-2) = 8*n^2 - 51*n + 86 for n >= 5." (Entry by _R. J. Mathar_, May 22 2019; name: "Triangle T(n,w) read by rows: the number of fixed polyominoes with n cells and width w of the convex hull.", offset 1; comment: "The sequence counts the fixed n-ominoes with prescribed bounding box width w and variable height w <= h <= n.")

**The frozen Lean statement**

```lean
def Adj (p q : ℕ × ℕ) : Prop :=
  (p.1 = q.1 ∧ (p.2 + 1 = q.2 ∨ q.2 + 1 = p.2)) ∨ (p.2 = q.2 ∧ (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1))
def Step (S : Finset (ℕ × ℕ)) (p q : ℕ × ℕ) : Prop := p ∈ S ∧ q ∈ S ∧ Adj p q
def IsConnected (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, Relation.ReflTransGen (Step S) p q
def IsPoly (n w : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  S.card = n ∧ (∃ p ∈ S, p.1 = 0) ∧ (∃ p ∈ S, p.2 = 0) ∧ S.sup Prod.fst + 1 = w ∧ IsConnected S
noncomputable def T (n w : ℕ) : ℕ := {S : Finset (ℕ × ℕ) | IsPoly n w S}.ncard

def statement : Prop :=
  ∀ n : ℕ, 5 ≤ n → (T n (n - 2) : ℤ) = 8 * (n : ℤ) ^ 2 - 51 * n + 86
```

**What the Lean statement says**

For every n ≥ 5, the number of n-cell edge-connected sets of grid cells, taken up to translation (each normalized to have min column 0 and min row 0) and spanning exactly n − 2 columns, with no condition on the number of rows, equals 8n^2 − 51n + 86 (compared in ℤ).

**What the kernel checks against the OEIS data**

a_data kernel-checks the first 23 listed terms (rows 1..6, then T(7,1) = 1 and T(7,2) = 66), including T(5,3) = 31 and T(6,4) = 68, the conjecture's n = 5 and n = 6 values. Every count goes through the computable Tbox, which T_eq_Tbox proves equal to the ncard definition (it also shows the set is finite, so ncard is not a junk 0), with connectivity decided by a flood fill proved equivalent to IsConnected. Independently, I enumerated fixed polyominoes by brute force (Python, column-span width, unrestricted height). This reproduces all 66 listed terms (rows 1..11), including T(n,n−2) = 31, 68, 121, 190, 275, 376, 493 for n = 5..11, each equal to 8n^2 − 51n + 86. The definitions are pinned down.

**Points for the reviewer**

- *Note.* The entry's comment says the height ranges over w ≤ h ≤ n, but the entry contradicts this: T(3,3) = 1, T(n,n−1) = 4n−8 ('width n-1 and height 2'), and the row sums equal A001168. Under the comment's reading, T(n,n−2) would be 0 for n ≥ 6, because height ≤ n+1−w = 3 < n−2. So the Lean choice of unrestricted height is the only reading consistent with the data, and it reproduces every listed term. The choice between width and height does not matter, since transposition gives the same counts.
- *Note.* The truncated subtraction n − 2 is harmless because n ≥ 5. The right side is computed in ℤ, so it is not truncated. The 'width of the convex hull' of a union of unit squares equals the column span max x − min x + 1, which is what IsPoly encodes (min x = 0).

## A320099: Kagey's order-10 recurrence for no-leaf subgraphs of the 5 × n grid holds

Verdict of the pre-review: **faithful**. Result: [oeis-a320099](../../results/oeis-a320099/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A320099.lean`](../../lean/Math0/Statements/OEIS/A320099.lean).

**The conjecture as stated in OEIS**

> %F A320099 Conjecture: a(n) = 103*a(n-1) + 1063*a(n-2) - 1873*a(n-3) - 20274*a(n-4) + 44071*a(n-5) - 10365*a(n-6) - 20208*a(n-7) + 5959*a(n-8) + 2300*a(n-9) - 500*a(n-10) for n > 10.  (Entry and conjecture by _Peter Kagey_, Oct 05 2018; rev #20, Jun 09 2019, unchanged upstream.) Definition: %N Number of no-leaf subgraphs of the 5 X n grid. %C Also, the number of ways to lay unit-length matchsticks on a 5 X n grid of points in such a way that no end is "orphaned". %O 1,2

**The frozen Lean statement**

```lean
abbrev grid (n : ℕ) : SimpleGraph (Fin 5 × Fin n) := pathGraph 5 □ pathGraph n
def deg {n : ℕ} (S : Finset (Sym2 (Fin 5 × Fin n))) (v : Fin 5 × Fin n) : ℕ := #{e ∈ S | v ∈ e}
def a (n : ℕ) : ℕ := #{S ∈ (grid n).edgeFinset.powerset | ∀ v, deg S v ≠ 1}

def statement : Prop :=
  ∀ n : ℕ, 10 < n →
    (a n : ℤ) = 103 * (a (n - 1) : ℤ) + 1063 * (a (n - 2) : ℤ) - 1873 * (a (n - 3) : ℤ)
      - 20274 * (a (n - 4) : ℤ) + 44071 * (a (n - 5) : ℤ) - 10365 * (a (n - 6) : ℤ)
      - 20208 * (a (n - 7) : ℤ) + 5959 * (a (n - 8) : ℤ) + 2300 * (a (n - 9) : ℤ)
      - 500 * (a (n - 10) : ℤ)
```

**What the Lean statement says**

Let G_n be the grid graph on the 5-by-n array of points (two points adjacent iff they agree in one coordinate and differ by 1 in the other). Let a(n) be the number of edge subsets S of G_n such that no vertex lies on exactly one edge of S. Then for every integer n > 10, a(n) = 103a(n-1) + 1063a(n-2) - 1873a(n-3) - 20274a(n-4) + 44071a(n-5) - 10365a(n-6) - 20208a(n-7) + 5959a(n-8) + 2300a(n-9) - 500a(n-10), as an identity of integers.

**What the kernel checks against the OEIS data**

a_data checks all 15 listed terms a(1..15) (index i+1, matching offset 1) with decide +kernel. It goes through a_eq_T and a_eq_fastA, which prove for every n that a n equals the (noH,noH) entry of T^n for the 32x32 column transfer matrix, so the check is on the actual definition `a`, not on a separate evaluator. statement_check_listed verifies the recurrence at n = 11..15. I compared the Lean list with the OEIS %S/%T/%U data by script: identical (15/15). The data pins down the definition. a(1) = 1 rules out readings where subgraphs may drop vertices (that would give 32 for the empty edge set) and readings where '5 X n grid' means 5 x n cells (6 x (n+1) points). a(2) = 50 and the remaining terms confirm the 'no degree-1 vertex' edge-set count.

**Points for the reviewer**

- *Note.* 'Subgraph' is encoded as a spanning edge subset (all vertices kept, isolated vertices allowed). That is the matchstick reading in the entry's comment, and a(1) = 1 together with all 15 terms forces it, so this is not an interpretive gap.
- *Note.* a 0 = 1 (the empty grid) is a junk value outside offset 1. It is never used, because n > 10 makes every index n-k with 1 <= k <= 10 an exact natural subtraction that is >= 1. The range 'n > 10' and all ten coefficients, with their signs, match the OEIS text exactly.

## A323695: Odd terms of A323695 occur only at n = k(k+2)

Verdict of the pre-review: **faithful**. Result: [oeis-a323695](../../results/oeis-a323695/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A323695.lean`](../../lean/Math0/Statements/OEIS/A323695.lean).

**The conjecture as stated in OEIS**

> %C A323695 Odd terms occur only at n = k*(k+2) for k >= 0 (conjecture);  (_Paul D. Hanna_, Feb 23 2019; rev #24, Dec 15 2024, unchanged upstream.) Definition: %N G.f.: Sum_{n>=0} x^n * (1 - x^(n+1))^n / (1 + x^(n+1))^(n+1). %O 0,3. (The FORMULA section separately lists, without the word conjecture: 'a(n*(n+2)) = 1 (mod 2) for n >= 0.')

**The frozen Lean statement**

```lean
noncomputable def summand (m : ℕ) : PowerSeries ℤ :=
  X ^ m * (1 - X ^ (m + 1)) ^ m * invOfUnit ((1 + X ^ (m + 1)) ^ (m + 1)) 1
noncomputable def A : PowerSeries ℤ :=
  mk fun N => ∑ m ∈ Finset.range (N + 1), coeff N (summand m)
-- HasSum summand A proved (hasSum_summand)
def a (N : ℕ) : ℤ := coeffA N   -- explicit binomial formula; theorem a_eq_coeff : a N = coeff N A

def statement : Prop :=
  ∀ n : ℕ, Odd (a n) → ∃ k : ℕ, n = k * (k + 2)
```

**What the Lean statement says**

Let a(N) be the integer coefficient of x^N in the formal power series sum over m >= 0 of x^m (1 - x^(m+1))^m / (1 + x^(m+1))^(m+1), for N >= 0. For every N >= 0, if a(N) is odd then N = k(k+2) for some integer k >= 0 (equivalently, N+1 is a perfect square).

**What the kernel checks against the OEIS data**

a_data checks all 121 listed terms a(0..120) (index i+0, matching offset 0) with decide +kernel. `a` is a computable explicit formula, but a_eq_coeff proves a N = coeff N A for every N, and hasSum_summand proves that A is the X-adic sum of the OEIS summands, so the data check is a sanity check rather than what fixes the definition. I compared with the OEIS data by script: identical (121/121), signs included.

**Points for the reviewer**

- *Note.* The statement covers only the stated direction, odd => n = k(k+2), which is exactly what 'occur only at' says. The converse, a(k(k+2)) odd, appears in the entry's FORMULA section, not marked as a conjecture. It is not part of `statement`, so the result does not certify it, although the catalogued proof method (a(n) ≡ d(n+1) mod 2) would give it.
- *Note.* The summand inverse uses invOfUnit with unit 1, which is valid because (1+X^(m+1))^(m+1) has constant coefficient 1 (summand_spec proves the defining identity). k ranges over ℕ, matching 'k >= 0'. Odd on ℤ handles the negative terms correctly (e.g. -3, -93).

## A326407: Prime-Minesweeper on the A060734 array: a(n) < 6, and a(n) = 5 only at n = 6

Verdict of the pre-review: **faithful**. Result: [oeis-a326407](../../results/oeis-a326407/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A326407.lean`](../../lean/Math0/Statements/OEIS/A326407.lean).

**The conjecture as stated in OEIS**

> %C A326407 a(n) < 6 (conjectured). %C A326407 a(n) = 5 for n={6} (conjectured). [%C A326407 Set of n such that a(n) = 4 is unbounded (conjectured). — not targeted]  (_Witold Tatkiewicz_, Oct 02 2019; rev #27, Mar 20 2020, unchanged upstream.) Definition: %N Minesweeper sequence of positive integers arranged on a 2D grid along a square array that grows by alternately adding a row at its bottom edge and a column at its right edge. %C Place positive integers on a 2D grid starting with 1 in the top left corner and continue along an increasing square array as in A060734. Replace each prime with -1 and each nonprime with the number of primes in adjacent grid cells around them. %O 1,1

**The frozen Lean statement**

```lean
def val (r c : ℕ) : ℕ := if r ≤ c then (c + 1) ^ 2 - r else r ^ 2 + 1 + c
def pos (n : ℕ) : ℕ × ℕ := ...   -- inverse of val; pos_val, val_pos proved
def near (x : ℕ) : List ℕ := if x = 0 then [0, 1] else [x - 1, x, x + 1]
def neighbours (n : ℕ) : List ℕ :=
  (near (pos n).1).flatMap fun i =>
    (near (pos n).2).filterMap fun j =>
      if (i, j) = pos n then none else some (val i j)
def a (n : ℕ) : ℤ :=
  if n.Prime then -1 else (((neighbours n).filter fun m => m.Prime).length : ℤ)

def statement : Prop :=
  (∀ n : ℕ, 1 ≤ n → a n < 6) ∧ (∀ n : ℕ, 1 ≤ n → (a n = 5 ↔ n = 6))
```

**What the Lean statement says**

Write the positive integers into the infinite quadrant array whose cell (row r, column c), both 0-indexed, holds (c+1)^2 - r if r <= c and r^2 + 1 + c if r > c. Every positive integer occupies exactly one cell. For n >= 1 let a(n) = -1 if n is prime, and otherwise the number of primes among the up to 8 king-move neighbours of n's cell that lie in the quadrant. Claim: (i) a(n) < 6 for all n >= 1, and (ii) for n >= 1, a(n) = 5 holds if and only if n = 6.

**What the kernel checks against the OEIS data**

a_data checks all 81 listed terms a(1..81) (index i+1, matching offset 1) with decide +kernel. I compared with the OEIS data by script: identical (81/81). val_data checks `val` against the 66 listed A060734 terms (antidiagonals read downward) and against the 6x6 example array in the entry. pos_val and val_pos prove that val is a bijection from ℕ×ℕ onto the positive integers. Together these pin the layout. The data also pins king-move adjacency: a(1) = 2 needs the diagonal neighbour 3, and a(6) = 5 needs the diagonals 2 and 12/10. It also pins the treatment of border cells: cells outside the quadrant are absent, as with the zero padding in the entry's Mathematica program.

**Points for the reviewer**

- *Note.* Scope: `statement` is the conjunction of the first two conjectures only. The entry's third conjecture (the set of n with a(n) = 4 is unbounded) is recorded separately as `statement_four_unbounded` and is not settled. The catalogue title scopes the result correctly; any summary saying 'the A326407 conjectures are settled' would overstate it.
- *Note.* 'a(n) = 5 for n={6}' is read as {n >= 1 : a(n) = 5} = {6}, an iff, which is the natural reading of the set notation. The direction a(6) = 5 is also fixed by the data. a 0 is a junk value (pos 0 = (0,0), giving 2) and is excluded by 1 <= n. The inequality a(n) < 6 holds trivially at primes (-1), which agrees with the OEIS convention.

## A326602: A326602: a(n) is odd iff n is a square

Verdict of the pre-review: **faithful**. Result: [oeis-a326602](../../results/oeis-a326602/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A326602.lean`](../../lean/Math0/Statements/OEIS/A326602.lean).

**The conjecture as stated in OEIS**

> %F A326602 a(n) is odd iff n is square (conjecture).  (_Paul D. Hanna_, Aug 08 2019; rev #19, Aug 11 2019, unchanged upstream.) Definition: %N G.f.: Sum_{n>=0} (x^(2*n-1) + 1)^n * x^n / (1 + x^(2*n+1))^(n+1), an even function. %F G.f. A(x) = Sum_{n>=0} a(n)*x^(2*n). %O 0,2

**The frozen Lean statement**

```lean
noncomputable def summand (n : ℕ) : PowerSeries ℤ :=
  (X ^ (2 * n - 1) + 1) ^ n * X ^ n * invOfUnit ((1 + X ^ (2 * n + 1)) ^ (n + 1)) 1
noncomputable def A : PowerSeries ℤ :=
  mk fun N => ∑ n ∈ Finset.range (N + 1), coeff N (summand n)
-- HasSum summand A proved (hasSum_summand)
def a (n : ℕ) : ℤ := coeffA (2 * n)   -- theorem a_eq_coeff : a n = coeff (2 * n) A

def statement : Prop :=
  ∀ n : ℕ, Odd (a n) ↔ IsSquare n
```

**What the Lean statement says**

Let A(x) be the formal power series over ℤ given by the sum over m >= 0 of (x^(2m-1) + 1)^m x^m / (1 + x^(2m+1))^(m+1), where the m = 0 summand is 1/(1+x). Let a(n) be the coefficient of x^(2n) in A. Then for every n >= 0, a(n) is odd if and only if n = k^2 for some integer k >= 0 (so n = 0 counts as a square).

**What the kernel checks against the OEIS data**

a_data checks all 68 listed terms a(0..67) (index i+0, matching offset 0) with decide +kernel. I compared with the OEIS data by script: identical (68/68), signs included. a_eq_coeff proves a n = coeff (2n) A for every n, and hasSum_summand proves A is the sum of the OEIS summands, so the definition is fixed by proof and the data is a cross-check. coeffA_odd_data checks that the odd-index coefficients 1, 3, ..., 79 vanish, a sanity check of 'even function'.

**Points for the reviewer**

- *Note.* At m = 0 the OEIS factor (x^(-1)+1)^0 involves a negative exponent. In Lean, 2*0-1 truncates to 0, giving (X^0+1)^0 = 1. Both equal 1 because the outer exponent is 0, so the truncated subtraction does no harm. For m >= 1 the subtraction is exact.
- *Note.* Evenness of A is checked only for the first 40 odd coefficients, not proved. It plays no role, because a(n) is defined, as in the entry ('A(x) = Sum a(n) x^(2n)', PARI polcoeff(A,2*n)), as the x^(2n) coefficient. IsSquare on ℕ counts 0 as a square, consistent with a(0) = 1 being odd and with the entry's list of odd terms starting at a(0^2).

## A328202: The gcd of the interior binomial coefficients of row n equals Λ-exp(n)·Λ-exp(n−1) (A328202, Maiga's conjecture)

Verdict of the pre-review: **faithful**. Result: [oeis-a328202](../../results/oeis-a328202/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A328202.lean`](../../lean/Math0/Statements/OEIS/A328202.lean).

**The conjecture as stated in OEIS**

> %F A328202 a(n) = A014963(n) * A014963(n - 1) (conjecture). - _Jon Maiga_, Oct 08 2019. Definition (entry by _Joel Kaufmann_, Oct 07 2019): %N a(n) is the greatest common divisor of all the numbers in row n of Pascal's triangle excluding 1 and n. %O 4,1. (Upstream differs from the local mirror only in the %K keyword 'changed'; text identical.) [Also in the entry, not targeted: %C (Robert Israel, Oct 16 2019) 'If p is a Fermat prime > 3, a(p)=2*p. If p is a Mersenne prime, a(p+1)=2*p. Conjecture: these are the only cases where a(n)>n.']

**The frozen Lean statement**

```lean
def a (n : ℕ) : ℕ := (Finset.Icc 2 (n - 2)).gcd (Nat.choose n)
def expMangoldt (m : ℕ) : ℕ := if IsPrimePow m then m.minFac else 1
-- theorem cast_expMangoldt : (expMangoldt m : ℝ) = Real.exp (ArithmeticFunction.vonMangoldt m)

def statement : Prop :=
  ∀ n : ℕ, 4 ≤ n → a n = expMangoldt n * expMangoldt (n - 1)
```

**What the Lean statement says**

For every integer n >= 4, the gcd of the binomial coefficients C(n,k) with 2 <= k <= n-2 equals L(n)·L(n-1). Here L(m) = p if m is a power p^t (t >= 1) of a prime p, and L(m) = 1 otherwise.

**What the kernel checks against the OEIS data**

a_data checks all 75 listed terms a(4..78) (index i+4, matching offset 4) with decide +kernel. I compared with the OEIS data by script: identical (75/75). expMangoldt_data checks the 95 listed terms A014963(1..95), and cast_expMangoldt proves expMangoldt = exp ∘ Λ (Mathlib's von Mangoldt function) for all m. Both definitions are therefore fixed by proof or by direct definition, and the data agrees.

**Points for the reviewer**

- *Note.* 'Excluding 1 and n' is encoded positionally, dropping k = 0, 1, n-1, n. For n >= 4 every C(n,k) with 2 <= k <= n-2 is >= n(n-1)/2 > n, so the value-based reading gives the same set. The entry's own example ('remove the first and last 2 numbers') and its programs (k = 2..n/2) agree with the encoding.
- *Note.* Scope: Robert Israel's separate conjecture in the same entry (a(n) > n only at Fermat primes > 3 and at n = Mersenne prime + 1) is recorded as `statementIsrael` and is not part of `statement`. The result certifies only Maiga's formula, which is what the catalogue title claims. a n for n < 4 is junk (e.g. gcd over the empty set = 0) and is excluded by 4 <= n. n-1 is an exact subtraction. Catalogue classification: known result (Kaplan–Levy 2004), first formalization. This is not a fidelity issue.
