# Fidelity review packet 01 of 11

Prepared on 29 Oct 2026 by an adversarial reviewing agent, not by a person. It is meant to make a human review of these statements quick: for each one it quotes the OEIS conjecture and the frozen Lean statement, restates the Lean in plain words, and lists anything a reviewer should look at. See [the index](README.md).

Statements in this packet: A001040, A005590, A022445, A057566, A057566b, A060693, A062887, A071685, A073642, A075855.

## A001040: Kurkov's rook-tour conjecture for A001040: 2·n!·a(n) counts opposite-line Hamiltonian paths of K_n □ K_2

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a001040](../../results/oeis-a001040/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A001040.lean`](../../lean/Math0/Statements/OEIS/A001040.lean).

**The conjecture as stated in OEIS**

> %C A001040 Conjecture: 2*n!*a(n) is the number of open tours by a rook on an (n X 2) chessboard which ends at the opposite line of length n. - _Mikhail Kurkov_, Nov 19 2019
> (Sequence: %N a(n+1) = n*a(n) + a(n-1) with a(0)=0, a(1)=1; %O 0,4. Rev #140, Oct 15 2026, identical in the local mirror and in current GitHub oeisdata.)

**The frozen Lean statement**

```lean
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => (n + 1) * a (n + 1) + a n

def RookMove {n : ℕ} (p q : Fin n × Fin 2) : Prop :=
  p ≠ q ∧ (p.1 = q.1 ∨ p.2 = q.2)

def IsOpenTour (n : ℕ) (l : List (Fin n × Fin 2)) : Prop :=
  l.Nodup ∧ (∀ s, s ∈ l) ∧ l.IsChain RookMove

def EndsOnOppositeLine {n : ℕ} (l : List (Fin n × Fin 2)) : Prop :=
  ∃ s ∈ l.head?, ∃ t ∈ l.getLast?, s.2 ≠ t.2

def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    {l : List (Fin n × Fin 2) | IsOpenTour n l ∧ EndsOnOppositeLine l}.ncard = 2 * n ! * a n
```

**What the Lean statement says**

Let a(0)=0, a(1)=1, a(m+1)=m·a(m)+a(m−1). Take the board with squares (i,c), i in {0..n−1}, c in {0,1}. Two distinct squares are adjacent when they share i or share c (the graph K_n □ K_2; a move can be any distance along a line). Count the sequences that list every square exactly once with consecutive squares adjacent (directed Hamiltonian paths, so a path and its reversal both count) and whose first and last squares have different c. For every n ≥ 1 this count is 2·n!·a(n).

**What the kernel checks against the OEIS data**

a_data kernel-checks all 24 listed terms a(0..23) against the recursion, which pins down a. tours_card_small kernel-checks the tour counts 2, 4, 36, 480 for n = 1..4 through the Finset `tours n`, proved equal to the set in the statement by ncard_eq_card_tours. These match 2·n!·a(n). These counts also pin down the model. I recomputed under alternative readings: a rook that cannot pass over visited squares gives 2, 4, 16, 72, and one-step moves give 2, 4, 8, 12, so both are ruled out at n = 3. Reading tours as undirected would give 1 at n = 1. Taking 'open' to mean 'the ends are not a rook move apart' would give 0 at n = 1. The reading also agrees with A096121, the total count that Kurkov's conjecture refines: its comment says the rook 'may intersect its own path', and its data 2, 8, 60, 816, 17520, 550080 equal 2·n!·(A001040(n)+A001053(n)), the opposite-line count plus Kurkov's same-line count.

**Points for the reviewer**

- *Note.* The statement makes three reading choices: directed tours, 'open' meaning a Hamiltonian path rather than a cycle, and a rook allowed to pass over squares. The OEIS text does not spell these out, but the n = 1, 3, 4 counts force them, and they match A096121's definition and data. Kurkov's companion conjecture in A001053 counts tours that 'start and end at the same line', which would be identically 0 under the 'ends not rook-adjacent' reading of 'open'. That supports the path reading.
- *Note.* At n = 2 the board is 2×2, so 'lines of length n' and the short rows both have length 2, and the Lean picks the c-lines. By transpose symmetry the count is the same either way.
- *Note.* The range is n ≥ 1. n = 0 is trivial (tours_zero gives 0, and 2·0!·a(0) = 0), so nothing is lost. Set.ncard returns a junk value 0 on infinite sets, but ncard_eq_card_tours identifies the set with a finite Finset, so no junk value arises.

## A005590: Zeros of a(3n) for the signed Stern sequence A005590 are exactly the fibbinary numbers

Verdict of the pre-review: **faithful**. Result: [oeis-a005590](../../results/oeis-a005590/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A005590.lean`](../../lean/Math0/Statements/OEIS/A005590.lean).

**The conjecture as stated in OEIS**

> %F A005590 Conjecture: a(3n)=0 iff n in A003714. - _Ralf Stephan_, May 02 2003
> (Sequence: %N a(0) = 0, a(1) = 1, a(2n) = a(n), a(2n+1) = a(n+1) - a(n); %O 0,10. A003714: fibbinary numbers, '... Also numbers whose binary representation contains no two adjacent 1's', %O 0,3, first term 0. Rev #97, Nov 05 2025, unchanged on GitHub.)

**The frozen Lean statement**

```lean
def aux : ℕ → ℕ → ℤ
  | 0, _ => 0
  | fuel + 1, n =>
    if n ≤ 1 then (n : ℤ)
    else if n % 2 = 0 then aux fuel (n / 2)
    else aux fuel (n / 2 + 1) - aux fuel (n / 2)

def a (n : ℕ) : ℤ := aux (n + 1) n

def IsFibbinary (n : ℕ) : Prop :=
  ∀ i : ℕ, ¬ (n.testBit i = true ∧ n.testBit (i + 1) = true)

def statement : Prop :=
  ∀ n : ℕ, a (3 * n) = 0 ↔ IsFibbinary n
```

**What the Lean statement says**

Let a : ℕ → ℤ satisfy a(0)=0, a(1)=1, a(2n)=a(n), a(2n+1)=a(n+1)−a(n). For every n ≥ 0, a(3n) = 0 if and only if no two adjacent binary digits of n are both 1.

**What the kernel checks against the OEIS data**

a_data kernel-checks all 105 listed terms a(0..104). The theorems a_zero, a_one, a_even and a_odd prove that the fuelled definition satisfies the OEIS defining equations for every n. Those equations determine the sequence, so the fuel cannot cut the recursion off. fibbinary_data kernel-checks that IsFibbinary selects exactly the 61 listed terms of A003714 up to 264. Both definitions are therefore pinned down, not just matched on samples.

**Points for the reviewer**

- *Note.* n = 0 is included: a(0) = 0, and 0 is the first term of A003714 (offset 0). This matches the literal claim.
- *Note.* A003714 is encoded through its 'no two adjacent 1's in binary' description rather than the Zeckendorf-image description. The entry itself gives both and they define the same set; the 61-term check agrees.

## A022445: The generating function of A022445 (closed self-avoiding walks in the strip {0,1,2} x Z)

Verdict of the pre-review: **faithful**. Result: [oeis-a022445](../../results/oeis-a022445/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A022445.lean`](../../lean/Math0/Statements/OEIS/A022445.lean).

**The conjecture as stated in OEIS**

> %F A022445 G.f.: (-6*x^7+10*x^6-18*x^5+27*x^4-14*x^3+10*x^2-4*x+1) / ((1+x^2)^2*(1-2*x)^2) (conjectured). - _Ralf Stephan_, Apr 28 2004
> (Sequence: %N Number of self-avoiding closed walks (from 0 to 0) of length 2n in the strip {0, 1, 2} X Z of the square lattice Z X Z; %O 0,3; data 1,0,4,10,34,94,222,... (29 terms). Rev #10, May 16 2019, unchanged on GitHub.)

**The frozen Lean statement**

```lean
def step : Fin 4 → ℤ × ℤ := ![(1, 0), (-1, 0), (0, 1), (0, -1)]
def vertex {m : ℕ} (t : Fin m → Fin 4) (i : ℕ) : ℤ × ℤ :=
  ∑ j : Fin m, if (j : ℕ) < i then step (t j) else 0
def InStrip (v : ℤ × ℤ) : Prop := 0 ≤ v.1 ∧ v.1 ≤ 2
def IsClosedSAW {m : ℕ} (t : Fin m → Fin 4) : Prop :=
  (∀ i < m + 1, InStrip (vertex t i)) ∧ vertex t m = 0 ∧
    (∀ j < m, ∀ i < j, vertex t i ≠ vertex t j) ∧
    (∀ j < m, ∀ i < j, s(vertex t i, vertex t (i + 1)) ≠ s(vertex t j, vertex t (j + 1)))
def a (n : ℕ) : ℕ := Fintype.card {t : Fin (2 * n) → Fin 4 // IsClosedSAW t}

open PowerSeries in
def statement : Prop :=
  PowerSeries.mk (fun n => (a n : ℤ)) * ((1 + X ^ 2) ^ 2 * (1 - 2 * X) ^ 2) =
    -6 * X ^ 7 + 10 * X ^ 6 - 18 * X ^ 5 + 27 * X ^ 4 - 14 * X ^ 3 + 10 * X ^ 2 - 4 * X + 1
```

**What the Lean statement says**

Let a(n) be the number of step sequences of length 2n on the square lattice with these properties. The walk starts at (0,0), every vertex has first coordinate in {0,1,2}, and the walk returns to (0,0). Vertices 0..2n−1 are pairwise distinct, and no edge is used twice. The empty walk counts, and each polygon through the origin counts once per direction. Then (Σ a(n) xⁿ)·(1+x²)²(1−2x)² = 1 − 4x + 10x² − 14x³ + 27x⁴ − 18x⁵ + 10x⁶ − 6x⁷ in ℤ[[x]]. Since the denominator has constant term 1, this says Σ a(n) xⁿ equals the stated rational function.

**What the kernel checks against the OEIS data**

a_data kernel-checks a(0..9) = 1, 0, 4, 10, 34, 94, 222, 516, 1202, 2738 through a DFS evaluator proved equal to `a` for all n (a_eq_aFast). These terms pin the model. a(0) = 1 requires counting the empty walk. a(1) = 0 requires excluding the back-and-forth walks of length 2. a(2) = 4 requires the origin on the boundary column (a middle-column origin gives 8, which is A022444) and counting walks with direction. listed_satisfy_gf checks that all 29 listed terms satisfy the transcribed numerator and denominator, which tests the transcription only. Together with the proved result, it implies that the definition reproduces all 29 listed terms.

**Points for the reviewer**

- *Note.* The generating-function identity is stated with the denominator cleared. The denominator is a unit in ℤ⟦X⟧ (constant term 1), so this is equivalent to the quotient form in the OEIS. The numerator and denominator are transcribed exactly.
- *Note.* The edge-distinctness clause only matters for length 2, where it excludes 0→v→0. That exclusion is forced by the listed a(1) = 0.

## A057566: Layman's floor formula for collinear triples in a 3 × n grid (A057566), as printed until its October 2026 correction, fails at n = 24

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a057566](../../results/oeis-a057566/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A057566.lean`](../../lean/Math0/Statements/OEIS/A057566.lean).

**The conjecture as stated in OEIS**

> %F A057566 Conjecture: a(n) = 5*floor((2n^3 - 3n^2 - n)/24) + floor((2(n-1)^3 - 3(n-1)^2 - (n-1))/24) + n, which fits all of the listed terms.
> (Text as of rev #27, Feb 22 2024, in the local mirror. The line is unsigned; the entry is by _John W. Layman_, Oct 04 2000. %N Number of collinear triples in a 3 X n rectangular grid; %O 0,3. OEIS replaced this line with a corrected formula on Oct 21 2026, rev #30.)

**The frozen Lean statement**

```lean
def grid (n : ℕ) : Finset (ℕ × ℕ) := Finset.range 3 ×ˢ Finset.range n
def cross (p q r : ℕ × ℕ) : ℤ :=
  ((q.1 : ℤ) - p.1) * ((r.2 : ℤ) - p.2) - ((q.2 : ℤ) - p.2) * ((r.1 : ℤ) - p.1)
def IsCollinear (s : Finset (ℕ × ℕ)) : Prop := ∀ p ∈ s, ∀ q ∈ s, ∀ r ∈ s, cross p q r = 0
def a (n : ℕ) : ℕ := ((grid n).powersetCard 3 |>.filter IsCollinear).card

def statement : Prop :=
  ∀ n : ℕ, 3 ≤ n → (a n : ℤ) =
    5 * ⌊(2 * (n : ℚ) ^ 3 - 3 * (n : ℚ) ^ 2 - (n : ℚ)) / 24⌋
      + ⌊(2 * ((n : ℚ) - 1) ^ 3 - 3 * ((n : ℚ) - 1) ^ 2 - ((n : ℚ) - 1)) / 24⌋ + n
(The result proved is ¬ statement.)
```

**What the Lean statement says**

Let a(n) be the number of 3-element subsets of {0,1,2}×{0,…,n−1} whose points lie on a common line. Claim: for every n ≥ 3, a(n) = 5⌊(2n³−3n²−n)/24⌋ + ⌊(2(n−1)³−3(n−1)²−(n−1))/24⌋ + n. The project proves this claim false.

**What the kernel checks against the OEIS data**

a_data kernel-checks a(0..24) = 0, 1, 2, 8, …, 5578, 6360 through fastA, which is proved equal to `a` for all n. This pins down 'collinear triple' as an unordered 3-subset; ordered triples would give 6 times as many. It also fixes the decisive term a(24) = 6360, where the formula gives 6365. I recomputed both values independently: 3·C(24,3)+24+2⌊23²/4⌋ = 6360, and the formula gives 5·1079+946+24 = 6365. The formula fails at every n from 24 to at least 199.

**Points for the reviewer**

- *Note.* The statement restricts n to n ≥ 3, while the OEIS line gives no range and the offset is 0. Because the result refutes the statement, this restriction makes the result stronger. The counterexample n = 24 lies in every reasonable range, and both floor arguments are positive there, so floor, truncation and integer division agree. The restriction only avoids a spurious refutation at n = 0, 1, where the literal true-floor reading gives −1 and −4. Read with truncation, the formula matches a(0..23).
- *Note.* What is refuted is the formula as printed before OEIS's Oct 21 2026 correction. The printed polynomial differs from the corrected one by n−3 in the numerator, which is not a typo-level slip. The printed formula fits exactly a(0..23) (read with truncation) and fails from n = 24 on, which is consistent with Layman fitting the terms listed in 2000. So the refutation settles what the author wrote. The catalogue title and summary say plainly that this is the superseded text, and the corrected formula is handled separately as A057566b.
- *Note.* The OEIS %F line is unsigned. Attributing it to Layman, the author of the entry, as of Oct 04 2000 is an inference.

## A057566b: The corrected floor formula for collinear triples in a 3 x n grid (OEIS A057566) holds for all n

Verdict of the pre-review: **faithful**. Result: [oeis-a057566b](../../results/oeis-a057566b/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A057566b.lean`](../../lean/Math0/Statements/OEIS/A057566b.lean).

**The conjecture as stated in OEIS**

> %F A057566 Conjecture: a(n) = 5*floor((2n^3 - 3n^2 - 2n + 3)/24) + floor((2(n-1)^3 - 3(n-1)^2 - 2(n-1) + 3)/24) + n, which fits all of the listed terms. [Corrected by _Alper Ferudun_, Oct 21 2026]
> (Rev #30, Oct 22 2026. The scratchpad live copy is identical to current GitHub oeisdata. %N Number of collinear triples in a 3 X n rectangular grid; %O 0,3; original conjecture by _John W. Layman_, Oct 04 2000.)

**The frozen Lean statement**

```lean
def grid (n : ℕ) : Finset (ℕ × ℕ) := Finset.range 3 ×ˢ Finset.range n
def cross (p q r : ℕ × ℕ) : ℤ :=
  ((q.1 : ℤ) - p.1) * ((r.2 : ℤ) - p.2) - ((q.2 : ℤ) - p.2) * ((r.1 : ℤ) - p.1)
def IsCollinear (s : Finset (ℕ × ℕ)) : Prop := ∀ p ∈ s, ∀ q ∈ s, ∀ r ∈ s, cross p q r = 0
def a (n : ℕ) : ℕ := ((grid n).powersetCard 3 |>.filter IsCollinear).card

def statement : Prop :=
  ∀ n : ℕ, (a n : ℤ) =
    5 * ⌊(2 * (n : ℚ) ^ 3 - 3 * (n : ℚ) ^ 2 - 2 * (n : ℚ) + 3) / 24⌋
      + ⌊(2 * ((n : ℚ) - 1) ^ 3 - 3 * ((n : ℚ) - 1) ^ 2 - 2 * ((n : ℚ) - 1) + 3) / 24⌋ + n
```

**What the Lean statement says**

Let a(n) be the number of 3-element collinear subsets of {0,1,2}×{0,…,n−1}. For every n ≥ 0, with true floors and n−1 = −1 when n = 0: a(n) = 5⌊(2n³−3n²−2n+3)/24⌋ + ⌊(2(n−1)³−3(n−1)²−2(n−1)+3)/24⌋ + n.

**What the kernel checks against the OEIS data**

a_data kernel-checks a(0..24), the same evaluator and data as A057566, which pins down unordered collinear 3-subsets. numer_nonneg proves that 2m³−3m²−2m+3 = (m−1)(m+1)(2m−3) ≥ 0 for all integers m ≥ −1, so the claim does not depend on the floor convention. I checked independently that the formula equals 3·C(n,3)+n+2⌊(n−1)²/4⌋ for n = 0..4999, including n = 0, 1, 2 (0, 1, 2).

**Points for the reviewer**

- *Note.* The range is all n ≥ 0, the full offset range, with true floors. Since every floor argument is nonnegative, truncation and integer division give the same claim, and statement_iff_ediv records the integer-division form. This is the strongest literal reading.
- *Note.* The grid is 3 rows × n columns. Transposing does not change the number of collinear triples, so the orientation is immaterial.

## A060693: Schulte's alternating quadratic sum over the Schröder-peaks triangle (A060693)

Verdict of the pre-review: **faithful**. Result: [oeis-a060693](../../results/oeis-a060693/README.md) (known-result-already-formalized). Frozen statement: [`lean/Math0/Statements/OEIS/A060693.lean`](../../lean/Math0/Statements/OEIS/A060693.lean).

**The conjecture as stated in OEIS**

> %F A060693: "Conjecture: Sum_{k=0..n} (-1)^k*T(n,k)*(n+1-k)^2 = 1+n+n^2. - _Werner Schulte_, Jan 11 2017". Entry definition (%N, offset 0, keyword tabl): "Triangle (0 <= k <= n) read by rows: T(n, k) is the number of Schröder paths from (0,0) to (2n,0) having k peaks." Deutsch's comment: "Schroeder paths (i.e., consisting of steps U=(1,1), D=(1,-1), H=(2,0) and never going below the x-axis) from (0,0) to (2n,0), having k peaks. Example: T(2,1)=3 because we have UU*DD, U*DH and HU*D, the peaks being shown by *." (Local mirror %I #147, Oct 04 2026.)

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * (T n k : ℤ) * ((n : ℤ) + 1 - k) ^ 2 =
    1 + (n : ℤ) + (n : ℤ) ^ 2

-- dependencies
inductive Step | U | D | H
def Step.dx : Step → ℕ | U => 1 | D => 1 | H => 2
def Step.dy : Step → ℤ | U => 1 | D => -1 | H => 0
def width (p : List Step) : ℕ := (p.map Step.dx).sum
def height (p : List Step) : ℤ := (p.map Step.dy).sum
def IsSchroderPath (n : ℕ) (p : List Step) : Prop :=
  width p = 2 * n ∧ height p = 0 ∧ ∀ q ∈ p.inits, 0 ≤ height q
def peaks (p : List Step) : ℕ := (p.zip p.tail).count (U, D)
def words : ℕ → List (List Step)
  | 0 => [[]] | 1 => [[U], [D]]
  | m + 2 => (words (m + 1)).map (U :: ·) ++ (words (m + 1)).map (D :: ·) ++ (words m).map (H :: ·)
def schroderPaths (n : ℕ) : Finset (List Step) := (words (2 * n)).toFinset.filter (IsSchroderPath n)
def T (n k : ℕ) : ℕ := ((schroderPaths n).filter (fun p => peaks p = k)).card
```

**What the Lean statement says**

For every integer n ≥ 0, let T(n,k) be the number of lattice paths from (0,0) to (2n,0) with steps (1,1), (1,-1), (2,0) that never go below the x-axis and contain exactly k occurrences of an up-step immediately followed by a down-step. Then the integer sum over k = 0..n of (-1)^k · T(n,k) · (n+1-k)^2 equals 1 + n + n^2.

**What the kernel checks against the OEIS data**

T_data kernel-checks rows n = 0..9 of the triangle plus T(10,0) = 16796 (all 56 listed terms); a_data checks the same 56 terms as the flattened sequence a 0..a 55. Both go through a dynamic program, but T_eq_Tfast proves Tfast = T for all n, k, so the values are values of the stated definition. T_eq_ncard restates T as the cardinality of {p | IsSchroderPath n p ∧ peaks p = k}. statement_check confirms the identity for n ≤ 12 (sanity check only). T is defined directly by the entry's combinatorial definition, not reverse-engineered from the data. The data also pin down the conventions: what counts as a peak (only UD, not UH or HD), the H step having width 2, and the non-negativity condition.

**Points for the reviewer**

- *Note.* The arithmetic is in ℤ, so n+1-k is not truncated. For k ≤ n it is positive anyway. The sum range k = 0..n and the range n ≥ 0 (including the trivial n = 0 case) match the conjecture exactly.
- *Note.* Non-negativity is checked only at the vertices (prefixes) of the path. This is correct because the path is straight between vertices: an H step stays at the same height, and U/D steps change the height by one.

## A062887: Odd descending-by-2 multiples exist exactly when 125 does not divide 2n+1 (A062887)

Verdict of the pre-review: **faithful**. Result: [oeis-a062887](../../results/oeis-a062887/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A062887.lean`](../../lean/Math0/Statements/OEIS/A062887.lean).

**The conjecture as stated in OEIS**

> %C A062887: "Conjecture: The only numbers n for which a(n)=0 are those for which 2*n+1 is divisible by 125. - _Sean A. Irvine_, Apr 14 2023". Entry definition (%N, offset 0, Amarnath Murthy, Jun 28 2001): "Smallest multiple of 2n+1 with the property that its digits are odd and each digit is two less (mod 10) than the previous digit, or 0 if no such number exists." (Local mirror #12, Apr 14 2023.)

**The frozen Lean statement**

```lean
def statement : Prop := ∀ n : ℕ, a n = 0 ↔ 125 ∣ 2 * n + 1

-- dependencies
def IsDesc2 (N : ℕ) : Prop :=
  0 < N ∧ (∀ d ∈ Nat.digits 10 N, Odd d) ∧
    (Nat.digits 10 N).reverse.IsChain (fun prev next => next + 2 ≡ prev [MOD 10])

open Classical in
noncomputable def a (n : ℕ) : ℕ :=
  if h : ∃ N, IsDesc2 N ∧ 2 * n + 1 ∣ N then Nat.find h else 0
```

**What the Lean statement says**

Call a positive integer N admissible if all of its decimal digits are odd and, reading left to right, each digit is 2 less (mod 10) than the one before it. Let a(n) be the least admissible multiple of 2n+1, or 0 if there is none. Then for every n ≥ 0, a(n) = 0 if and only if 125 divides 2n+1. Because admissible numbers are positive, this is the same as: 2n+1 has no admissible multiple if and only if 125 | 2n+1.

**What the kernel checks against the OEIS data**

a_data proves a(0..25) equal all 26 listed terms, up to 753197531975319753, for the noncomputable a. It uses a bounded search aSearch with B = 18 digits. The lemma a_eq_of_aSearch proves that a search hit is the true Nat.find minimum: isDesc2_ofDigits_gen and exists_gen_of_isDesc2 characterize the admissible numbers exactly, and any smaller admissible number has no more digits. example_975 checks the entry's example 975 = 13·75. The data pin the definition down well. Single-digit numbers count (a(1..4) = 3, 5, 7, 9), the digits descend left to right (319, not 913), and 2n+1 itself counts as a multiple (a(0) = 1).

**Points for the reviewer**

- *Note.* "The only numbers n for which a(n)=0 are those for which ..." is read as a set equality (iff). A strict one-way reading would be a(n) = 0 ⇒ 125 | 2n+1. The extra direction, 125 | 2n+1 ⇒ a(n) = 0, is an elementary finite check: an admissible number with 3 or more digits ends in 975, 753, 531, 319 or 197, none of which is divisible by 125. So the iff contains the substantive direction and adds only a trivially true one. No material difference.
- *Note.* The requirement N > 0 in IsDesc2 is needed and correct. Without it, Nat.digits 10 0 = [] would make 0 vacuously admissible and Nat.find would return 0. With it, a n = 0 holds exactly when no admissible multiple exists, which matches the entry's "0 if no such number exists".

## A071685: Reverse-divisor numbers are 1, 12, 78 or 89 mod 100 (A071685, Dale's conjecture)

Verdict of the pre-review: **faithful**. Result: [oeis-a071685](../../results/oeis-a071685/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A071685.lean`](../../lean/Math0/Statements/OEIS/A071685.lean).

**The conjecture as stated in OEIS**

> %C A071685: "Conjecture: every term mod 100 is equal to 1, 12, 78, or 89. - _Harvey P. Dale_, Dec 13 2017". Entry definition (%N, offset 1, Labos Elemer, Jun 03 2002): "Non-palindromic numbers n, not divisible by 10, such that either n divides R(n) or R(n) divides n, where R(n) is the digit-reversal of n." (Local mirror #39, Nov 05 2025.)

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ n : ℕ, IsTerm n → n % 100 = 1 ∨ n % 100 = 12 ∨ n % 100 = 78 ∨ n % 100 = 89

-- dependencies
def R (n : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 n).reverse
def IsTerm (n : ℕ) : Prop := R n ≠ n ∧ ¬ 10 ∣ n ∧ (n ∣ R n ∨ R n ∣ n)
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)   -- used only in the data check
```

**What the Lean statement says**

Let R(n) be the decimal digit reversal of n, with leading zeros dropped. Take any natural number n with R(n) ≠ n, 10 ∤ n, and either n | R(n) or R(n) | n. Then n mod 100 is one of 1, 12, 78, 89.

**What the kernel checks against the OEIS data**

term_iff proves, with kernel scans backed by soundness lemmas, that for n < 10^7 IsTerm n holds exactly when n is one of the 16 listed terms 1089, …, 9899901. a_data derives a(1..16) from this. So the predicate is pinned down completely below 10^7, including the entry's exclusions: palindromes such as 12021, and multiples of 10 such as 8380 and 8400 fail IsTerm. R_examples checks R 1089 = 9801, R 8712 = 2178, R 12021 = 12021, R 8380 = 838, and also R 120 = 21 and R 0 = 0. The listed terms of 8 or more digits (10891089, …) are not checked, but the predicate is the entry's definition verbatim.

**Points for the reviewer**

- *Note.* The statement quantifies over the predicate IsTerm, not over a(i) = Nat.nth IsTerm (i-1). These are equivalent: the terms of the sequence are exactly the n with IsTerm n. The predicate form even avoids any dependence on the sequence being infinite.
- *Note.* "Non-palindromic" is encoded as R n ≠ n. For n not divisible by 10, R(n) has the same digit list reversed, so this coincides with the digit-palindrome definition. Multiples of 10 are excluded separately anyway.

## A073642: Yanev's identity for A073642 (sum of the positions of the 1-bits)

Verdict of the pre-review: **faithful**. Result: [oeis-a073642](../../results/oeis-a073642/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A073642.lean`](../../lean/Math0/Statements/OEIS/A073642.lean).

**The conjecture as stated in OEIS**

> %F A073642: "Conjecture: a(n) = (3*A011371(n) - Sum_{k=1..n} A007814(k)^2)/2 for n > 0. - _Velin Yanev_, Sep 09 2017". Entry definition (%N, offset 0): "Replace 2^k in the binary representation of n with k (i.e., if n = 2^b + 2^c + 2^d + ... then a(n) = b + c + d + ...)." A011371 (offset 0): "a(n) = n minus (number of 1's in binary expansion of n). Also highest power of 2 dividing n!." A007814 (offset 1): "Exponent of highest power of 2 dividing n, a.k.a. ... the 2-adic valuation of n." (Local mirror A073642 #121, Jul 05 2026.)

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ n : ℕ, 0 < n →
    (a n : ℚ) = (3 * (A011371 n : ℚ) - ∑ k ∈ Finset.Icc 1 n, (A007814 k : ℚ) ^ 2) / 2

-- dependencies
def a (n : ℕ) : ℕ := (Nat.bitIndices n).sum
def A011371 (n : ℕ) : ℕ := n - (Nat.digits 2 n).count 1
def A007814 (n : ℕ) : ℕ := padicValNat 2 n
```

**What the Lean statement says**

For every n ≥ 1, let a(n) be the sum of the exponents in the binary expansion of n, s(n) the number of 1-bits of n, and v₂(k) the 2-adic valuation of k. Then a(n) = (3·(n − s(n)) − Σ_{k=1}^{n} v₂(k)²) / 2, computed in the rationals.

**What the kernel checks against the OEIS data**

a_data checks all 88 listed terms a(0..87). a_sum_two_pow proves structurally that a(Σ_{i∈s} 2^i) = Σ_{i∈s} i for every finite set s, which is the entry's definition exactly. A011371_data checks all 73 listed terms of A011371 (n = 0..72), and A011371_eq_padicValNat_factorial proves A011371 n = v₂(n!), the second description. A007814_data checks all 111 listed terms of A007814 (k = 1..111). rhs_data checks that 3·A011371(n) − Σ_{k≤n} A007814(k)² = 2·a(n) for n = 1..87. This is a sanity check, not part of the statement. Together these fully pin down all three definitions.

**Points for the reviewer**

- *Note.* "/2" is read as exact division in ℚ. This is at least as strong as any integer or floor reading: it also asserts that the numerator is even. So the result implies every reasonable reading.
- *Note.* A011371 uses natural-number subtraction n − (number of 1-bits), which never truncates because there are at most n ones. A007814 0 = padicValNat 2 0 = 0 is a junk value, but it is never used because the sum runs over Icc 1 n. The range n > 0 matches the conjecture.

## A075855: The longest path on the black squares of an even chessboard has (n^2-n+2)/2 squares (A075855)

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a075855](../../results/oeis-a075855/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A075855.lean`](../../lean/Math0/Statements/OEIS/A075855.lean).

**The conjecture as stated in OEIS**

> %F A075855 (Jon Perry, Oct 15 2002; edited by Dean Hickerson, Oct 25 2002): "For n odd, a(n)=(n-1)^2/2+1. For n even, it is conjectured that a(n)=(n^2-n+2)/2 (it is easy to show this is a lower bound)." Entry definition (%N, offset 1): "Maximum number of black squares on an n X n chessboard (with a black square in at least one corner) that can be covered by a single path, traveling only to adjacent black squares." Data: 1,2,3,7,9,16,19,29,33. (Local mirror #11, Aug 20 2025.)

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n → Even n → a n = (n ^ 2 - n + 2) / 2

-- dependencies
def IsBlack (n : ℕ) (c : ℕ × ℕ) : Prop := c.1 < n ∧ c.2 < n ∧ (c.1 + c.2) % 2 = 0
def Adj (c d : ℕ × ℕ) : Prop :=
  c ≠ d ∧ c.1 ≤ d.1 + 1 ∧ d.1 ≤ c.1 + 1 ∧ c.2 ≤ d.2 + 1 ∧ d.2 ≤ c.2 + 1
def IsBoardPath (n : ℕ) (l : List (ℕ × ℕ)) : Prop :=
  (∀ c ∈ l, IsBlack n c) ∧ l.Nodup ∧ l.IsChain Adj
-- a is an exhaustive DFS (abridged):
def a (n : ℕ) : ℕ := lmax (cells n) fun c => dfs n (n * n) c (1 <<< idx n c) + 1
-- proved characterization:
theorem a_spec (n : ℕ) : IsGreatest {k | ∃ l, IsBoardPath n l ∧ l.length = k} (a n)
```

**What the Lean statement says**

For every even n ≥ 2, colour square (i,j) of the n×n board (0 ≤ i,j < n) black when i+j is even, so corner (0,0) is black. Consider sequences of pairwise distinct black squares in which consecutive squares touch. For black squares this means they are diagonal neighbours. The maximum length of such a sequence is (n² − n + 2)/2 = 2m² − m + 1, where n = 2m. a_spec establishes that the Lean a n is exactly this maximum, so the statement does not depend on the search code.

**What the kernel checks against the OEIS data**

a_data kernel-checks the exact values a(1..6) = 1, 2, 3, 7, 9, 16. a_data_lower kernel-checks explicit paths, giving only lower bounds 19 ≤ a 7, 29 ≤ a 8, 33 ≤ a 9. The exact values 19, 29, 33 come from an outside-Lean search and are not in the kernel. a_spec proves that a n is the greatest path length for all n, so the search is tied to the definition. The exact terms fix the key conventions. a(3) = 3 rules out revisiting squares, which would give 5. a(2) = 2 confirms diagonal moves; with edge-only adjacency every value would be 1. a(3) = 3 also fixes the colouring for odd n: corners black, since with the other colouring the 4 black squares of the 3×3 board form a 4-cycle and give 4.

**Points for the reviewer**

- *Note.* The start square is unrestricted. The parenthetical "with a black square in at least one corner" is read as fixing the colouring, not as requiring the path to start at a corner. I checked by brute force (outside Lean) that both readings give the same values for n ≤ 7. For even n the two readings also coincide given the result: corner-start paths are a subset, so the upper bound transfers. The lower-bound path in the frontier proof (Frontier/OEIS/A075855.lean, snake starting from strip 0 left to right) and the n = 8 witness in a_data_lower both start at (0,0). No material difference.
- *Note.* Only the even case, which the entry marks as conjectured, is stated. The odd-case formula, which the entry asserts as fact, is not part of the statement. This matches the conjecture's scope. The range 1 ≤ n with Even n means n ≥ 2. The ℕ arithmetic is exact: n² ≥ n, and n² − n + 2 = n(n−1) + 2 is even.
- *Note.* The data check is weaker for n ≥ 7: only lower bounds are kernel-checked, so for the even case only a(2), a(4), a(6) are exact in the kernel and a(8) ≥ 29 is a bound. This is a limit of the sanity check, not a definitional gap, because a_spec proves a n equals the definition for every n.
