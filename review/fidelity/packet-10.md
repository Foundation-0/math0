# Fidelity review packet 10 of 11

Prepared on 29 Oct 2026 by an adversarial reviewing agent, not by a person. It is meant to make a human review of these statements quick: for each one it quotes the OEIS conjecture and the frozen Lean statement, restates the Lean in plain words, and lists anything a reviewer should look at. See [the index](README.md).

Statements in this packet: A356360, A357216, A357583, A362086, A363482, A363609, A367119, A368846, A369366, A373345.

## A356360: A356360: the continued-fraction denominators are 1 or prime

Verdict of the pre-review: **faithful**. Result: [oeis-a356360](../../results/oeis-a356360/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A356360.lean`](../../lean/Math0/Statements/OEIS/A356360.lean).

**The conjecture as stated in OEIS**

> %N Denominator of the continued fraction 1/(2-3/(3-4/(4-5/(...(n-1)-n/(n+1))))).  %C Conjecture: The sequence contains only 1's and the primes.  (%A _Mohammed Bouras_, Oct 15 2022; offset 3; entry rev #31, Aug 06 2024, identical in the local mirror and current GitHub oeisdata.)

**The frozen Lean statement**

```lean
def step (k : ℕ) (t : ℚ) : ℚ := (k : ℚ) - ((k : ℚ) + 1) / t
def cf (n : ℕ) : ℚ := 1 / (List.range' 2 (n - 2)).foldr step ((n : ℚ) + 1)
def a (n : ℕ) : ℕ := (cf n).den

def statement : Prop :=
  ∀ n : ℕ, 3 ≤ n → a n = 1 ∨ (a n).Prime
```

**What the Lean statement says**

For every natural number n ≥ 3, start with t = n+1 and, for k = n-1, n-2, ..., 2 in turn, replace t by k - (k+1)/t (exact rational arithmetic, with Lean's convention x/0 = 0). Let c = 1/t. Then the denominator of c in lowest terms is either 1 or a prime number.

**What the kernel checks against the OEIS data**

`example : cf 3 = 4/5 ∧ cf 4 = 11/7 ∧ cf 5 = 11/3` and `theorem a_data`, which checks a 3, ..., a 84 against all 82 listed terms. Both are kernel-checked with decide +kernel. I compared the Lean list with the %S/%T/%U lines of the entry and they match exactly. The definition is a literal transcription of the %N formula, and these checks fix the reduced-denominator reading (for example a(8) = 1 because the value is an integer).

**Points for the reviewer**

- *Note.* Junk values: if some tail of the fraction were 0, Lean's x/0 = 0 would give a junk value. If the outermost tail were 0, cf = 0 and a n = 1, so the claim would hold trivially at that n. The docstring rules this out by induction: every tail t_k exceeds u_k = k(k-2)/(k-1) ≥ 0. I also checked by exact arithmetic that no tail vanishes for 3 ≤ n < 1200. The definition therefore agrees with the real continued fraction for every n ≥ 3.
- *Note.* The statement covers only the %C conjecture, read as 'every term is 1 or prime' (a subset claim; it does not say every prime occurs). That reading is the right one, because 2 never occurs (a(n) divides 2n-1). It does not include the stronger %F line 'From the conjecture: Except for n = 5, a(n) = 2n-1 if 2n-1 is prime, 1 otherwise', nor McEachen's separate 2024 conjecture that all odd primes after 11 appear in order. Neither is the conjecture targeted here.

## A357216: Internal n-gons in a regular n-gon: triple points occur only for n = 3, 4, 6, and otherwise there are n k^2 + 1 regions (Shannon's A357216 conjecture)

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a357216](../../results/oeis-a357216/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A357216.lean`](../../lean/Math0/Statements/OEIS/A357216.lean).

**The conjecture as stated in OEIS**

> %N Table read by antidiagonals: T(n,k) (n >= 3, k >= 0) is the number of regions in an n-gon when k internal n-gons are drawn between the n*k points that divide each side into k+1 equal parts.  %C Conjecture: the only n-gons that contain non-simple intersections are the 3-gon (triangle), 4-gon (square), and 6-gon (hexagon).  %F Conjectured formula for all columns for n >= 7: T(n,k) = n*k^2 + 1.  %F Conjectured formula for all rows except for n = 3, 4, 6: T(n,k) = n*k^2 + 1.  (%A _Scott R. Shannon_, Sep 18 2022; the conjecture lines are unsigned, so they are the author's; rev #23, Sep 21 2022, unchanged upstream.)

**The frozen Lean statement**

```lean
noncomputable def vertex (n j : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * j / n)
noncomputable def divPt (n k j m : ℕ) : ℂ :=
  vertex n j + ((m : ℂ) / ((k : ℂ) + 1)) * (vertex n (j + 1) - vertex n j)
noncomputable def chord (n k : ℕ) (c : Fin n × Fin k) : Set ℂ :=
  segment ℝ (divPt n k (c.1 : ℕ) ((c.2 : ℕ) + 1)) (divPt n k ((c.1 : ℕ) + 1) ((c.2 : ℕ) + 1))
noncomputable def polygon (n : ℕ) : Set ℂ :=
  convexHull ℝ (Set.range fun j : Fin n => vertex n j)
noncomputable def regionSet (n k : ℕ) : Set ℂ :=
  interior (polygon n) \ ⋃ c : Fin n × Fin k, chord n k c
noncomputable def regions (n k : ℕ) : ℕ :=
  Nat.card (ConnectedComponents (regionSet n k))
def HasNonSimpleIntersection (n k : ℕ) : Prop :=
  ∃ p : ℂ, ∃ c₁ c₂ c₃ : Fin n × Fin k, c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃ ∧
    p ∈ chord n k c₁ ∧ p ∈ chord n k c₂ ∧ p ∈ chord n k c₃

def statement : Prop :=
  (∀ n : ℕ, 3 ≤ n → ((∃ k : ℕ, HasNonSimpleIntersection n k) ↔ (n = 3 ∨ n = 4 ∨ n = 6))) ∧
  (∀ n k : ℕ, (n = 5 ∨ 7 ≤ n) → regions n k = n * k ^ 2 + 1)

(Abridged: the file also defines a computable T n k by exact arithmetic in Z[2cos(2π/n)], and the sequence a, which reads T by antidiagonals. These are used only for the data check, not by `statement`.)
```

**What the Lean statement says**

Take the regular n-gon with vertices V_j = exp(2πij/n). For m = 1..k, let P_{j,m} be the point m/(k+1) of the way from V_j to V_{j+1}. The drawn segments are [P_{j,m}, P_{j+1,m}] for j = 0..n-1 and m = 1..k: the m-th internal n-gon joins the m-th points of consecutive sides, all counted in the same direction. (1) For every n ≥ 3, there is some k and some point of the plane lying on three distinct drawn segments if and only if n is 3, 4 or 6. (2) For n = 5 and every n ≥ 7, and every k ≥ 0, the open n-gon minus all n·k segments has exactly n·k^2 + 1 connected components.

**What the kernel checks against the OEIS data**

`theorem a_data` (decide +kernel) checks all 66 listed terms, which are antidiagonals n+k = 3..13. I compared the Lean list with the OEIS data and they match exactly. The check runs on the computable T, not on `regions` or `HasNonSimpleIntersection`, and the link T n k = regions n k is stated in the docstring but not proved. The kernel check therefore confirms the chord construction, which T shares (same index m on consecutive sides, boundary positions j(k+1)+m), but it does not formally pin down the topological definitions used in `statement`. The docstring also reports Python and floating-point cross-checks: the 195 EXAMPLE values for n = 3..15 and k = 0..14, and T(3,5)=70<76, T(4,5)=93<101 and T(6,9)=475<487 as the first triple-point deficits.

**Points for the reviewer**

- *Minor.* The kernel data check validates the computable T, not the geometric `regions` and `HasNonSimpleIntersection` that `statement` actually uses, and T = regions is not proved. A mistake in the topological encoding would not be caught by a_data. By reading, the encoding is literal and sound: open convex hull minus closed segments, Nat.card of the connected components, and k = 0 gives 1. Distinct chord indices give distinct, non-collinear segments, because a line meets the convex boundary in only 2 points. Also, the proved equality regions n k = n k^2 + 1 rules out a degenerate definition for n = 5 and n ≥ 7.
- *Note.* Construction reading: the m-th internal n-gon joins the m-th division points of consecutive sides, counted in the same direction, so each internal n-gon is a rotated, scaled copy of the outer one. For odd n this is the only rotationally symmetric pairing that closes up into n-gons, and the data (via T) confirm it. The polygon is taken to be regular, which is implicit in Shannon's sequences and images (for example T(5,20) = 2001 = 5·400+1).
- *Note.* A 'non-simple intersection' is encoded as a point on three or more distinct internal-polygon sides. The outer polygon's sides are not counted as lines. At each division point exactly two chords meet the outer side, so counting the side would make every n-gon non-simple and contradict the conjecture. No third chord can pass through a division point, because chord interiors lie in the open polygon.
- *Note.* Part (1) is an iff. Besides the conjecture's 'only' direction, it also asserts that n = 3, 4, 6 do have triple points for some k. That is supported by the data deficits and only strengthens the statement. Part (2) is exactly the union of the two %F conjectures: 'all columns for n >= 7' and 'all rows except n = 3, 4, 6', which also covers n = 5. Both are taken for all k ≥ 0.

## A357583: Kurkov's recursion for the row polynomials of convolution triangles holds

Verdict of the pre-review: **faithful**. Result: [oeis-a357583](../../results/oeis-a357583/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A357583.lean`](../../lean/Math0/Statements/OEIS/A357583.lean).

**The conjecture as stated in OEIS**

> %N Triangle read by rows. Convolution triangle of the Bell numbers.  %F Conjecture: row polynomials are x*R(n,1) for n > 0 where R(n,k) = R(n-1,k+1) + x*R(n-1,1)*R(1,k) for n > 1, k > 0 with R(1,k) = Bell(k) for k > 0. The same recursion seems to work for self-convolution of any other sequence. - _Mikhail Kurkov_, Apr 05 2025  (Entry by _Peter Luschny_, Oct 05 2022, offset 0; rev #10, Apr 06 2025, unchanged upstream. The same conjecture appears in A340991, whose %N reads 'Triangle T(n,k) whose k-th column is the k-fold self-convolution of the primes', with %F T(n,k) = [x^n] (Sum_{j>=1} prime(j)*x^j)^k.)

**The frozen Lean statement**

```lean
def pad (s : ℕ → R) (j : ℕ) : R := if j = 0 then 0 else s j
def convT (s : ℕ → R) : ℕ → ℕ → R
  | n, 0 => if n = 0 then 1 else 0
  | n, k + 1 => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, pad s p.1 * convT s p.2 k
def T (n k : ℕ) : ℕ := convT Nat.bell n k
noncomputable def R (s : ℕ → ℤ) : ℕ → ℕ → ℤ[X]
  | 0, _ => 0
  | 1, k => C (s k)
  | n + 2, k => R s (n + 1) (k + 1) + X * R s (n + 1) 1 * R s 1 k
def bellZ (k : ℕ) : ℤ := (Nat.bell k : ℤ)
noncomputable def rowPoly (s : ℕ → ℤ) (n : ℕ) : ℤ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (convT s n k) * X ^ k

def statement : Prop :=
  (∀ n : ℕ, 0 < n →
      ∑ k ∈ Finset.range (n + 1), C (T n k : ℤ) * X ^ k = X * R bellZ n 1) ∧
  (∀ s : ℕ → ℤ, ∀ n : ℕ, 0 < n → rowPoly s n = X * R s n 1)
```

**What the Lean statement says**

For a sequence s, let T_s(n,k) be the coefficient of z^n in (s(1)z + s(2)z^2 + ...)^k; the value s(0) plays no role. Define integer polynomials in x by R_s(1,k) = s(k) and R_s(n,k) = R_s(n-1,k+1) + x·R_s(n-1,1)·R_s(1,k) for n ≥ 2. (1) For s = the Bell numbers and every n ≥ 1, the sum of T(n,k)x^k over k = 0..n equals x·R(n,1). (2) The same identity holds for every integer sequence s and every n ≥ 1.

**What the kernel checks against the OEIS data**

`theorem T_data` checks all 11 listed rows n = 0..10 (66 entries). `theorem a_data` checks the 66 terms read by rows, a 0, ..., a 65. Both are kernel-checked (decide +kernel, via the proved rewrite T = Tfast), and the Lean list matches the OEIS data exactly. These checks pin down convT and pad for the Bell case: T(n,1) = Bell(n), and Bell(0) is not used. `convT_eq_coeff` proves convT s n k = [z^n](gf s)^k for every s, which pins down the general triangle. R has no kernel check, but it transcribes the recursion literally. I checked the identity by hand for n ≤ 3 (Bell case) and numerically for n ≤ 8 with a random integer sequence.

**Points for the reviewer**

- *Note.* The second sentence ('the same recursion seems to work for self-convolution of any other sequence') is read as: for every s : ℕ → ℤ, the convolution triangle T_s(n,k) = [z^n](Σ_{j≥1} s(j)z^j)^k has row polynomials x·R_s(n,1), where R_s(1,k) = s(k). This matches A357368's PMatrix terminology and A340991's 'k-th column is the k-fold self-convolution'. Because s ranges over all integer sequences, it also covers 0-based or shifted conventions by relabelling. The identity is polynomial in the s(j), so the integer case implies it over any commutative ring. If anything, the formal version is at least as strong as any narrower reading.
- *Note.* Junk values: R s 0 k = 0, and R at k = 0, are never reached starting from R s n 1 with n ≥ 1. Since n > 0 is required, the n = 0 row (polynomial 1 versus x·R(0,1) = 0) is correctly excluded.
- *Note.* Catalog metadata, not the statement: the catalog entry's area is 'Discrete geometry'. It should be combinatorics or enumerative combinatorics.

## A362086: OEIS A362086: every denominator of 1/(2-3/(3-4/(...(n-1)-n/(-3)))) except 9 is 1 or a prime

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a362086](../../results/oeis-a362086/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A362086.lean`](../../lean/Math0/Statements/OEIS/A362086.lean).

**The conjecture as stated in OEIS**

> %N Denominator of the continued fraction 1/(2-3/(3-4/(4-5/(...(n-1)-n/(-3))))).  %C Conjecture: Except for 9, every term of this sequence is either a prime or 1.  (%A _Mohammed Bouras_, May 28 2023; offset 3; rev #35, May 09 2024, unchanged upstream. %e: for n=3, 1/(2 - 3/(-3)) = 1/3, so a(3)=3; n=4: 13/17; n=5: 13/9.)

**The frozen Lean statement**

```lean
def step (k : ℕ) (t : ℚ) : ℚ := (k : ℚ) - ((k : ℚ) + 1) / t
def cf (n : ℕ) : ℚ := 1 / (List.range' 2 (n - 2)).foldr step (-3)
def a (n : ℕ) : ℕ := (cf n).den

def statement : Prop :=
  ∀ n : ℕ, 3 ≤ n → a n ≠ 9 → a n = 1 ∨ (a n).Prime
```

**What the Lean statement says**

For every n ≥ 3, start with t = -3 and, for k = n-1 down to 2, replace t by k - (k+1)/t (rational arithmetic, with x/0 = 0). Let a(n) be the reduced denominator of 1/t. Then for every n ≥ 3, if a(n) is not 9, a(n) is 1 or a prime.

**What the kernel checks against the OEIS data**

`example : cf 3 = 1/3 ∧ cf 4 = 13/17 ∧ cf 5 = 13/9`, which matches the three %e examples exactly, and `theorem a_data`, which checks all 57 listed terms a 3, ..., a 59. Both are kernel-checked, and the Lean list matches the OEIS data exactly. The definition transcribes %N literally, and the examples fix the shape: the innermost level is (n-1) - n/(-3), and for n = 3 it is the single level 2 - 3/(-3).

**Points for the reviewer**

- *Minor.* 'Except for 9' is encoded as exempting every n with a n = 9. On a strict reading, the author is excepting the single term a(5) = 9. The Lean statement is therefore formally weaker by the claim 'the value 9 occurs only once', since a second 9 would refute the strict reading but not the Lean statement. The gap does not matter in practice. Exact computation shows 9 occurs only at n = 5 for 3 ≤ n < 1200. Using the closed form a(n) = N/gcd(N, 3(n-1)(n-3)!) with N = n^2+n-3 (which I checked against exact evaluation for n < 400), 9 | a(n) needs v_3(N) ≥ 3 + v_3((n-3)!), which is impossible for n ≥ 15 or so. The index reading (n = 9) is untenable, because a(5) = 9 is not prime.
- *Note.* Junk values: no tail vanishes. t_{n-1} = (n-1)+n/3 ≥ 2, the later tails stay positive down to t_3, and t_2 ≠ 0 because the closed-form numerator 3·A051403(n-3)+n·A051403(n-4) is positive. I checked by exact arithmetic that no tail vanishes for 3 ≤ n < 1200. A vanishing t_2 would have made a n = 1 trivially. The definition therefore matches the true continued fraction for all n ≥ 3.

## A363482: OEIS A363482: apart from 49, every denominator of 1/(2-3/(3-4/(...(n-1)-n/(-5)))) is 1 or a prime

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a363482](../../results/oeis-a363482/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A363482.lean`](../../lean/Math0/Statements/OEIS/A363482.lean).

**The conjecture as stated in OEIS**

> %N Denominator of the continued fraction 1/(2-3/(3-4/(4-5/(...(n-1)-n/(-5))))).  %C Conjecture: Except for 49, every term of this sequence is either a prime or 1.  (%A _Mohammed Bouras_, Jun 04 2023; offset 3; rev #29, Jul 13 2025, unchanged upstream. %e: n=3: 5/13, n=4: 19/23, n=5: 11/7. McEachen, Jul 08 2025: 'The conjecture holds through n=10000.')

**The frozen Lean statement**

```lean
def step (k : ℕ) (t : ℚ) : ℚ := (k : ℚ) - ((k : ℚ) + 1) / t
def cf (n : ℕ) : ℚ := 1 / (List.range' 2 (n - 2)).foldr step (-5)
def a (n : ℕ) : ℕ := (cf n).den

def statement : Prop :=
  ∀ n : ℕ, 3 ≤ n → a n ≠ 49 → a n = 1 ∨ (a n).Prime
```

**What the Lean statement says**

For every n ≥ 3, start with t = -5 and, for k = n-1 down to 2, replace t by k - (k+1)/t (rational arithmetic, with x/0 = 0). Let a(n) be the reduced denominator of 1/t. Then for every n ≥ 3, if a(n) is not 49, a(n) is 1 or a prime.

**What the kernel checks against the OEIS data**

`example : cf 3 = 5/13 ∧ cf 4 = 19/23 ∧ cf 5 = 11/7`, which matches the three %e examples, and `theorem a_data`, which checks all 61 listed terms a 3, ..., a 63 (including a 6 = 49 and a 12 = 1). Both are kernel-checked, and the Lean list matches the OEIS data exactly. The definition transcribes %N literally.

**Points for the reviewer**

- *Minor.* 'Except for 49' is encoded as exempting every n with a n = 49. On a strict reading, the author is excepting the single term a(6) = 49, so the Lean statement is weaker by 'the value 49 occurs only once'. The gap does not matter in practice. Exact computation shows 49 occurs only at n = 6 for 3 ≤ n < 1200. Using the closed form a(n) = N/gcd(N, 5(n-1)(n-3)!) with N = n^2+3n-5 (which I checked for n < 400), 49 | a(n) needs v_7(N) ≥ 2 + v_7(5(n-1)(n-3)!), which fails for all n beyond about 50 because of size. The catalog summary itself states that 49 occurs only at n = 6.
- *Note.* Junk values: t_{n-1} = (n-1)+n/5 > 0, the later tails are positive down to t_3, and t_2 ≠ 0 because the closed-form numerator 5·A051403(n-3)+n·A051403(n-4) is positive. I checked by exact arithmetic that no tail vanishes for 3 ≤ n < 1200. Lean's x/0 = 0 therefore never comes into play for n ≥ 3.

## A363609: A363609: a(k^3) = 6k(k+2), the cube is the optimal polycube of k^3 dice

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a363609](../../results/oeis-a363609/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A363609.lean`](../../lean/Math0/Statements/OEIS/A363609.lean).

**The conjecture as stated in OEIS**

> %F A363609 Conjecture: a(k^3) = 6*(k+2)*k for k > 1.  (Unattributed formula line; entry by _Matt Donahoe_, Jun 11 2023, rev #45 Sep 03 2023. Name: "Minimum sum of the visible pips on a polycube made from n dice." Comment: "This sequence is calculated using standard six-sided dice of the same chirality. Opposite sides sum to seven." Offset 1. Example: "For n = 2, two dice are conjoined to hide both their 6-pip faces, so a(2) = 30.")

**The frozen Lean statement**

```lean
def statement : Prop := ∀ k : ℕ, 1 < k → a (k ^ 3) = 6 * (k + 2) * k

-- dependencies (verbatim, abridged to the definitional core)
abbrev Cell := ℤ × ℤ × ℤ
def dirs : Finset Cell := {(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)}
def IsOrientation (o : Cell × Cell) : Prop := o.1 ∈ dirs ∧ o.2 ∈ dirs ∧ dot o.1 o.2 = 0
def pips (o : Cell × Cell) (d : Cell) : ℕ :=
  if d = o.1 then 1 else if d = o.2 then 2 else if d = cross o.1 o.2 then 3
  else if d = -cross o.1 o.2 then 4 else if d = -o.2 then 5 else if d = -o.1 then 6 else 0
def visiblePips (P : Finset Cell) (o : Cell → Cell × Cell) : ℕ :=
  ∑ c ∈ P, ∑ d ∈ dirs, if c + d ∈ P then 0 else pips (o c) d
def Adj (P : Finset Cell) (u v : Cell) : Prop := u ∈ P ∧ v ∈ P ∧ v - u ∈ dirs
def FaceConnected (P : Finset Cell) : Prop := ∀ x ∈ P, ∀ y ∈ P, Relation.ReflTransGen (Adj P) x y
def totals (n : ℕ) : Set ℕ :=
  {t | ∃ P : Finset Cell, P.card = n ∧ FaceConnected P ∧
    ∃ o : Cell → Cell × Cell, (∀ c ∈ P, IsOrientation (o c)) ∧ visiblePips P o = t}
noncomputable def a (n : ℕ) : ℕ := sInf (totals n)
```

**What the Lean statement says**

Place one die in each cell of a finite face-connected set P of unit cubes in Z^3. Each die is independently given one of the 24 rotations of a fixed right-handed die (1 on u, 2 on v, 3 on u×v, and 7−k opposite the k-face). A face of a die counts if the neighbouring cell in that direction is not in P (this includes bottom faces and faces facing an enclosed empty cell). a(n) is the least possible total of counted pips over all such n-cell polycubes and all orientations. Claim: for every integer k ≥ 2, a(k^3) = 6k(k+2).

**What the kernel checks against the OEIS data**

wits_ok / a_le_data: for every one of the 57 listed terms a(1..57), a kernel-checked face-connected witness polycube attains the listed value, so a(n) ≤ listed value. a_data: kernel-checked exhaustive enumeration (up to the 48 cube symmetries) gives the exact values a(1..7) = 21, 30, 40, 40, 51, 52, 54. These pin down that all six faces count (a(1) = 21), that opposite faces sum to 7 (a(2) = 30), face-connectivity, and the per-die minimisation. For n = k^3 only upper bounds are checked (a(8) ≤ 48, a(27) ≤ 90). Neither chirality nor the cavity convention is pinned, since no polycube with ≤ 7 cells encloses a cavity.

**Points for the reviewer**

- *Minor.* Faces that face an enclosed cavity count as visible. The file justifies this by the listed a(26) = 93: under the other reading, the 3×3×3 cube minus its centre would give ≤ 90. But Donahoe's dice.py only searches box-plus-slab layouts and never builds a cavity, so the data are weak evidence either way. The Lean reading matches the author's convention that every exposed face counts, bottom faces included (a(1) = 21), so it is the natural one. Under the other reading, the Lean result gives only a(k^3) ≤ 6k(k+2), not equality. The projection-type lower bound plausibly also holds there, but that is not part of this statement.
- *Note.* Every die uses the same right-handed numbering. The entry says only "same chirality". Reflecting the whole configuration swaps the chiralities and keeps the pip total, so the minimum is the same either way.
- *Note.* The data values come from a heuristic search, so the Lean a(n) (a true minimum over all polycubes) could in principle fall below a listed term for some n. This does not affect the k^3 statement, whose upper bound comes from the cube.

## A367119: Edges of the all-chords graph of a triangle with n general-position points per side (A367119)

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a367119](../../results/oeis-a367119/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A367119.lean`](../../lean/Math0/Statements/OEIS/A367119.lean).

**The conjecture as stated in OEIS**

> %F A367119 Conjecture: a(n) = (3/2)*(3*n^4 + 4*n^3 + 3*n^2 + 4*n + 2).  (_Scott R. Shannon_ and _N. J. A. Sloane_, Nov 05 2023; rev #14 Nov 09 2023.) Name: "Place n points in general position on each side of an equilateral triangle, and join every pair of the 3*n+3 boundary points by a chord; sequence gives number of edges in the resulting planar graph." Comment: "'In general position' implies that the internal lines (or chords) only have simple intersections. There is no interior point where three or more chords meet." Offset 0.

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ (n : ℕ) (B : Finset ℂ), IsPlacement n B → GeneralPosition B →
    (edges B : ℚ) = 3 / 2 * (3 * n ^ 4 + 4 * n ^ 3 + 3 * n ^ 2 + 4 * n + 2)

-- dependencies (verbatim)
noncomputable def corner : Fin 3 → ℂ := ![0, 1, ⟨1 / 2, Real.sqrt 3 / 2⟩]
noncomputable def triangle : Set ℂ := convexHull ℝ (Set.range corner)
def IsPlacement (n : ℕ) (B : Finset ℂ) : Prop :=
  (∀ j : Fin 3, corner j ∈ B) ∧
  (∀ z ∈ B, ∃ j : Fin 3, z ∈ segment ℝ (corner j) (corner (j + 1))) ∧
  (∀ j : Fin 3, ((B : Set ℂ) ∩ openSegment ℝ (corner j) (corner (j + 1))).ncard = n)
def drawn (B : Finset ℂ) : Set (Set ℂ) := {s | ∃ p ∈ B, ∃ q ∈ B, p ≠ q ∧ s = segment ℝ p q}
def GeneralPosition (B : Finset ℂ) : Prop :=
  ∀ z ∈ interior triangle, ∀ s₁ ∈ drawn B, ∀ s₂ ∈ drawn B, ∀ s₃ ∈ drawn B,
    z ∈ s₁ → z ∈ s₂ → z ∈ s₃ → s₁ = s₂ ∨ s₁ = s₃ ∨ s₂ = s₃
def vertices (B : Finset ℂ) : Set ℂ := (B : Set ℂ) ∪ {z | ∃ s ∈ drawn B, ∃ t ∈ drawn B, s ∩ t = {z}}
def planarGraph (B : Finset ℂ) : SimpleGraph ℂ :=
  SimpleGraph.fromRel fun u v =>
    u ∈ vertices B ∧ v ∈ vertices B ∧ (∃ s ∈ drawn B, u ∈ s ∧ v ∈ s) ∧
      ∀ w ∈ vertices B, w ∉ openSegment ℝ u v
noncomputable def edges (B : Finset ℂ) : ℕ := (planarGraph B).edgeSet.ncard
```

**What the Lean statement says**

Fix the equilateral triangle with corners 0, 1 and 1/2 + (√3/2)i. Let B be the three corners plus exactly n points in the open interior of each side, and nothing else. Draw the segment between every pair of distinct points of B. Assume that no point of the open triangle lies on three distinct drawn segments. The vertices of the graph are B together with every point where two drawn segments meet in exactly one point. The edges join two vertices that lie on a common drawn segment with no vertex strictly between them. Claim: for every n ≥ 0 and every such B, the number of edges is (3/2)(3n^4 + 4n^3 + 3n^2 + 4n + 2).

**What the kernel checks against the OEIS data**

a_data checks a 0, …, a 10 = 3, 24, 153, 588, 1635, 3708, 7329, 13128, 21843, 34320, 51513 in the kernel. Here `a` is a combinatorial surrogate: 3n+3 boundary edges plus the sum over interior chords of (1 + number of interleaving chords). The file states but does not prove that a n = edges B, so the kernel check does not pin down the geometric definitions used in `statement`. As an independent check, I computed the geometric definition exactly (rational arithmetic, random side points on an affine image of the triangle, vertices = B ∪ singleton intersections, edges = consecutive vertex pairs on drawn segments) for n = 0..4. It gives 3, 24, 153, 588, 1635, which agree with the data and the formula.

**Points for the reviewer**

- *Minor.* The kernel data check is on the computable surrogate `a`, which is not linked to `edges`. So the geometric statement's definitions (vertices, adjacency, placement, general position) are validated only by inspection and by my numerical check, not by a kernel-checked term. On inspection they are correct: chords cannot overlap; side pieces overlapping on a common side are excluded from the vertices by the `s ∩ t = {z}` clause; consecutive boundary points give the 3n+3 side edges; and n = 0 gives 3.
- *Note.* "General position" is read exactly as the entry's comment: no three distinct drawn segments meet at an interior point. Since this is the weakest reading and the statement quantifies over all such B, the statement is at least as strong as intended. General-position placements exist for every n (generic points), so the statement is not vacuous, though the file does not prove this.
- *Note.* The entry presupposes that the edge count does not depend on B. The Lean statement asserts the formula for every admissible B, which is the right reading.

## A368846: Diagonal sums of A368846 equal A229580 (Luschny's conjecture)

Verdict of the pre-review: **faithful**. Result: [oeis-a368846](../../results/oeis-a368846/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A368846.lean`](../../lean/Math0/Statements/OEIS/A368846.lean).

**The conjecture as stated in OEIS**

> %C A368846 Conjecture: |Sum_{j=0..k} T(k + j, k)| = A229580(k + 1) for k >= 0.  (_Peter Luschny_, Jan 07 2024; rev #26 Feb 17 2025.) Name: "Triangle read by rows: T(n, k) = (-1)^(n + k)*2*binomial(2*k - 1, n)* binomial(2*n + 1, 2*k) for k > 0, and k^n for k = 0." Offset 0. A229580 (R. H. Hardin, offset 1): "Number of defective 3-colorings of an n X 2 0..2 array connected horizontally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..2 order."

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ k : ℕ, |∑ j ∈ Finset.range (k + 1), T (k + j) k| = (A229580 (k + 1) : ℤ)

-- dependencies (verbatim)
def T (n k : ℕ) : ℤ :=
  if k = 0 then 0 ^ n
  else (-1) ^ (n + k) * 2 * ((2 * k - 1).choose n : ℤ) * ((2 * n + 1).choose (2 * k) : ℤ)
abbrev Cell (n : ℕ) := Fin n × Fin 2
def Cell.rank {n : ℕ} (p : Cell n) : ℕ := 2 * p.1.val + p.2.val
def IsEdge {n : ℕ} (p q : Cell n) : Prop :=
  (p.1 = q.1 ∧ p.2 = 0 ∧ q.2 = 1) ∨ (p.1.val + 1 = q.1.val ∧ p.2 = 1 ∧ q.2 = 0)
def mistakes {n : ℕ} (c : Cell n → Fin 3) : ℕ :=
  (Finset.univ.filter fun e : Cell n × Cell n => IsEdge e.1 e.2 ∧ c e.1 = c e.2).card
def ColorsInOrder {n : ℕ} (c : Cell n → Fin 3) : Prop :=
  ∀ p : Cell n, c p ≠ 0 → ∃ q : Cell n, q.rank < p.rank ∧ (c q).val + 1 = (c p).val
def A229580 (n : ℕ) : ℕ :=
  (Finset.univ.filter fun c : Cell n → Fin 3 => mistakes c = 1 ∧ ColorsInOrder c).card
```

**What the Lean statement says**

Let T(n,k) = (−1)^(n+k)·2·C(2k−1,n)·C(2n+1,2k) for k ≥ 1, and T(n,0) = 0^n (so T(0,0) = 1). Let A229580(m) count the 3-colourings of an m-row, 2-column array whose colour word, read in row-major order, is a restricted growth word (one representative per relabelling of colours), and which have exactly one monochromatic edge. The edges are the horizontal ones (i,0)–(i,1) and the antidiagonal ones (i,1)–(i+1,0). Claim: for every k ≥ 0, |T(k,k) + T(k+1,k) + … + T(2k,k)| = A229580(k+1), as integers.

**What the kernel checks against the OEIS data**

a_data checks all 55 listed terms of the triangle (rows 0..9) in the kernel, which pins T, including T(0,0) = 1 and the sign. A229580_data checks A229580(1..3) = 1, 6, 40 from the colouring definition. sum_data shows that the left-hand side for k = 0..21 equals the 22 listed terms of A229580. statement_check confirms the full equation with the Lean A229580 for k = 0, 1, 2. The data do not distinguish antidiagonal from diagonal edges, but this does not affect the count: either way the graph is a path on the 2n cells, and the restricted-growth condition picks one colouring per orbit of colour permutations whatever the cell order. The entry's first example solution (0 1 / 0 0 / 1 0) confirms the antidiagonal reading.

**Points for the reviewer**

- *Note.* Only A229580(1..3) are kernel-checked against the colouring definition, since larger n are too slow. The definition is robust, though: ColorsInOrder is equivalent to the row-major word being a restricted growth word, and the n×2 orientation (n rows, 2 columns) is fixed by the entry's 3×2 examples and the value 40.
- *Note.* T is evaluated only at (k+j, k) with 0 ≤ j ≤ k, which lies inside the triangle. The natural-number subtraction 2k−1 is used only for k ≥ 1, so it never truncates.

## A369366: The least number of inequivalent cells of a (6k+5)-iamond is 3(k+1)

Verdict of the pre-review: **faithful**. Result: [oeis-a369366](../../results/oeis-a369366/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A369366.lean`](../../lean/Math0/Statements/OEIS/A369366.lean).

**The conjecture as stated in OEIS**

> %C A369366 Conjecture: a(6k+5) = 3(k+1) for all k >= 0. Observed for k = 0, 1, 2 (n = 5, 11, 17). The next test case is a(23), predicted to be 12.  (From _Peter Exley_, Apr 07 2026; rev #14 Apr 14 2026.) Name: "Least number of inequivalent cells in a polyiamond with n cells." Comment: "Equivalently, a(n) is the least number of free rooted (or pointed) polyiamonds (A369365) corresponding to a given polyiamond with n cells." Offset 1.

**The frozen Lean statement**

```lean
def statement : Prop := ∀ k : ℕ, a (6 * k + 5) = 3 * (k + 1)

-- dependencies (verbatim, abridged)
abbrev Pt := ℤ × ℤ × ℤ
def sumC (x : Pt) : ℤ := x.1 + x.2.1 + x.2.2
def IsCell (x : Pt) : Prop := sumC x = 0 ∨ sumC x = 1
def Adj (x y : Pt) : Prop := |y.1 - x.1| + |y.2.1 - x.2.1| + |y.2.2 - x.2.2| = 1
-- perm s : the 6 coordinate permutations; lin s neg x := if neg then -perm s x else perm s x
structure Isom where s : Fin 6; neg : Bool; t : Pt; ht : sumC t = tReq neg   -- tReq neg = if neg then 1 else 0
def Isom.app (g : Isom) (x : Pt) : Pt := lin g.s g.neg x + g.t
def IsConnected (P : Finset Pt) : Prop := ∀ x ∈ P, ∀ y ∈ P, Relation.ReflTransGen (Step P) x y
def IsPolyiamond (n : ℕ) (P : Finset Pt) : Prop := P.card = n ∧ (∀ x ∈ P, IsCell x) ∧ IsConnected P
def Equivalent (P : Finset Pt) (c d : Pt) : Prop := ∃ g : Isom, P.image g.app = P ∧ g.app c = d
noncomputable def cls (P : Finset Pt) (c : Pt) : Finset Pt := P.filter (Equivalent P c)
noncomputable def numClasses (P : Finset Pt) : ℕ := (P.image (cls P)).card
noncomputable def a (n : ℕ) : ℕ := sInf {m | ∃ P : Finset Pt, IsPolyiamond n P ∧ numClasses P = m}
```

**What the Lean statement says**

Label the triangles of the triangular grid by integer triples with coordinate sum 0 or 1; two triangles share an edge exactly when their labels differ by ±1 in one coordinate. A polyiamond with n cells is an edge-connected set of n triangles (holes allowed). Two of its cells are equivalent if some symmetry of the grid (translations, rotations by multiples of 60°, and reflections: the full p6m group) maps the polyiamond onto itself and one cell to the other. a(n) is the least number of equivalence classes over all n-cell polyiamonds. Claim: for every k ≥ 0, a(6k+5) = 3(k+1).

**What the kernel checks against the OEIS data**

a_eq_aComp proves that `a` equals a kernel-computable enumeration of free polyiamonds up to grid symmetry, for all n ≥ 1. a_data then checks a(1..8) = 1, 1, 2, 2, 3, 1, 3, 3 in the kernel. These values pin down that reflections are included (with rotations only, a(5) would be 5, not 3), that adjacency is by edges, and the grid model (a(6) = 1 for the hexagon). a(11) and a(17), the k = 1, 2 cases, are not kernel-checked.

**Points for the reviewer**

- *Note.* The 12 point-group maps (6 coordinate permutations × ±) together with translations of coordinate sum 0 (or 1 for the negated maps) are exactly the symmetries of the triangular grid, and adjacency is invariant under them. The file's remark that plane isometries preserving a polyiamond are grid symmetries justifies using grid symmetries instead of arbitrary isometries.
- *Note.* a 0 = 0 (empty polyiamond) is a junk value outside the offset; the statement only evaluates a at 6k+5 ≥ 5.

## A373345: Row lengths of the Schreier-set triangle A373345 are A007895 (number of Zeckendorf summands)

Verdict of the pre-review: **faithful**. Result: [oeis-a373345](../../results/oeis-a373345/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A373345.lean`](../../lean/Math0/Statements/OEIS/A373345.lean).

**The conjecture as stated in OEIS**

> %Y A373345 Cf. A007895 (conjectured row lengths), A072649 (first column), A373346 (row sums), A373347.  (_Paolo Xausa_, Jun 01 2024; rev #45 Sep 13 2024.) Name: "Irregular triangle read by rows where row n lists (in decreasing order) the elements of the Schreier set encoded by A371176(n)." Comment: "Each term k of A371176 can be put into a one-to-one correspondence with a Schreier set by interpreting the 1-based position of the ones in the binary expansion of k (where position 1 corresponds to the least significant bit) as the elements of the corresponding Schreier set." Offset 1. A371176: "Numbers k such that A000120(k) <= A001511(k)." A007895 (offset 0): "Number of terms in the Zeckendorf representation of n."

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n → (T n).length = (Nat.zeckendorf n).length

-- dependencies (verbatim)
def IsTerm (k : ℕ) : Prop := 0 < k ∧ k.bitIndices.length ≤ padicValNat 2 (2 * k)
noncomputable def A371176 (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)
noncomputable def T (n : ℕ) : List ℕ := ((A371176 n).bitIndices.map (· + 1)).reverse
```

**What the Lean statement says**

Let A371176 be the increasing list of positive integers k whose binary weight is at most the 2-adic valuation of 2k, and let A371176(n) be its n-th term (n ≥ 1). Row n of the triangle is the list of 1-based positions of the 1-bits of A371176(n), in decreasing order. Claim: for every n ≥ 1, the length of row n (the binary weight of A371176(n)) equals the number of terms in the Zeckendorf representation of n (the length of Mathlib's Nat.zeckendorf n).

**What the kernel checks against the OEIS data**

a_data checks all 91 listed terms (rows 1..42) of the flattened triangle in the kernel. code_data checks the first 42 terms of A371176 = 1, 2, 4, 6, 8, 10, 12, 16, …, 160. statement_check confirms the claimed equality for n = 1..42, which fixes the alignment of row n with A007895(n), not A007895(n−1). These checks are tied to the noncomputable definitions by proved equalities (code_eq_nth, row_eq_T, zeckAux_eq), and they pin the definitions of A371176 (including the exclusion of k = 0) and of the rows.

**Points for the reviewer**

- *Note.* The conjecture appears only as a cross-reference ("A007895 (conjectured row lengths)"). The Lean reading, row n has A007895(n) elements for n ≥ 1, is the only alignment consistent with the data (row 1 = {1} has length 1 = A007895(1), while A007895(0) = 0), and it covers all rows.
- *Note.* Nat.nth IsTerm is total and genuine here, because IsTerm holds for every power of two, so the set is infinite. The guard 0 < k correctly excludes k = 0, which A371176 omits.
