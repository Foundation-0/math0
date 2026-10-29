# Fidelity review packet 02 of 11

Prepared on 29 Oct 2026 by an adversarial reviewing agent, not by a person. It is meant to make a human review of these statements quick: for each one it quotes the OEIS conjecture and the frozen Lean statement, restates the Lean in plain words, and lists anything a reviewer should look at. See [the index](README.md).

Statements in this packet: A081200, A083020, A086004, A090905, A091817, A092054, A093726, A097154, A106505, A113676.

## A081200: Collinear 5-point sets in the grid {0,…,4}^n number (7^n − 5^n)/2 (Hardin's conjecture, A081200)

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a081200](../../results/oeis-a081200/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A081200.lean`](../../lean/Math0/Statements/OEIS/A081200.lean).

**The conjecture as stated in OEIS**

> %C A081200 Conjecture (verified up to a(9)): Number of collinear 5-tuples of points in a 5 X 5 X 5 X ... n-dimensional cubic grid. - _Ron Hardin_, May 24 2010
> (%N: 6th binomial transform of (0,1,0,1,0,1,...), A000035. Offset 0.)

**The frozen Lean statement**

```lean
def binomialTransform (m : ℕ) (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), n.choose k * m ^ (n - k) * b k
def A000035 (k : ℕ) : ℕ := k % 2
def a (n : ℕ) : ℕ := binomialTransform 6 A000035 n
def toReal (n : ℕ) (x : Fin n → Fin 5) : Fin n → ℝ := fun i => ((x i : ℕ) : ℝ)

def statement : Prop :=
  ∀ n : ℕ,
    {s : Finset (Fin n → Fin 5) |
        s.card = 5 ∧ Collinear ℝ (toReal n '' (s : Set (Fin n → Fin 5)))}.ncard = a n
```

**What the Lean statement says**

For every n ≥ 0, the number of 5-element subsets of the grid {0,1,2,3,4}^n, viewed in R^n, that lie on a single real line equals sum_{k=0}^{n} C(n,k) 6^(n-k) (k mod 2), i.e. the 6th binomial transform of 0,1,0,1,... (which is (7^n - 5^n)/2).

**What the kernel checks against the OEIS data**

a_data: kernel-checks all 23 listed terms a(0..22) against the binomial-transform definition, so the sequence side is fully pinned (and equals the OEIS %N definition, not a closed form). There is no kernel check of the counting side. I brute-forced it independently: the count is 1 for n=1 and 12 for n=2, matching a(1), a(2). It also matches the classical ((k+2)^n - k^n)/2 count of lines for k=5. Unordered sets are the only reading that fits a(1)=1, since ordered 5-tuples would give 120.

**Points for the reviewer**

- *Note.* "5-tuples" is read as unordered 5-element sets. The data forces this reading (a(1)=1, a(2)=12). In a 5^n grid, a collinear set of 5 distinct points must be a full grid line, so Collinear ℝ (vector span of rank at most 1) matches the intended notion.
- *Note.* The statement also covers n = 0, which Hardin's "n-dimensional grid" probably did not intend. There the grid is one point, the count is 0 and a(0) = 0, so the extra case is true and harmless. Set.ncard is applied to a set of Finsets of a finite type, so it is a genuine count, not a junk 0.

## A083020: 3^(3^18) + 2 is divisible by 31^2, so Hilliard's squarefree conjecture (A083020) fails

Verdict of the pre-review: **faithful**. Result: [oeis-a083020](../../results/oeis-a083020/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A083020.lean`](../../lean/Math0/Statements/OEIS/A083020.lean).

**The conjecture as stated in OEIS**

> %C A083020 Conjecture: These numbers have no repeating factors or 3^(3^n) + 2 is squarefree.
> (%N: Irregular triangle read by row of the prime factors of 3^(3^n) + 2. Offset 0. Entry by _Cino Hilliard_, May 31 2003; the comment carries no separate attribution.)

**The frozen Lean statement**

```lean
def N (n : ℕ) : ℕ := 3 ^ (3 ^ n) + 2
def row (n : ℕ) : List ℕ := Nat.primeFactorsList (N n)

def statement : Prop :=
  ∀ n : ℕ, Squarefree (3 ^ (3 ^ n) + 2)

(also proved: statement_iff : statement ↔ ∀ n, (row n).Nodup)
```

**What the Lean statement says**

For every n ≥ 0, the number 3^(3^n) + 2 is squarefree (no prime square divides it).

**What the kernel checks against the OEIS data**

row_data proves rows 0..4 of the triangle by Lucas/Pratt certificates (5; 29; 5·31·127; 11·693236134999; 5·15679·2372959·5945531·3312453269·121032673159). a_data checks a(0..12). N5_data checks that the 116-digit listed term equals 3^243+2, but its primality is not proved. row6_data checks that row 6 begins 5, 31. The data only serves to confirm N n = 3^(3^n)+2 and the row indexing. The statement itself uses the closed form directly, so nothing in it depends on the data. The result (¬ statement) uses n = 18, p = 31. I confirmed independently that (3^(3^18) + 2) mod 961 = 0. It is also the smallest n with p^2 | N(n) over primes p < 2000.

**Points for the reviewer**

- *Note.* "These numbers have no repeating factors" could be misread as "no prime appears twice anywhere in the sequence". That reading is already false from the listed data (5 appears in rows 0, 2, 4 and 6). The author's own "or 3^(3^n)+2 is squarefree" fixes the meaning as per-row squarefreeness. statement_iff shows this is the same as no repeated prime within a row.
- *Note.* The range n ≥ 0 matches the triangle's offset 0 (row 0 is 3^1+2 = 5). The refutation uses n = 18, which is well inside any reasonable range, so the range choice cannot affect the result.

## A086004: There are no 5-Rotation Cycle Primes (A086004, Conjecture 2)

Verdict of the pre-review: **faithful**. Result: [oeis-a086004](../../results/oeis-a086004/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A086004.lean`](../../lean/Math0/Statements/OEIS/A086004.lean).

**The conjecture as stated in OEIS**

> %C A086004 Conjecture 2: There are no 5-Rotation Cycle Primes.
> (Entry by _Chuck Seggelin_, Jul 07 2003. Context in the entry: %N "Primes which remain prime after one and after two and after three applications of the rotate-and-add operation of A086002"; "Note: Have not yet found any 4-Rotation Cycle Primes."; Chai Wah Wu, Aug 20 2015: "4-Rotation Cycle Primes exist and are listed in A261458" — A261458 = primes which remain prime after one, two, three and four applications.)

**The frozen Lean statement**

```lean
def rot (n : ℕ) : ℕ :=
  let d := (Nat.digits 10 n).length
  let l := d / 2
  let h := d - l
  n % 10 ^ l * 10 ^ h + n / 10 ^ l % 10 ^ (h - l) * 10 ^ l + n / 10 ^ h
def rotAdd (n : ℕ) : ℕ := n + rot n
def IsRotationCyclePrime (k p : ℕ) : Prop :=
  p.Prime ∧ ∀ j, 1 ≤ j → j ≤ k → (rotAdd^[j] p).Prime

def statement : Prop :=
  ∀ p : ℕ, ¬ IsRotationCyclePrime 5 p
```

**What the Lean statement says**

Let rot(n) swap the block of the first floor(d/2) decimal digits of n with the block of the last floor(d/2) digits, where d is the digit count and the centre digit stays in place when d is odd. Let f(n) = n + rot(n). Then no prime p has f(p), f(f(p)), f^3(p), f^4(p) and f^5(p) all prime.

**What the kernel checks against the OEIS data**

rot_examples checks the A086002 examples (rot 1234 = 3412, rot 12345 = 45312) and the A086003/A086004 chain 12917 → 30829 → 60659 → 120319. It also checks the 11-digit A261458 chain 10010905789 → … → 126399526399. rot_eq_rotDigits_data checks the arithmetic rot against a digit-list version for all n < 2000 and on the example numbers. a_data checks a(1..13), all listed terms below 10^8, using a kernel scan that proves the 3-Rotation Cycle Primes below 1530000 are exactly those 13. Independently, I compared the Lean formula with the entry's Mathematica rot on 200,000 random numbers of up to 15 digits and they always agreed. Together these pin rot and the k-step notion.

**Points for the reviewer**

- *Note.* The term "k-Rotation Cycle Prime" is never defined explicitly in the entry. The Lean reading is: p prime, and f^j(p) prime for every j = 1..k. Several things support it: the name of A086004 ("remain prime after one and after two and after three applications") alongside the note about 4-Rotation Cycle Primes, Wu's identification of 4-Rotation Cycle Primes with A261458 ("after one, two, three and four applications"), and the fact that a_data reproduces A086004 as the k=3 case. I see no other plausible reading.
- *Note.* Leading zeros produced by rotation are handled the way Mathematica's FromDigits handles them: rot(1203) = 312. A055642(0)=1 differs from (Nat.digits 10 0).length = 0, but only primes and their images matter, and those are all ≥ 2.

## A090905: A090905: every row ends at twice the largest prime of the previous row (Murthy's conjecture proved)

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a090905](../../results/oeis-a090905/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A090905.lean`](../../lean/Math0/Statements/OEIS/A090905.lean).

**The conjecture as stated in OEIS**

> %C A090905 Conjecture: For n > 4 the last term of the n-th group is 2p where p is the largest prime in the (n-1)th group. And these are the Bertrand primes.
> (Entry by _Amarnath Murthy_, Dec 13 2003. %N: Left side of irregular triangle of natural numbers in which every row product is a multiple of the previous. Offset 1. Example rows (1),(2),(3,4),(5,6,7,8),(9..14),(15..26). Mathematica by Michael De Vlieger, Dec 15 2016, searches the next row length starting from the previous length.)

**The frozen Lean statement**

```lean
def search (P s : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, k, _ => k
  | fuel + 1, k, Q => if P ∣ Q then k else search P s fuel (k + 1) ((s + k) * Q)
def next (r : ℕ × ℕ) : ℕ × ℕ :=
  (r.1 + r.2,
    search (r.1.ascFactorial r.2) (r.1 + r.2) (r.1 + r.2) r.2 ((r.1 + r.2).ascFactorial r.2))
def row (n : ℕ) : ℕ × ℕ := next^[n - 1] (1, 1)
def a (n : ℕ) : ℕ := (row n).1
def len (n : ℕ) : ℕ := (row n).2
def last (n : ℕ) : ℕ := a n + len n - 1
def bertrand (n : ℕ) : ℕ := (fun b => Nat.findGreatest Nat.Prime (2 * b - 1))^[n - 1] 2
(len_succ_isLeast: len (n+1) is the least k ≥ len n with (a n).ascFactorial (len n) ∣ (a (n+1)).ascFactorial k)

def statement : Prop :=
  ∀ n : ℕ, 4 < n → ∃ p : ℕ,
    IsGreatest {q : ℕ | q.Prime ∧ a (n - 1) ≤ q ∧ q ≤ last (n - 1)} p ∧
      last n = 2 * p ∧ p = bertrand (n - 1)
```

**What the Lean statement says**

Split 1, 2, 3, … into consecutive blocks. Block 1 is (1). Each later block starts right after the previous one, and its length is the least k, with k at least the previous block's length, such that the product of the previous block divides the product of the new block. Then for every n > 4: block n-1 contains a largest prime p, the last element of block n equals 2p, and p equals the (n-1)-th Bertrand prime B_{n-1}, where B_1 = 2 and B_{k+1} is the largest prime < 2B_k.

**What the kernel checks against the OEIS data**

a_data checks a(1..18) (first terms of the rows), len_data checks 17 row lengths against A090906, and bertrand_data checks 13 terms of A006992. len_succ_isLeast proves that the computable search really returns the least admissible length. Independently, I recomputed rows 1..28 with a prime-valuation method. They reproduce the listed a(1..28), and they are identical whether the length search starts at k = 1 or at k = len(n). I also checked that all 34 listed terms satisfy a(n+1) - 1 = 2·B_{n-1} for n = 5..33. In other words, the listed data are consistent with what the proved statement forces.

**Points for the reviewer**

- *Minor.* The Lean triangle requires each row to be at least as long as the previous row (k ≥ len n). This bound comes from De Vlieger's 2016 Mathematica program. Murthy's name of the sequence ("every row product is a multiple of the previous") does not state it; the unbounded variant is A381901. The bound turns out not to matter. Rows 1..28 are identical with or without it. Moreover, once the proved statement holds, the largest prime B_n of row n forces the next row to have length at least 2B_n - 2B_{n-1}, and that is ≥ len(n) = 2B_{n-1} - 2B_{n-2}. I checked this inequality for all Bertrand primes up to index 38, and it follows from Nagura beyond that. So the bound is never binding, and the two triangles coincide for every n.
- *Note.* "And these are the Bertrand primes" is encoded as p = A006992(n-1). Given the first two conjuncts for all n > 4, this third conjunct follows by induction from B_4 = 7. Since last(n-1) = 2B_{n-2} is not prime, the largest prime of block n-1 is the largest prime ≤ 2B_{n-2} - 1, which is B_{n-1}. The conjunct therefore neither strengthens nor weakens the statement. A looser reading ("each p is some Bertrand prime") would also be implied. Indexing works out: n=5 gives p=7=B_4 and last(5)=14.
- *Note.* IsGreatest asserts that block n-1 contains a prime, which the phrase "the largest prime in the (n-1)th group" takes for granted. n > 4 matches the conjecture: n = 4 fails, since last(4) = 8 ≠ 2·3. last uses truncated subtraction, but len ≥ 1 always, so it never truncates.

## A091817: Quet's integrality conjecture for A091817 holds

Verdict of the pre-review: **faithful**. Result: [oeis-a091817](../../results/oeis-a091817/README.md) (known-result-first-formalization). Frozen statement: [`lean/Math0/Statements/OEIS/A091817.lean`](../../lean/Math0/Statements/OEIS/A091817.lean).

**The conjecture as stated in OEIS**

> %C A091817 _Leroy Quet_ conjectures that the terms are always integral. This is true for p < 3*10^4.  [Entry: Mohammed Bouayoun and _Ralf Stephan_, Mar 07 2004; %N (2*numerator(H(p-3)) -3*denominator(H(p-3)))/p with H(m) = 1 + 1/2 + 1/3 + ...+ 1/m; %O 1,3; PARI: forprime(p=3,100,...); %F a(n) = (2*A001008(p-3) - 3*A002805(p-3))/p, p prime >= 5.]

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ z : ℤ, a n = (z : ℚ)

where
def H (m : ℕ) : ℚ := ((List.range m).map (fun k => (1 : ℚ) / ((k : ℚ) + 1))).sum
def term (p : ℕ) : ℚ := (2 * (H (p - 3)).num - 3 * ((H (p - 3)).den : ℤ) : ℚ) / (p : ℚ)
def a (n : ℕ) : ℚ := term (primeAt n)
-- primeAt 0 = 2, primeAt (i+1) = nextPrime (primeAt i) (bounded Bertrand search); proved primeAt i = Nat.nth Nat.Prime i
```

**What the Lean statement says**

For every odd prime p (p = 3, 5, 7, 11, ...), write the harmonic number H(p-3) = 1 + 1/2 + ... + 1/(p-3) in lowest terms as N/D with D > 0 (H(0) = 0/1). Then the rational number (2N - 3D)/p is an integer; that is, p divides 2N - 3D.

**What the kernel checks against the OEIS data**

a_data checks all 18 listed terms, a 1 through a 18 (p = 3, ..., 67), including the sign of a(1) = -1, by decide +kernel. A separate example checks primeAt 1..4 = 3, 5, 7, 11. primeAt_eq_nth proves primeAt is Nat.nth Nat.Prime for every index, so the indexing is pinned beyond the data. With 18 exact, rapidly growing values checked, numerator, denominator and offset are fully pinned.

**Points for the reviewer**

- *Note.* The %F line says 'p prime >= 5', but the data and the PARI program start at p = 3 (a(1) = -1). The Lean statement covers every n >= 1, i.e. all primes p >= 3. This only adds the trivially true p = 3 case, so it is not weaker than the conjecture. n = 0 (p = 2, where the value -3/2 is not an integer and p-3 truncates to 0) is correctly excluded.
- *Note.* Natural-number subtraction p - 3 never truncates for p >= 3. Rat.num and Rat.den are in lowest terms with a positive denominator, which matches PARI's numerator and denominator.

## A092054: Convergents of [1; 1/2, 1/3, ..., 1/n]: numerator + denominator = 2^(v2(n!) + v2((n+1)!)) (A092054)

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a092054](../../results/oeis-a092054/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A092054.lean`](../../lean/Math0/Statements/OEIS/A092054.lean).

**The conjecture as stated in OEIS**

> %F A092054 It appears that a(n) = Sum_{k=1..n} A001511(floor((k+1)/2)). Equivalently, a(n) = 2n + 1 - A000120(n) - A000120(n+1) = A011371(n) + A011371(n+1). - _Franklin T. Adams-Watters_, Feb 02 2006
> (%N by _Paul D. Hanna_, Feb 19 2004: Base-2 logarithm of the sum of numerator and denominator of the convergents of the continued fraction expansion [1; 1/2, 1/3, 1/4, ..., 1/n, ...]. Offset 1. %C/%F also assert A001902(n) + A092053(n) = 2^a(n).)

**The frozen Lean statement**

```lean
def cfEval : List ℚ → ℚ
  | [] => 0
  | [x] => x
  | x :: y :: ys => x + 1 / cfEval (y :: ys)
def conv (n : ℕ) : ℚ := cfEval ((List.range n).map fun k => 1 / ((k : ℚ) + 1))
def num (n : ℕ) : ℕ := (conv n).num.natAbs
def den (n : ℕ) : ℕ := (conv n).den
def a (n : ℕ) : ℕ := Nat.log 2 (num n + den n)
def ruler (m : ℕ) : ℕ := padicValNat 2 (2 * m)
def binWeight (m : ℕ) : ℕ := (Nat.digits 2 m).sum
def A011371 (m : ℕ) : ℕ := m - binWeight m

def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    2 ^ a n = num n + den n ∧
    a n = ∑ k ∈ Finset.Icc 1 n, ruler ((k + 1) / 2) ∧
    (a n : ℤ) = 2 * (n : ℤ) + 1 - (binWeight n : ℤ) - (binWeight (n + 1) : ℤ) ∧
    a n = A011371 n + A011371 (n + 1)
```

**What the Lean statement says**

For every n ≥ 1, write the rational number 1 + 1/(1/2 + 1/(1/3 + … + 1/(1/n))) in lowest terms as p/q. Then p + q is a power of 2, namely 2^e with e = floor(log2(p+q)). Moreover e = sum_{k=1..n} (1 + v2(floor((k+1)/2))) = 2n + 1 - s2(n) - s2(n+1) = (n - s2(n)) + (n+1 - s2(n+1)), where s2 is the binary digit sum.

**What the kernel checks against the OEIS data**

conv_four checks the entry's example 45/19. num_data checks num(1..24) = A001902(1..24), the reduced numerators (A001902 has offset 0, and the indices line up). den_data checks den(1..25) = A092053(1..25). a_data checks all 67 listed terms a(1..67). ruler_data, binWeight_data and A011371_data check the helper sequences against their OEIS terms. Together these pin the lowest-terms convergent reading, the floor-log definition and the helpers. Independently, I checked in exact arithmetic for n = 1..399 that p+q is a power of 2 and that all four expressions agree.

**Points for the reviewer**

- *Note.* The first conjunct, 2^a(n) = num + den, is not part of Adams-Watters's formula. It is Hanna's power-of-2 claim, stated in the entry's %C/%F. The Lean a is the floor of log2, which is also what the entry's PARI program computes. Under the entry's real-logarithm definition, "a(n) = f(n)" already implies num + den = 2^f(n), so adding the conjunct is the faithful real-log reading. Under the floor-log reading it is a strengthening. Since the result proves the statement, the proof covers both readings.
- *Note.* The two "Equivalently" forms are included as extra conjuncts. They are identities in n and do not depend on the convergents. Writing m = ceil(k/2), the sum of A001511(m) up to M equals 2M - s2(M), and A011371(m) = m - s2(m). I verified the identity algebraically for even and odd n, so these conjuncts add no strength. The middle form is computed in ℤ, which avoids truncated subtraction. A011371 uses ℕ subtraction but never truncates, because binWeight m ≤ m.

## A093726: Imaginary parts of the convergents of [1+i; 1+i, 1+i, ...] are A317974(n+1)/A138573(n)

Verdict of the pre-review: **faithful-with-notes**. Result: [oeis-a093726](../../results/oeis-a093726/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A093726.lean`](../../lean/Math0/Statements/OEIS/A093726.lean).

**The conjecture as stated in OEIS**

> %F: "Conjecture: a(n)/A093727(n) = A317974(n+1)/A138573(n). - _Zhuorui He_, Jun 16 2026". Context: %N "Given the infinite continued fraction (1+i)+1/((1+i)+1/((1+i)+...)), where i is the square root of (-1), this is the numerator of the imaginary part of the convergents." %t "Table[ Im[ Numerator[ FromContinuedFraction[ Table[1 + I, {n}]]]], {n, 30}]". %e (He): "(1+i)+1/((1+i)+1/((1+i)+1/(1+i))) = (6+3*i)/4, so A093725(4)=6, a(4)=3 and A093727(4)=4." Offset 1; %E "Definition corrected by and a(29)-a(30) from _Zhuorui He_, Jun 16 2026". Rev #13 (Jun 20 2026); this is still the current version on GitHub oeisdata main.

**The frozen Lean statement**

```lean
def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (a n : ℚ) / (A093727 n : ℚ) = (A317974 (n + 1) : ℚ) / (A138573 n : ℚ)

where (abridged):
def gadd (z w : ℚ × ℚ) : ℚ × ℚ := (z.1 + w.1, z.2 + w.2)
def ginv (z : ℚ × ℚ) : ℚ × ℚ := (z.1 / (z.1*z.1 + z.2*z.2), -z.2 / (z.1*z.1 + z.2*z.2))
def cfValue : List (ℚ × ℚ) → ℚ × ℚ | [] => (0,0) | [x] => x | x :: xs => gadd x (ginv (cfValue xs))
def conv (n : ℕ) : ℚ × ℚ := cfValue (List.replicate n (1, 1))
def gden (z : ℚ × ℚ) : ℕ := Nat.lcm z.1.den z.2.den
def gnumIm (z : ℚ × ℚ) : ℤ := z.2.num * ((gden z / z.2.den : ℕ) : ℤ)
def a (n : ℕ) : ℤ := gnumIm (conv n)
def A093727 (n : ℕ) : ℕ := gden (conv n)
def A317974 : ℕ → ℤ | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1 | n+4 => 2*(A317974 (n+3) + A317974 (n+2) + A317974 (n+1)) - A317974 n
def A138573 : ℕ → ℤ | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | n+4 => 2*A138573 (n+3) + 2*A138573 (n+2) + 2*A138573 (n+1) - A138573 n
```

**What the Lean statement says**

Let c_n be the finite continued fraction (1+i) + 1/((1+i) + 1/(... + 1/(1+i))) with n partial quotients 1+i (a Gaussian rational). Write c_n = (X + Y i)/d, where d = lcm(den Re c_n, den Im c_n) is the least positive integer with d c_n a Gaussian integer. Then a(n) = Y = d·Im(c_n) and A093727(n) = d, so a(n)/A093727(n) is exactly Im(c_n). Let u = 0,0,1,1,... and v = 0,1,2,5,... (offset 0), both continued by w(m) = 2(w(m-1)+w(m-2)+w(m-3)) - w(m-4). The claim is that for every n >= 1, Im(c_n) = u(n+1)/v(n) as rational numbers.

**What the kernel checks against the OEIS data**

a_data kernel-checks all 30 listed terms a(1..30). A093727_data checks all 28 listed terms of A093727. A317974_data and A138573_data check 20 listed terms each (n = 0..19). These pin A317974 and A138573, which are defined by their own OEIS recurrences anyway. For a and A093727 they confirm the Mathematica Numerator/Denominator reading. They do NOT tell it apart from the literal-name reading 'reduced numerator of Im(c_n)': the two agree on n <= 41 and first differ at n = 42, so the choice between them rests on the program and the examples, not on the data.

**Points for the reviewer**

- *Minor.* The truth value depends on which reading of a(n) is used. The name says 'numerator of the imaginary part of the convergents'. Lean uses Im(Numerator(c_n)) = lcm(den Re, den Im)·Im(c_n), as in the program Im[Numerator[...]]. I checked numerically that the two readings first differ at n = 42 (then at 84 and 126). Under the literal-name reading the conjectured identity is false at n = 42: reduced num Im(c_42) = 18854485653829, while d·Im(c_42) = 245108313499777, with d = A093727(42) = 329919304636610. The Lean reading is the defensible one. It is the reading of the program, of He's own examples written as (A093725(n)+a(n)*i)/A093727(n), and of the only sense in which a(n)/A093727(n) is a natural quantity (Im c_n). A reviewer should still know that the alternative reading would give a counterexample rather than a proof.
- *Note.* Under these definitions a(n)/A093727(n) = Im(c_n) exactly (gnumIm/gden = z.2.num/z.2.den). So the statement is 'Im(c_n) = A317974(n+1)/A138573(n) for all n >= 1'. It is an equality of ratios only. It does not claim a(n) = A317974(n+1) or A093727(n) = A138573(n); those fail, e.g. A093727(5) = 15 but A138573(5) = 45.
- *Note.* A093727's OEIS name still carries the old garbled continued fraction '(1+i)+((1+i)/(1+i)+...)'. Lean follows its program (Denominator of FromContinuedFraction[Table[1+I,{n}]]) and all 28 listed terms, which agree with the corrected A093726 name.
- *Note.* There are no junk-value issues. The range is n >= 1, matching offset 1 of A093726 and A093727. A093727(n) >= 1, and A138573(n) >= 1 for n >= 1, so Lean's x/0 = 0 never fires. ginv is only applied to nonzero convergents (Re c_n >= 1). Offsets of A317974 and A138573 (both 0) match OEIS.

## A097154: The only fixed points of reverse(x) - maxdigit(x) are 0 and 89

Verdict of the pre-review: **faithful**. Result: [oeis-a097154](../../results/oeis-a097154/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A097154.lean`](../../lean/Math0/Statements/OEIS/A097154.lean).

**The conjecture as stated in OEIS**

> %C: "a(89)=-1 because 89 is the first number that will not reach zero: 98-9=89. It is conjectured that 0 and 89 are the only fixed points of f. See A097155 for numbers that reach 89." (entry by _Jason Earls_, Aug 01 2004; the comment is unsigned). %N: "Number of iterations of f(x) = reverse(x) - maxdigit(x) needed to reach zero, or -1 if zero is never reached, where maxdig(n) is the largest digit of n." The same sentence is in A097155 and A097157. Rev #4 (Dec 15 2017); unchanged on GitHub main.

**The frozen Lean statement**

```lean
def rev (x : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 x).reverse
def maxDigit (x : ℕ) : ℕ := (Nat.digits 10 x).foldr max 0
def f (x : ℕ) : ℕ := rev x - maxDigit x

def statement : Prop :=
  ∀ x : ℕ, f x = x ↔ x = 0 ∨ x = 89
```

**What the Lean statement says**

For a nonnegative integer x, let rev(x) be the number whose decimal digits are those of x in reverse order (trailing zeros of x become dropped leading zeros, rev 0 = 0). Let maxdig(x) be the largest decimal digit of x (maxdig 0 = 0), and f(x) = rev(x) - maxdig(x). Then for every nonnegative integer x, f(x) = x if and only if x = 0 or x = 89.

**What the kernel checks against the OEIS data**

f_examples kernel-checks the entry's example orbit 12 -> 19 -> 82 -> 20 -> 0, f(0) = 0, rev 89 = 98, maxDigit 89 = 9 and f(89) = 89. a_data kernel-checks all 127 listed terms a(1..127) of A097154, including a(89) = -1. a_spec proves that the bounded search used for computability equals the unbounded 'least k with f^[k] n = 0, else -1'. This pins rev (including trailing-zero handling, e.g. 20 -> 0, 100 -> 0), maxDigit and f well.

**Points for the reviewer**

- *Note.* Natural-number subtraction in f never truncates: maxDigit_le_rev is proved and f_eq_int restates f with integer subtraction. So f is the entry's map on the nonnegative integers, and f(x) is never negative there. Reversal matches the Mathematica in A097155 (FromDigits[Reverse[IntegerDigits[n]]]).
- *Note.* 'Fixed points' is read literally as f(x) = x, with both directions of the iff and 0 included, as the text says. A broader possible intent, that every orbit ends at 0 or 89 (no other cycles), is not formalized and is not settled by the result. I checked numerically that f has no cycles other than {0} and {89} among x < 10^7, so nothing in the data separates the two readings, but the wording 'only fixed points' supports the literal one.

## A106505: A106505: common sides of A/2A primitive triangles are periodic mod 8, so a(n+5) = a(n) + 8

Verdict of the pre-review: **faithful**. Result: [oeis-a106505](../../results/oeis-a106505/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A106505.lean`](../../lean/Math0/Statements/OEIS/A106505.lean).

**The conjecture as stated in OEIS**

> %F: "Conjecture: for n>2, a(n+5) = a(n) + 8. - _Ralf Stephan_, Nov 16 2010." %N (Lekraj Beedassy, May 04 2005): "Ordered and uniqued length of side common to the two angles, one being the double of the other, of a primitive integer-sided triangle." %F: "Values s^2 - r^2, where r<s<2r and (r, s)=1." Offset 1. Rev #21 (Apr 23 2021); unchanged on GitHub main.

**The frozen Lean statement**

```lean
def statement : Prop := ∀ n : ℕ, 2 < n → a (n + 5) = a n + 8

where:
noncomputable def angleOpp (p q r : ℝ) : ℝ := Real.arccos ((q ^ 2 + r ^ 2 - p ^ 2) / (2 * q * r))
def IsDoubleAngleTriangle (x y c : ℕ) : Prop :=
  x < y + c ∧ y < x + c ∧ c < x + y ∧
    angleOpp (y : ℝ) (x : ℝ) (c : ℝ) = 2 * angleOpp (x : ℝ) (y : ℝ) (c : ℝ)
def IsSide (c : ℕ) : Prop := ∃ x y : ℕ, IsDoubleAngleTriangle x y c ∧ Nat.gcd (Nat.gcd x y) c = 1
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsSide (n - 1)
```

**What the Lean statement says**

Call a positive integer c a side if there are integers x, y such that x, y, c are the sides of a non-degenerate triangle with gcd(x, y, c) = 1, in which the angle opposite y (law of cosines, in [0, π]) is twice the angle opposite x. Here c is the side joining the vertices of those two angles. Let a(1) < a(2) < ... list the sides in increasing order without repetition. The claim is that a(n+5) = a(n) + 8 for every n >= 3.

**What the kernel checks against the OEIS data**

a_data kernel-checks all 67 listed terms (5, 7, ..., 111, 112) by a kernel-decided filter of IsSide over [0, 113), via the proved equivalence of IsSide with y^2 = x(x+c) (isDoubleAngleTriangle_iff, isSide_iff). This pins IsSide exactly on [0, 113). example_33 checks the entry's two triangles with common side 33.

**Points for the reviewer**

- *Note.* Lean formalizes the geometric name, not the %F parametrization s^2 - r^2 (r < s < 2r, gcd(r,s) = 1). The two give the same set. Primitivity plus y^2 = x(x+c) forces gcd(x, x+c) = 1, so x = r^2 and x+c = s^2. The triangle inequality c < x + y is equivalent to s < 2r. I also checked numerically that both equal {odd c >= 5} ∪ {8m : m >= 2} for c < 600.
- *Note.* Range and offset are faithful. Offset 1 is handled by Nat.nth (n-1), and the hypothesis n > 2 matches 'for n>2'. The identity genuinely fails at n = 1, 2 (a(6) = 15 ≠ 13, a(7) = 16 ≠ 15). Nat.nth's junk value 0 for a finite set would make the statement false, not vacuous.

## A113676: The Golomb-row triangle A113676 and Levine's sequence A014644

Verdict of the pre-review: **faithful**. Result: [oeis-a113676](../../results/oeis-a113676/README.md) (new-result). Frozen statement: [`lean/Math0/Statements/OEIS/A113676.lean`](../../lean/Math0/Statements/OEIS/A113676.lean).

**The conjecture as stated in OEIS**

> %C: "Conjecture: a(n) for n>1 gives first differences of Lionel Levine's sequence A014644(n) for n>=3." %C: "Conjecture: Final elements of the rows form A014644 except for duplicate 2." (entry by _Floor van Lamoen_ and _Paul D. Hanna_, Nov 06 2005). %N: "Number of elements of rows of Golomb's sequence A001462, with one less 2, interpreted as triangle: Start with first row 1. The row sum of row n-1 gives the number of elements taken from A001642 (one less 2) of row n." %e: rows 1; 2; 3,3; 4,4,4,5,5,5. Offset 1. Rev #9 (Mar 05 2025); unchanged on GitHub main.

**The frozen Lean statement**

```lean
def statement : Prop :=
  (∀ n : ℕ, 2 ≤ n → (a n : ℤ) = (A014644 (n + 2) : ℤ) - (A014644 (n + 1) : ℤ)) ∧
  ((row 1).getLast? = some (A014644 1) ∧
    ∀ n : ℕ, 2 ≤ n → (row n).getLast? = some (A014644 (n + 1)))

where (abridged):
def golombAux : ℕ → List ℕ | 0 => [1, 2, 2] | m + 1 => golombAux m ++ List.replicate ((golombAux m).getD (m + 2) 0) (m + 3)
def golomb : ℕ → ℕ | 0 => 0 | n + 1 => (golombAux n).getD n 0
def H (j : ℕ) : ℕ := if j ≤ 1 then golomb j else golomb (j + 1)
def rowEnd : ℕ → ℕ | 0 => 0 | 1 => 1 | n + 2 => rowEnd (n + 1) + ((List.range' (rowEnd n + 1) (rowEnd (n + 1) - rowEnd n)).map H).sum
def row (n : ℕ) : List ℕ := (List.range' (rowEnd (n - 1) + 1) (rowEnd n - rowEnd (n - 1))).map H
def a (n : ℕ) : ℕ := (row n).length
def levineAux : List ℕ → ℕ → List ℕ | [], _ => [] | c :: l, i => List.replicate c i ++ levineAux l (i + 1)
def levineRow : ℕ → List ℕ | 0 => [] | 1 => [1, 1] | k + 2 => levineAux (levineRow (k + 1)) 1
def A014644 (k : ℕ) : ℕ := (levineRow k).getLastD 0
```

**What the Lean statement says**

Let G be Golomb's sequence (G(1) = 1, nondecreasing, n occurs G(n) times), and let H = 1, 2, 3, 3, 4, 4, 4, ... be G with one 2 removed. Cut H into consecutive rows: row 1 has 1 term, and row n+1 has as many terms as the sum of row n. Let a(n) be the length of row n. Levine's array starts with row [1,1], and each next row lists i repeated c_i times for i = 1, 2, ..., where c_i is the i-th term of the current row. L(k) is the last term of row k. Claim (1): for every n >= 2, a(n) = L(n+2) - L(n+1), as integers. Claim (2): the last term of row 1 is L(1), and for every n >= 2 the last term of row n exists and equals L(n+1).

**What the kernel checks against the OEIS data**

golomb_data checks all 84 listed terms of A001462. rows_example checks the four rows shown in the entry. a_data checks all 9 listed terms of A113676 (a(9) = 4362192095 via a proved weighted-sum shortcut). rowLast_data checks that the last elements of rows 1..7 are 1, 2, 3, 5, 11, 38, 272. A014644_data checks the first 11 terms of A014644. Together these pin the triangle, Golomb and Levine definitions and the index shift in claim (1). Only a(n) = A014644(n+2) - A014644(n+1) fits a(2) = 1 = 3 - 2; the shift A014644(n+1) - A014644(n) would give 0.

**Points for the reviewer**

- *Note.* The name's 'A001642' is read as the typo it is for A001462, and the example rows confirm this. Deleting either of the two equal 2s gives the same H.
- *Note.* Levine's array is built left to right: i repeated c_i times in increasing i, as in A014643/A014644 and the A014644 Mathematica program. The right-to-left variant (A011784: 1, 2, 2, 3, 4, 7, 14, ...) is not used. The A014644 data (1, 2, 2, 3, 5, 11, 38, 272, ...) fixes this choice.
- *Note.* 'Except for duplicate 2' is formalized as row 1 -> A014644(1) and row n -> A014644(n+1) for n >= 2. getLast? = some also forces every row n >= 1 to be nonempty, which makes the claim slightly stronger than needed (fine for a proof). Claim (1) is in ℤ, so there is no truncated subtraction, and it covers n >= 2 only, as in 'for n>1'; a(1) = 1 is correctly excluded.
