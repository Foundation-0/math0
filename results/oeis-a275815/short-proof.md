# A short proof of the queen-mobility bound for n ≥ 8

**Status: informal, not formalized in Lean.** The Lean proofs in math0 establish the same bound
by a different route: computer-found linear-programming dual (flow) certificates in
[`A278212.lean`](../../lean/Math0/Frontier/OEIS/A278212.lean) (n ≥ 7) and
[`A275815.lean`](../../lean/Math0/Frontier/OEIS/A275815.lean) (n = 6). The argument below was found
on 29 Oct 2026 by an assessor agent that was asked to judge how hard that result was. Two further
agents then checked it independently:

- one re-derived every step by hand and wrote out the corner cases, which the first version left
  terse;
- the other implemented the move count and the charging scheme and searched for counterexamples.
  This covered all 2^25 queen patterns on a 5 × 5 corner block against several backgrounds,
  exhaustive enumeration of the squares each bound depends on, and random and annealed boards for
  n = 8 to 14.

Neither found a gap or a counterexample. The argument shows that the A275815 bound needs no
computer certificate for n ≥ 8. For that reason the results for
[A275815](README.md) and [A278212](../oeis-a278212/README.md) are both rated *routine*.

## Setting

The board is {1, …, n} × {1, …, n}. Q is a set of squares, each holding a queen; all the queens
are the same colour. A queen moves along any of its 8 rays, to an empty square, passing only
through empty squares. M(Q) is the total number of moves available to all the queens.

**Claim.** For n ≥ 8, M(Q) ≤ 8(n − 2)² for every Q. Equality holds when every border square holds
a queen.

## 1. Counting along lines

The *lines* are the n rows, the n columns, and the 2n − 1 diagonals in each direction. This
includes the length-1 diagonals, each of which consists of a single corner square. Every square
lies on exactly 4 lines.

Fix a line with E empty squares. Let g₁ and g₂ be its *end gaps*: the number of empty squares
before the first queen, counted from each end. A line with no queen has g₁ = g₂ = its length.
Every empty square between two queens on the line can be reached by both of them, and every empty
square in an end gap by one queen only. So the moves along this line number 2E − g₁ − g₂.

Summing over all lines, and using that each square lies on 4 lines,

  M(Q) = 8(n² − |Q|) − Σ (end gaps over all line ends).

Every line end is a border square, and the gap at an end occupied by a queen is 0. There are
n² − (n − 2)² = 4(n − 1) border squares. For an empty border square b, let G(b) be the sum of the
gaps of the line ends at b, and let Q_int be the set of interior queens. Then the claim is
equivalent to

  Σ_{empty border b} (G(b) − 8) + 8·|Q_int| ≥ 0.   (∗)

A border square that is not a corner is an end of 3 lines: the line perpendicular to its edge and
its two diagonals. The line along its edge ends at the two corners. A corner is an end of 5
line ends: its row, its column, the long diagonal, and both ends of its length-1 diagonal.

## 2. Discharging

Each interior queen starts with 8 units, 2 for each of its 4 lines. Consider one line through the
queen q, and an end b of that line that is empty. If q is the first queen seen from b, and q is
the 2nd or 3rd square counted from b (so the gap at b is 1 or 2), then q sends its 2 units on that
line to b. If both ends of the line qualify, which needs the line to have length at most 5, q sends
1 unit to each end instead. So no queen sends more than 8 units.

Let val(b) be G(b) plus the units b receives. Then (∗) follows if every empty border square has
val(b) ≥ 8. The only exceptions are a deficit of exactly 1 at no more than one square in each
corner region, and each such deficit is covered by one unit that a distinct interior queen did not
send.

## 3. The value of a line end

The *value* of a line end at b is its gap plus the units b receives along that line.

- **A line of length at least 6 whose 2nd and 3rd squares from b are interior.**
  - Gap 1: a queen on the 2nd square sends 2. It cannot qualify for the far end, because the line
    is too long. The value is 3.
  - Gap 2: the value is 2 + 2 = 4.
  - Gap at least 3: the value is at least 3.

  So the value is always at least 3. This covers every line perpendicular to an edge at a
  non-corner border square. It also covers every diagonal of length at least 6 that starts at a
  border square.
- **A diagonal of length 5:** at least 3. Its 2nd, 3rd and 4th squares are interior. The queen
  splits its units only if it sits on the middle square, and then the gap is 2, so the value is
  2 + 1 = 3.
- **A diagonal of length 3 or 4:** at least 2.
- **The length-2 diagonal** through the two neighbours of a corner: 1 if the other square holds a
  queen (gap 1, and a border queen sends nothing), and 2 if it is empty.
- **The length-1 diagonal at an empty corner:** it contributes 2, a gap of 1 at each of its two ends.
- **The row and the column along the edges through a corner:** they contain no interior queens, so
  they contribute only their gaps.

## 4. Border squares at least two squares from every corner

Take b = (r, 1) with 3 ≤ r ≤ n − 2; the other edges are symmetric. Its perpendicular line gives at
least 3. Its two diagonals have lengths r and n + 1 − r, which add up to n + 1 ≥ 9. So one of them
has length at least 5 and gives at least 3, and the other has length at least 3 and gives at least
2. Hence val(b) ≥ 8.

This is where n ≥ 8 is used. For n = 7, the square (4, 1) has two diagonals of length 4 and can
have value 3 + 2 + 2 = 7.

## 5. Corner regions

Take the corner C = (1, 1) and its neighbours A = (2, 1) and B = (1, 2); the other corners are
symmetric. A lies on row 1 and B lies on column 1.

**C empty.** Then

  val(C) = (gap of row 1 at C) + (gap of column 1 at C) + d + 2,

where d ≥ 3 is the value of the long diagonal at C. If A is empty, the row gap is at least 2, and
if B is empty, the column gap is at least 2. So val(C) ≥ 7, with equality only when A and B both
hold queens and d = 3.

**A empty.** The line ends at A are:
- column 2, with value at least 3;
- the long diagonal through A, of length n − 1 ≥ 7, with value at least 3;
- the length-2 diagonal A–B, with value 1 or 2.

So val(A) ≥ 7, with equality only when B holds a queen and the first two values are exactly 3.
The same holds for B, with the roles of A and B swapped.

**At most one square per region falls short, and by exactly 1.**
- C empty, A and B queens: only C can fall short.
- C empty, B a queen, A empty: the row gap at C is at least 2, so val(C) ≥ 8. Only A can fall
  short. The case with A and B swapped is symmetric.
- C, A and B all empty: val(C) ≥ 2 + 2 + 3 + 2 = 9 and val(A), val(B) ≥ 3 + 3 + 2 = 8.
- C a queen: A falls short only if B is a queen, and B only if A is a queen. So they cannot both
  fall short.

**Covering the shortfall.**
- **C is short.** Then d = 3, so one of two things holds:
  - (2, 2) holds a queen. Row 2 runs from B to (n, 2). B holds a queen, and (n, 2) is n − 2 squares
    away, so this queen sends nothing along row 2. Its 2 row units are unsent.
  - (2, 2) and (3, 3) are empty and (4, 4) holds a queen. That queen is 3 squares from C and n − 4
    from (n, n), so it sends nothing along the main diagonal. Its 2 diagonal units are unsent.
- **A is short.** Column 2 has value 3, so one of two things holds:
  - (2, 2) holds a queen. Its row-2 units are unsent, as above.
  - (2, 2) and (2, 3) are empty and (2, 4) holds a queen. That queen is 3 squares from A and n − 4
    from (2, n), so its 2 column units are unsent.
- **B is short:** symmetric, using (2, 2) or (4, 2).

The covering queens near (1, 1) lie among (2, 2), (4, 4), (2, 4) and (4, 2), and the covering queens
near the other corners lie in the mirror-image positions. For n ≥ 8 these four sets are disjoint.
Each region needs at most one unit, so each covering queen gives at most one unit, and only from
units it did not send.

## 6. Conclusion

Every empty border square has val ≥ 8. The only exception is at most one square per corner region
with val = 7, and each of those is covered by one unsent unit of its own interior queen. So (∗)
holds, and M(Q) ≤ 8(n − 2)² for every n ≥ 8.

For n = 6 and n = 7 the charging scheme fails locally. The values a(6) = 128 and a(7) = 200 come
from the Lean proofs above. The checking agent also confirmed them, and a(8) = 288 and
a(9) = 392, with an exact integer program.
