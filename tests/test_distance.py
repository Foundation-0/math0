"""Validation against codes whose parameters are KNOWN theorems.

Every expected [n,k,d] below is classical (Hamming d=3, Reed-Solomon MDS
d=n-k+1, ternary Golay [11,6,5]/[12,6,6], repetition, single-parity).
Where size permits, brute force and Brouwer-Zimmermann must agree, so no
expected value rests on one code path alone.
"""
import unittest

from gfq import GF, min_distance, brute_force_min_distance, bz_min_distance
from gfq import codes
from gfq.matrix import parse_matrix, row_space_contains, weight


def check(tc, G, q, n, k, d, methods=("auto", "brute", "bz")):
    F = GF(q)
    tc.assertEqual(len(G[0]), n)
    for m in methods:
        res = min_distance(G, F, method=m)
        tc.assertTrue(res.complete, f"{m}: incomplete")
        tc.assertEqual((res.n, res.k, res.d), (n, k, d), m)
        tc.assertEqual(weight(res.codeword), d, m)
        tc.assertTrue(row_space_contains(G, F, res.codeword), m)
    return res


class TestKnownCodes(unittest.TestCase):
    def test_ternary_golay(self):
        check(self, codes.ternary_golay_generator(False), 3, 11, 6, 5)

    def test_ternary_golay_extended(self):
        check(self, codes.ternary_golay_generator(True), 3, 12, 6, 6)

    def test_hamming_gf3(self):
        check(self, codes.hamming_generator(GF(3), 2), 3, 4, 2, 3)

    def test_hamming_gf3_r3(self):
        # [13,10,3]: 3^10/2 normalised codewords, brute still feasible.
        check(self, codes.hamming_generator(GF(3), 3), 3, 13, 10, 3)

    def test_hamming_gf4(self):
        check(self, codes.hamming_generator(GF(4), 2), 4, 5, 3, 3)

    def test_hamming_gf4_r3_bz_only(self):
        # [21,18,3]: brute force (4^18) infeasible; BZ must close exactly.
        F = GF(4)
        res = bz_min_distance(codes.hamming_generator(F, 3), F)
        self.assertTrue(res.complete)
        self.assertEqual((res.n, res.k, res.d), (21, 18, 3))

    def test_hamming_gf8_gf9(self):
        # n=(q^2-1)/(q-1)=q+1: GF(8) -> [9,7,3], GF(9) -> [10,8,3]
        check(self, codes.hamming_generator(GF(8), 2), 8, 9, 7, 3,
              methods=("auto", "bz"))
        check(self, codes.hamming_generator(GF(9), 2), 9, 10, 8, 3,
              methods=("auto", "bz"))

    def test_reed_solomon(self):
        check(self, codes.reed_solomon_generator(GF(8), 7, 3), 8, 7, 3, 5)
        check(self, codes.reed_solomon_generator(GF(8), 7, 4), 8, 7, 4, 4,
              methods=("auto", "bz"))
        check(self, codes.reed_solomon_generator(GF(9), 9, 4), 9, 9, 4, 6,
              methods=("auto", "bz"))
        check(self, codes.reed_solomon_generator(GF(7), 7, 3), 7, 7, 3, 5)
        check(self, codes.reed_solomon_generator(GF(5), 5, 2), 5, 5, 2, 4)
        check(self, codes.reed_solomon_generator(GF(3), 3, 2), 3, 3, 2, 2)

    def test_trivial_codes(self):
        for q in (3, 4, 9):
            F = GF(q)
            check(self, codes.repetition_generator(F, 6), q, 6, 1, 6)
            check(self, codes.single_parity_generator(F, 5), q, 5, 4, 2)
            ident = [[1 if i == j else 0 for j in range(4)] for i in range(4)]
            check(self, ident, q, 4, 4, 1)

    def test_binary_sanity(self):
        # binary Hamming [7,4,3] and Golay-free sanity that GF(2) also works
        check(self, codes.hamming_generator(GF(2), 3), 2, 7, 4, 3)


class TestBehaviour(unittest.TestCase):
    def test_rank_deficient_generator(self):
        F = GF(3)
        G = [[1, 0, 1], [2, 0, 2], [0, 1, 1]]  # rows 1,2 proportional: k=2
        res = min_distance(G, F)
        self.assertEqual(res.k, 2)
        self.assertEqual(res.d, 2)

    def test_zero_code_rejected(self):
        with self.assertRaises(ValueError):
            min_distance([[0, 0, 0]], GF(3))

    def test_out_of_field_rejected(self):
        with self.assertRaises(ValueError):
            min_distance([[1, 3]], GF(3))

    def test_bz_incomplete_is_honest(self):
        # A starved budget must yield bounds, never a claimed exact d.
        F = GF(4)
        res = bz_min_distance(codes.hamming_generator(F, 3), F, max_enum=1)
        self.assertFalse(res.complete)
        self.assertIsNone(res.d)
        self.assertLessEqual(res.lower_bound, 3)
        self.assertGreaterEqual(res.upper_bound, 3)

    def test_brute_matches_bz_random_small(self):
        # Deterministic pseudo-random small codes (fixed LCG, no `random`
        # import needed): independent methods must agree exactly.
        seed = 12345
        def rnd(mod):
            nonlocal seed
            seed = (seed * 1103515245 + 12345) & 0x7FFFFFFF
            return seed % mod
        for q, k, n in ((3, 4, 9), (4, 3, 8), (5, 3, 7), (9, 3, 8), (8, 3, 8)):
            F = GF(q)
            for _ in range(3):
                G = [[rnd(q) for _ in range(n)] for _ in range(k)]
                try:
                    a = brute_force_min_distance(G, F)
                except ValueError:
                    continue
                b = bz_min_distance(G, F)
                self.assertTrue(b.complete)
                self.assertEqual(a.d, b.d)
                self.assertEqual(a.k, b.k)

    def test_parse_formats(self):
        F = GF(3)
        a = parse_matrix("1 0 2\n0 1 1\n", F)
        b = parse_matrix("[1,0,2]\n[0,1,1]\n", F)
        c = parse_matrix("102\n011\n", F)
        d_ = parse_matrix("# hdr\n3 2 3\n1 0 2\n0 1 1\n", F)
        self.assertEqual(a, b)
        self.assertEqual(a, c)
        self.assertEqual(a, d_)
        with self.assertRaises(ValueError):
            parse_matrix("1 0\n1 0 0\n", F)      # ragged
        with self.assertRaises(ValueError):
            parse_matrix("1 5\n0 1\n", F)        # 5 not in GF(3)


if __name__ == "__main__":
    unittest.main()
