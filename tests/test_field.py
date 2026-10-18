import unittest
from gfq import GF


class TestField(unittest.TestCase):
    def test_supported_and_unsupported(self):
        for q in (2, 3, 4, 5, 7, 8, 9):
            self.assertEqual(GF(q).q, q)
        for q in (1, 6, 10, 11, 16):
            with self.assertRaises(ValueError):
                GF(q)

    def test_field_axioms_exhaustive(self):
        # VERIFIED by finite enumeration for every supported field.
        for q in (2, 3, 4, 5, 7, 8, 9):
            F = GF(q)
            for a in range(q):
                self.assertEqual(F.add(a, 0), a)
                self.assertEqual(F.mul(a, 1), a)
                self.assertEqual(F.add(a, F.neg(a)), 0)
                if a:
                    self.assertEqual(F.mul(a, F.inv(a)), 1)
                for b in range(q):
                    self.assertEqual(F.add(a, b), F.add(b, a))
                    self.assertEqual(F.mul(a, b), F.mul(b, a))
                    for c in range(q):
                        self.assertEqual(F.mul(a, F.add(b, c)),
                                         F.add(F.mul(a, b), F.mul(a, c)))
            # multiplicative group cyclic of order q-1
            g = F.primitive_element()
            self.assertEqual({F.pow(g, e) for e in range(q - 1)}, set(range(1, q)))

    def test_prime_fields_are_residues(self):
        F = GF(5)
        self.assertEqual(F.mul(3, 4), 2)
        self.assertEqual(F.inv(2), 3)
        self.assertEqual(GF(3).add(2, 2), 1)

    def test_gf4_table_spot_check(self):
        # GF(4)=GF(2)[x]/(x^2+x+1): element 2 is x, x*x = x+1 = 3.
        F = GF(4)
        self.assertEqual(F.mul(2, 2), 3)
        self.assertEqual(F.mul(2, 3), 1)   # x(x+1)=1 mod (x^2+x+1)
        with self.assertRaises(ZeroDivisionError):
            F.inv(0)
        with self.assertRaises(ValueError):
            F.add(4, 1)


if __name__ == "__main__":
    unittest.main()
