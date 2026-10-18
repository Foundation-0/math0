"""Finite fields GF(q) for q in {2,3,4,5,7,8,9}.

Elements are encoded as integers 0..q-1.  For a prime field GF(p) the
encoding is the residue itself.  For an extension field GF(p^m) the integer
is the base-p digit string of the polynomial coefficients:
element = sum_i digit_i * x^i  <->  code = sum_i digit_i * p^i.
Multiplication is polynomial multiplication modulo a fixed irreducible
polynomial (see _IRREDUCIBLE).  Addition/multiplication tables are built
once at construction, which is cheap for q <= 9.

There is no field of order 6, so q=6 (and any non-prime-power, or a prime
power other than the supported ones) raises ValueError.
"""
from __future__ import annotations


# Irreducible polynomials, coefficients low -> high over GF(p).
_IRREDUCIBLE = {
    4: (2, [1, 1, 1]),       # x^2 + x + 1 over GF(2)
    8: (2, [1, 1, 0, 1]),    # x^3 + x + 1 over GF(2)
    9: (3, [1, 0, 1]),       # x^2 + 1 over GF(3) (no root mod 3)
}
_PRIMES = {2, 3, 5, 7}
SUPPORTED_Q = (2, 3, 4, 5, 7, 8, 9)


def _digits(code: int, p: int, m: int) -> list[int]:
    out = []
    for _ in range(m):
        out.append(code % p)
        code //= p
    return out


def _from_digits(digs: list[int], p: int) -> int:
    code = 0
    for d in reversed(digs):
        code = code * p + (d % p)
    return code


class GF:
    """The finite field with ``q`` elements; elements are ints 0..q-1."""

    def __init__(self, q: int):
        if q in _PRIMES:
            self.q, self.p, self.m = q, q, 1
            self.modulus = None
        elif q in _IRREDUCIBLE:
            self.q = q
            self.p, self.modulus = _IRREDUCIBLE[q]
            self.m = len(self.modulus) - 1
        else:
            raise ValueError(
                f"no supported field of order {q}; supported q: {SUPPORTED_Q} "
                "(q must be a prime power; there is no field GF(6))"
            )
        self.zero = 0
        self.one = 1
        self._add = [[self._add_raw(a, b) for b in range(q)] for a in range(q)]
        self._mul = [[self._mul_raw(a, b) for b in range(q)] for a in range(q)]
        self._neg = [self._find_neg(a) for a in range(q)]
        self._inv = [0] + [self._find_inv(a) for a in range(1, q)]

    # -- raw arithmetic (used only to build tables) ---------------------
    def _add_raw(self, a: int, b: int) -> int:
        if self.m == 1:
            return (a + b) % self.p
        da, db = _digits(a, self.p, self.m), _digits(b, self.p, self.m)
        return _from_digits([(x + y) % self.p for x, y in zip(da, db)], self.p)

    def _mul_raw(self, a: int, b: int) -> int:
        if self.m == 1:
            return (a * b) % self.p
        p, mod = self.p, self.modulus
        da, db = _digits(a, p, self.m), _digits(b, p, self.m)
        prod = [0] * (2 * self.m - 1)
        for i, x in enumerate(da):
            for j, y in enumerate(db):
                prod[i + j] = (prod[i + j] + x * y) % p
        # reduce modulo the (monic) irreducible polynomial
        for deg in range(len(prod) - 1, self.m - 1, -1):
            c = prod[deg] % p
            if c:
                shift = deg - self.m
                for j in range(len(mod)):
                    prod[shift + j] = (prod[shift + j] - c * mod[j]) % p
        return _from_digits(prod[: self.m], p)

    def _find_neg(self, a: int) -> int:
        for b in range(self.q):
            if self._add[a][b] == 0:
                return b
        raise AssertionError("no additive inverse")  # pragma: no cover

    def _find_inv(self, a: int) -> int:
        for b in range(self.q):
            if self._mul[a][b] == 1:
                return b
        raise AssertionError("no multiplicative inverse")  # pragma: no cover

    # -- public arithmetic ------------------------------------------------
    def _check(self, a: int) -> int:
        if not isinstance(a, int) or not 0 <= a < self.q:
            raise ValueError(f"{a!r} is not an element of GF({self.q}) (0..{self.q - 1})")
        return a

    def add(self, a: int, b: int) -> int:
        return self._add[self._check(a)][self._check(b)]

    def sub(self, a: int, b: int) -> int:
        return self._add[self._check(a)][self._neg[self._check(b)]]

    def neg(self, a: int) -> int:
        return self._neg[self._check(a)]

    def mul(self, a: int, b: int) -> int:
        return self._mul[self._check(a)][self._check(b)]

    def inv(self, a: int) -> int:
        self._check(a)
        if a == 0:
            raise ZeroDivisionError("0 has no inverse")
        return self._inv[a]

    def div(self, a: int, b: int) -> int:
        return self.mul(a, self.inv(b))

    def pow(self, a: int, e: int) -> int:
        self._check(a)
        if e < 0:
            return self.pow(self.inv(a), -e)
        r = 1
        for _ in range(e):
            r = self._mul[r][a]
        return r

    def elements(self) -> list[int]:
        return list(range(self.q))

    def nonzero(self) -> list[int]:
        return list(range(1, self.q))

    def primitive_element(self) -> int:
        """Smallest generator of the multiplicative group."""
        for a in range(1, self.q):
            seen, cur = set(), 1
            for _ in range(self.q - 1):
                seen.add(cur)
                cur = self._mul[cur][a]
            if len(seen) == self.q - 1:
                return a
        raise AssertionError("multiplicative group is cyclic")  # pragma: no cover

    def __repr__(self) -> str:  # pragma: no cover
        return f"GF({self.q})"
