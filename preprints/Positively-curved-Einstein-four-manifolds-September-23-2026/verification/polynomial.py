"""Small exact rational polynomial arithmetic for the accompanying checks.

Author: OpenAI. Standard library only; no symbolic or numerical dependencies.
"""
from fractions import Fraction
from functools import lru_cache
from math import comb, factorial


def rational(value):
    if isinstance(value, float):
        raise TypeError("Floating-point coefficients are not permitted")
    return Fraction(value)


def require(condition, message):
    """An assertion that remains active when Python is invoked with -O."""
    if not condition:
        raise ArithmeticError(message)


class Poly:
    __slots__ = ("variables", "terms")

    def __init__(self, variables, terms=None):
        self.variables = tuple(variables)
        self.terms = {}
        for exponent, value in (terms or {}).items():
            exponent = tuple(exponent)
            require(len(exponent) == len(self.variables), "Wrong monomial dimension")
            require(all(isinstance(i, int) and i >= 0 for i in exponent),
                    "Polynomial exponents must be nonnegative integers")
            value = rational(value)
            if value:
                self.terms[exponent] = value

    @classmethod
    def constant(cls, variables, value):
        return cls(variables, {(0,) * len(variables): rational(value)})

    def _coerce(self, other):
        if isinstance(other, Poly):
            require(other.variables == self.variables, "Polynomial ring mismatch")
            return other
        return Poly.constant(self.variables, other)

    def __add__(self, other):
        other = self._coerce(other)
        terms = self.terms.copy()
        for exponent, value in other.terms.items():
            terms[exponent] = terms.get(exponent, Fraction(0)) + value
        return Poly(self.variables, terms)

    __radd__ = __add__

    def __neg__(self):
        return Poly(self.variables, {e: -c for e, c in self.terms.items()})

    def __sub__(self, other):
        return self + -self._coerce(other)

    def __rsub__(self, other):
        return self._coerce(other) + -self

    def __mul__(self, other):
        other = self._coerce(other)
        terms = {}
        for e, c in self.terms.items():
            for f, d in other.terms.items():
                exponent = tuple(a + b for a, b in zip(e, f))
                terms[exponent] = terms.get(exponent, Fraction(0)) + c * d
        return Poly(self.variables, terms)

    __rmul__ = __mul__

    def __truediv__(self, value):
        if isinstance(value, Poly):
            require(value.degree() <= 0, "Use divide_exact for polynomial division")
            value = value.terms.get((0,) * len(self.variables), Fraction(0))
        value = rational(value)
        require(value != 0, "Division by zero")
        return self * (1 / value)

    def __pow__(self, exponent):
        require(isinstance(exponent, int) and exponent >= 0,
                "Only nonnegative integral powers are polynomial")
        result = Poly.constant(self.variables, 1)
        base = self
        while exponent:
            if exponent % 2:
                result = result * base
            exponent //= 2
            if exponent:
                base = base * base
        return result

    def __eq__(self, other):
        try:
            other = self._coerce(other)
        except (ArithmeticError, TypeError, ValueError):
            return False
        return self.terms == other.terms

    def degree(self, variable=None):
        if variable is None:
            return max((sum(e) for e in self.terms), default=-1)
        index = self.variables.index(variable)
        return max((e[index] for e in self.terms), default=-1)

    def derivative(self, variable, order=1):
        index = self.variables.index(variable)
        result = self
        for _ in range(order):
            terms = {}
            for exponent, coefficient in result.terms.items():
                if exponent[index]:
                    new_exponent = list(exponent)
                    new_exponent[index] -= 1
                    terms[tuple(new_exponent)] = coefficient * exponent[index]
            result = Poly(self.variables, terms)
        return result

    def substitute(self, values):
        require(len(values) == len(self.variables), "Wrong substitution length")
        target = next((p.variables for p in values if isinstance(p, Poly)), None)
        if target is None:
            return self.evaluate(values)
        values = [p if isinstance(p, Poly) else Poly.constant(target, p) for p in values]
        require(all(p.variables == target for p in values), "Substitution ring mismatch")
        powers = []
        for index, value in enumerate(values):
            row = [Poly.constant(target, 1)]
            for _ in range(max((e[index] for e in self.terms), default=0)):
                row.append(row[-1] * value)
            powers.append(row)
        result = Poly.constant(target, 0)
        for exponent, coefficient in self.terms.items():
            term = Poly.constant(target, coefficient)
            for index, power in enumerate(exponent):
                term = term * powers[index][power]
            result = result + term
        return result

    def evaluate(self, values):
        require(len(values) == len(self.variables), "Wrong evaluation length")
        values = list(map(rational, values))
        answer = Fraction(0)
        for exponent, coefficient in self.terms.items():
            term = coefficient
            for value, power in zip(values, exponent):
                term *= value ** power
            answer += term
        return answer

    def coefficient(self, variable, power):
        index = self.variables.index(variable)
        variables = self.variables[:index] + self.variables[index + 1:]
        terms = {e[:index] + e[index + 1:]: c for e, c in self.terms.items()
                 if e[index] == power}
        return Poly(variables, terms)

    def divide_exact(self, divisor):
        divisor = self._coerce(divisor)
        require(bool(divisor.terms), "Polynomial division by zero")
        leading = lambda terms: max(terms, key=lambda e: (sum(e), e))
        de = leading(divisor.terms)
        dc = divisor.terms[de]
        remainder = self
        quotient = Poly.constant(self.variables, 0)
        while remainder.terms:
            re = leading(remainder.terms)
            require(all(a >= b for a, b in zip(re, de)), "Nonzero polynomial remainder")
            exponent = tuple(a - b for a, b in zip(re, de))
            term = Poly(self.variables, {exponent: remainder.terms[re] / dc})
            quotient = quotient + term
            remainder = remainder - term * divisor
        require(quotient * divisor == self, "Exact polynomial division failed")
        return quotient

    def reduce_circle(self, cosine="sigma", sine="rho"):
        """Reduce modulo sine^2+cosine^2-1 without numerical roots."""
        si = self.variables.index(sine)
        ci = self.variables.index(cosine)
        terms = {}
        for exponent, coefficient in self.terms.items():
            pairs, residual = divmod(exponent[si], 2)
            for j in range(pairs + 1):
                new_exponent = list(exponent)
                new_exponent[si] = residual
                new_exponent[ci] += 2 * j
                new_exponent = tuple(new_exponent)
                value = coefficient * comb(pairs, j) * (-1) ** j
                terms[new_exponent] = terms.get(new_exponent, Fraction(0)) + value
        return Poly(self.variables, terms)

    def integral(self, left, right):
        require(len(self.variables) == 1, "Interval integration requires one variable")
        left, right = rational(left), rational(right)
        return sum((c * (right ** (e[0] + 1) - left ** (e[0] + 1)) / (e[0] + 1)
                    for e, c in self.terms.items()), Fraction(0))

    def data(self):
        return {"variables": list(self.variables), "degree": self.degree(),
                "terms": [{"powers": list(e), "coefficient": str(c)}
                          for e, c in sorted(self.terms.items())]}


def ring(*variables):
    variables = tuple(variables)
    answer = []
    for index in range(len(variables)):
        exponent = [0] * len(variables)
        exponent[index] = 1
        answer.append(Poly(variables, {tuple(exponent): Fraction(1)}))
    return tuple(answer)


@lru_cache(maxsize=None)
def _interval_basis(degree):
    (z,) = ring("z")
    return tuple(comb(degree, i) * z ** i * (1 - z) ** (degree - i)
                 for i in range(degree + 1))


def interval_coefficients(poly, left, right, degree=None):
    require(len(poly.variables) == 1, "Expected a one-variable polynomial")
    degree = poly.degree() if degree is None else degree
    require(0 <= poly.degree() <= degree, "Univariate degree truncation prohibited")
    (z,) = ring("z")
    affine = poly.substitute([rational(left) + (rational(right) - rational(left)) * z])
    coeffs = []
    for i in range(degree + 1):
        coeffs.append(sum((c * Fraction(comb(i, e[0]), comb(degree, e[0]))
                           for e, c in affine.terms.items() if e[0] <= i), Fraction(0)))
    reconstructed = sum((c * p for c, p in zip(coeffs, _interval_basis(degree))),
                        Poly.constant(("z",), 0))
    require(reconstructed == affine, "Univariate Bernstein reconstruction failed")
    return coeffs


@lru_cache(maxsize=None)
def _triangle_basis(degree):
    z, w = ring("z", "w")
    answer = {}
    for i in range(degree + 1):
        for j in range(degree + 1 - i):
            k = degree - i - j
            multinomial = factorial(degree) // (factorial(i) * factorial(j) * factorial(k))
            answer[i, j] = multinomial * z ** i * w ** j * (1 - z - w) ** k
    return answer


def triangle_coefficients(poly, vertices, degree):
    require(len(poly.variables) == 2, "Expected a two-variable polynomial")
    require(poly.degree() <= degree, "Triangle degree truncation prohibited")
    z, w = ring("z", "w")
    p1, p2, p3 = [tuple(map(rational, p)) for p in vertices]
    v = p3[0] + (p1[0] - p3[0]) * z + (p2[0] - p3[0]) * w
    b = p3[1] + (p1[1] - p3[1]) * z + (p2[1] - p3[1]) * w
    affine = poly.substitute([v, b])
    coeffs = {}
    for i in range(degree + 1):
        for j in range(degree + 1 - i):
            coeffs[i, j] = sum((c * Fraction(comb(i, d) * comb(j, e),
                                 comb(degree, d + e) * comb(d + e, d))
                                for (d, e), c in affine.terms.items()
                                if d <= i and e <= j), Fraction(0))
    reconstructed = sum((coeffs[index] * basis
                         for index, basis in _triangle_basis(degree).items()),
                        Poly.constant(("z", "w"), 0))
    require(reconstructed == affine, "Triangle Bernstein reconstruction failed")
    return coeffs
