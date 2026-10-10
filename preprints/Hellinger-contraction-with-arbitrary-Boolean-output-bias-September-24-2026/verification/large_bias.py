#!/usr/bin/env python3
"""Exact rational certificates for the large-bias argument.
Adapted from low-bias-tail.py in the original audit; additional assertions
certify the displayed component ceilings and logarithmic bracket.

Every comparison uses fractions.Fraction. Decimal output is diagnostic only.
Run with Python 3; no third-party dependencies.
"""

from decimal import Decimal, localcontext
from fractions import Fraction as F
import hashlib


def dec(value, precision=24):
    with localcontext() as ctx:
        ctx.prec = precision
        return str(Decimal(value.numerator) / Decimal(value.denominator))


def partial_exp(x, order):
    term = F(1)
    total = term
    for i in range(1, order + 1):
        term *= x / i
        total += term
    return total, term


def E(z):
    return 1 / partial_exp(F("2.04") * z, 40)[0]


def ceil_scaled(x, scale):
    return -((-x.numerator * scale) // x.denominator)


def main():
    p, Llo, Lhi = F(".13"), F("2.04"), F("2.041")
    exp_lo_partial, last = partial_exp(Llo, 15)
    exp_lo_upper = exp_lo_partial + (last * Llo / 16) / (1 - Llo / 17)
    exp_hi_lower, _ = partial_exp(Lhi, 15)
    assert exp_lo_upper < F(7691, 1000) < 1 / p < F(7698, 1000) < exp_hi_lower
    assert F(".361") ** 2 > p
    print("PASS: exp(2.04) < 100/13 < exp(2.041), via exact order-15 sums and geometric tail")
    print("PASS: S15(2.04)+tail < 7.691 < 100/13 < 7.698 < S15(2.041)")
    print("PASS: sqrt(.13) < .361")
    print("PASS: p-difference monotonicity threshold exp(-2) > .13 follows from log(1/.13)>2.04")

    coefficients = [F(1, 2)]
    for k in range(1, 10):
        coefficients.append(coefficients[-1] * (F(k) - F(1, 2)) / (k + 1))
    tail_mass = 1 - sum(coefficients)
    assert tail_mass > 0
    print(f"c_1 through c_10: {', '.join(str(c) for c in coefficients)}")
    print(f"tail coefficient mass: {tail_mass} = {dec(tail_mass)}")

    expected = [982, 969, 954, 940]
    component_ceilings = [
        [746521967, 60049597, 2525240],
        [748896408, 56019174, 1084482],
        [750555827, 51401364, 283275],
        [751524751, 46967364, 36923],
    ]
    for n, (us, vs) in enumerate([(".84", ".88"), (".88", ".92"), (".92", ".96"), (".96", "1")]):
        u, v = F(us), F(vs)
        low, high = 1 - v * v, 1 - u * u
        B = Lhi * F(".361") * (1 + u) / (1 + u * u) * (1 + E(low / (2 * (2 - low)))) / 2
        total = F(0)
        chosen = []
        print(f"\nInterval [{us}, {vs}]: l={low}, R={high}, B={dec(B)}")
        for k, c in enumerate(coefficients, 1):
            q = F(k) + F(1, 2)
            a = q / (1 + high * (q - 1))
            b1 = q / (1 + low * (q - 1))
            assert a >= F("1.3")
            assert Llo * a > 2
            choices = [("derivative", Lhi * (1 - 1 / q) * a * a * E(a))]
            if low:
                choices.append(("direct", E(a) / low))
            choices.append(("trapezoid", Lhi * (q - 1) * (a * E(a) + b1 * E(q)) / 2))
            name, bound = min(choices, key=lambda x: x[1])
            total += c * bound
            chosen.append(name)
            print(f"  k={k:2}: a={dec(a)}, B_k={dec(bound)} ({name})")
        qtail = F(23, 2)
        atail = qtail / (1 + high * (qtail - 1))
        choices = [("derivative", Lhi * atail * atail * E(atail))]
        if low:
            choices.append(("direct", E(atail) / low))
        name, tail_bound = min(choices, key=lambda x: x[1])
        assert atail >= F("1.3") and Llo * atail > 2
        components = [B, total, tail_mass * tail_bound]
        rounded_components = [ceil_scaled(value, 10**9) for value in components]
        assert rounded_components == component_ceilings[n], (n, rounded_components)
        B_up, finite_up, tail_up = [F(value, 10**9) for value in rounded_components]
        displayed_upper = B_up + 2 * (1 + v) * (finite_up + tail_up)
        assert displayed_upper < F(expected[n], 1000)
        print(f"  component ceilings at 1e-9 (B, finite, weighted tail): {rounded_components}")
        print(f"  total from displayed component bounds: {displayed_upper} < {F(expected[n], 1000)}")
        final = B + 2 * (1 + v) * (total + tail_mass * tail_bound)
        assert final < 1
        rounded = ceil_scaled(final, 1000)
        assert rounded == expected[n], (n, rounded, expected[n])
        print(f"  B'={dec(tail_bound)} ({name})")
        print(f"  weighted finite part={dec(total)}, weighted tail={dec(tail_mass * tail_bound)}")
        print(f"  FINAL exact comparison: {dec(final)} < {F(expected[n], 1000)} < 1")
        print(f"  upward thousandth: .{rounded:03}")
        # Fingerprint the exact reduced value for reproduction without a giant log.
        exact_bytes = (format(final.numerator, "x") + "/" + format(final.denominator, "x")).encode()
        print(f"  exact rational SHA256 (hex numerator/denominator): {hashlib.sha256(exact_bytes).hexdigest()}")
    print("\nPASS: all four claimed upward-rounded constants reproduced with exact rational arithmetic")


if __name__ == "__main__":
    main()
