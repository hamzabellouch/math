#!/usr/bin/env python3
"""Verify the finite arithmetic certificate for the degree-31 example.

From the manuscript project root, run with Python 3 (without -O):
    python3 verification/verify_degree31.py

Only the Python standard library is used. Every mathematical calculation uses
integers or fractions.Fraction; no floating-point operation enters the proof.
The script checks root-center inequalities, coefficient arrays, rounded cosine
products, predictor sums, and finite products bounding the anisotropy term.
The accompanying manuscript proves the analytic error bounds that relate these
finite calculations to the infinite products.

A real represented by the integer n means n/S. A complex number is a pair of
such integers. The root centers instead have denominator E. Every rounding is
to the nearest integer, with a tie rounded toward positive infinity. In
particular, changing the order of a rounded multiplication and a summation can
change this certificate. The order below is part of its specification.
"""

from fractions import Fraction


S = 10**30
E = 10**40
W = 10**9
R = 3000
H = 100
K = 2000
ONE = (S, 0)
PI = 3141592653589793238462643383279

# Ascending coefficients of x^31 - 2*x^30 + sum_{j=0}^9 (x^(3*j+1)-x^(3*j)).
POLYNOMIAL = [-1, 1, 0] * 10 + [-2, 1]
DERIVATIVE = [i * POLYNOMIAL[i] for i in range(1, 32)]

# One representative of each conjugate pair, together with the real root.
# Each pair (x, y) represents (x + i*y)/E.
ROOT_CENTERS = [
    (18392867573155250211326543340571993487329, 0),
    (-9741384652837567528189111907762645564212, 960611633124778624015947511546714789832),
    (-9390979934023233037686839914141181659013, 2848063934279278841200845525848576791934),
    (-8707010393241200595697704637503228167256, 4634358961359777463662031763152574795910),
    (-7723118558199735333585947045021501410451, 6250214494152701297733561366714273855663),
    (-6480873022754265587670654805348739312397, 7617033927823246411701558316834470378693),
    (-3296776282962928450195355562079974291919, 9362810613239308448752821856735617305389),
    (-1442513481645415489053007250852371013818, 9733039088635544125591234293715446465839),
    (473579005983151143865690217073943282984, 9759329295153416086962240697595385836176),
    (2372858204750359429049351486827380431084, 9430908396110323024329804770889268443510),
    (4184061662454447896993374181551299054853, 8750376307352230997951514116951420713869),
    (5840543823426662247726359012202878127980, 7733999914049269380846159864123679516166),
    (7280042164772721585016920411987150804420, 6409668313572020921539025901166241650504),
    (8444162922855313595050499086097221186662, 4814843758334683329011653039104490553475),
    (9275649862302447872891854755866108397375, 2996533501299661135726051235425500195711),
    (9715324892541617145821300300817663390044, 1019107767839771580294306582422817927060),
]

EXPECTED_BIASES = (
    -1213260259553686847254563674,
    -1184318907352990016201416104,
)
EXPECTED_CORRELATION = 211815537786494774284357596751188225
EXPECTED_VARIANCE = 143920884250294630908494564120361905955993456
EXPECTED_BIG_GRAM = 105303788239450118397416374596041413014338334
EXPECTED_FACTORS = (
    10861284406435197401851134503,
    14731866010915969694738277129,
    3155364376927094122833206055,
)
BINOMIAL = {
    2: (1, 2, 1),
    4: (1, 4, 6, 4, 1),
    6: (1, 6, 15, 20, 15, 6, 1),
}


def report(message):
    """Flush stage messages so redirected output also shows progress promptly."""
    print(message, flush=True)


def rounded_ratio(numerator, denominator):
    """Round numerator/denominator to an integer; denominator must be positive."""
    return (numerator + denominator // 2) // denominator


def raw_product(z, w):
    """Multiply Gaussian integer pairs without rescaling."""
    x, y = z
    a, b = w
    return x * a - y * b, x * b + y * a


def add(z, w):
    return z[0] + w[0], z[1] + w[1]


def negate(z):
    return -z[0], -z[1]


def conjugate(z):
    return z[0], -z[1]


def norm_squared(z):
    return z[0] ** 2 + z[1] ** 2


def scale(z, numerator, denominator):
    """Multiply both components by a rational and round componentwise."""
    return (
        rounded_ratio(z[0] * numerator, denominator),
        rounded_ratio(z[1] * numerator, denominator),
    )


def reciprocal(z, denominator):
    """Return the reciprocal of z/denominator, represented at scale S."""
    return scale(conjugate(z), denominator * S, norm_squared(z))


def complex_product(z, w):
    """Multiply two scale-S complex numbers, rounding once per component."""
    return scale(raw_product(z, w), 1, S)


def product(x, y):
    """Multiply two scale-S reals and round once."""
    return rounded_ratio(x * y, S)


def quotient(z, w):
    """Divide two scale-S complex numbers and round once per component."""
    return scale(raw_product(z, conjugate(w)), S, norm_squared(w))


def verify_pi():
    """Check the displayed pi approximation by Machin's alternating series."""
    def arctangent_reciprocal(q, terms):
        return sum(
            Fraction((-1) ** j, (2 * j + 1) * q ** (2 * j + 1))
            for j in range(terms)
        )

    center = 16 * arctangent_reciprocal(5, 30) - 4 * arctangent_reciprocal(239, 10)
    radius = Fraction(16, 61 * 5**61) + Fraction(4, 21 * 239**21)
    assert abs(center - Fraction(PI, S)) + radius < Fraction(1, S)


def horner(coefficients, z):
    """Evaluate at z/E exactly; return a Gaussian numerator and denominator."""
    value = (coefficients[-1], 0)
    denominator = 1
    for coefficient in coefficients[-2::-1]:
        denominator *= E
        value = add(raw_product(value, z), (coefficient * denominator, 0))
    return value, denominator


def prepare_roots():
    """Check the root disks and return the rounded base/coefficient pairs."""
    all_centers = ROOT_CENTERS + [conjugate(z) for z in ROOT_CENTERS if z[1]]
    assert len(all_centers) == 31
    for i, z in enumerate(all_centers):
        for w in all_centers[:i]:
            assert norm_squared(add(z, negate(w))) * 10000 > E**2

    # Taylor's theorem gives the nonlinear remainder on every radius-10^-35
    # disk. Together with the residual and derivative checks below, this is
    # strictly less than half the linear term on the disk boundary.
    second_derivative_bound = sum(
        abs(coefficient) * i * (i - 1) * Fraction(2001, 1000) ** (i - 2)
        for i, coefficient in enumerate(POLYNOMIAL)
        if i >= 2
    )
    assert second_derivative_bound < 4 * 10**13
    assert Fraction(2 * 10**13, 10**70) < Fraction(1, 2 * 10**35)

    stable = []
    beta = weak = None
    for z in ROOT_CENTERS:
        value, value_denominator = horner(POLYNOMIAL, z)
        derivative, derivative_denominator = horner(DERIVATIVE, z)
        derivative_max = max(map(abs, derivative))
        assert derivative_max > derivative_denominator
        assert (
            2 * (abs(value[0]) + abs(value[1])) * derivative_denominator * 10**35
            < value_denominator * derivative_max
        )
        squared_modulus = norm_squared(z)
        assert squared_modulus < 4 * E**2
        inverse_derivative = reciprocal(derivative, derivative_denominator)
        if squared_modulus < E**2:
            assert squared_modulus * 10**8 < 9939**2 * E**2
            stable.append((scale(z, S, E), inverse_derivative))
        else:
            base = reciprocal(z, E)
            pair = (base, negate(complex_product(base, inverse_derivative)))
            if z[1] == 0:
                assert 183928 * E < z[0] * 100000 < 183929 * E
                beta = pair
            else:
                assert 10002090 * E**2 < squared_modulus * 10**7 < 10002093 * E**2
                weak = pair
    assert len(stable) == 14 and beta is not None and weak is not None
    for base, coefficient in stable + [beta, weak]:
        assert norm_squared(coefficient) <= S**2
        assert norm_squared(base) < S**2
    report("Root checks passed: 31 disjoint disks; 28 contracting roots, beta, and one weak pair.")
    return stable, beta, weak


def cosine_sine(coefficient):
    """Evaluate the prescribed 50-step Taylor recurrences at pi'*coefficient."""
    x = product(coefficient, PI)
    assert abs(x) <= 13 * S
    y = product(x, x)
    cosine = cosine_term = S
    sine = sine_term = x
    for j in range(1, 51):
        cosine_term = rounded_ratio(-cosine_term * y, S * (2 * j) * (2 * j - 1))
        cosine += cosine_term
        sine_term = rounded_ratio(-sine_term * y, S * (2 * j) * (2 * j + 1))
        sine += sine_term
    return cosine, sine


class Certificate:
    """Coefficient arrays and the finite products built from them."""

    def __init__(self):
        stable, beta, weak = prepare_roots()
        self.offset = R + K + 5
        upper = H + K + 5
        c0 = [0] * (self.offset + upper + 1)
        for base, coefficient in stable:
            value = coefficient
            for position in range(self.offset - 1, -1, -1):
                c0[position] += 2 * value[0]
                value = complex_product(value, base)
        for (base, coefficient), multiplicity in [(beta, 1), (weak, 2)]:
            value = coefficient
            for position in range(self.offset, len(c0)):
                c0[position] += multiplicity * value[0]
                value = complex_product(value, base)

        # Padding supplies the shifts in c1; its unused endpoints stay zero.
        c1 = [0] * len(c0)
        for position in range(1, len(c0) - 3):
            c1[position] = c0[position + 3] - c0[position] + c0[position - 1]
        self.coefficients = [c0, c1]
        self.cosines = []
        self.sines = []
        for array in self.coefficients:
            assert max(map(abs, array)) < S
            pairs = list(map(cosine_sine, array))
            self.cosines.append([z[0] for z in pairs])
            self.sines.append([z[1] for z in pairs])

        base, coefficient = weak
        self.base_powers = [ONE]
        for _ in range(max(K, H) + 6):
            self.base_powers.append(complex_product(self.base_powers[-1], base))
        shift = add(add(self.base_powers[3], negate(ONE)), quotient(ONE, base))
        self.weak_coefficients = [coefficient, complex_product(coefficient, shift)]
        self.check_coefficient_arrays()

    def check_coefficient_arrays(self):
        """Assert exact extrema, selected entries, and weak-pair coefficients."""
        expected_maxima = (
            (616455676740679424557814387144, -30),
            (846098324869156158975340856850, -33),
        )
        for kind, expected in enumerate(expected_maxima):
            maximum, index = max(
                (abs(self.coefficients[kind][self.offset + m]), m)
                for m in range(-R - K, H + K)
            )
            assert (maximum, index) == expected
            assert self.coefficients[kind][self.offset + index] == -maximum
            assert maximum * 1000 < 847 * S
            report(f"max |c{kind}(m)| on -5000 <= m < 2100: numerator {maximum} / S, attained at m={index}")
        left_cutoff_maximum = max(map(abs, self.coefficients[0][self.offset - 20:]))
        assert left_cutoff_maximum == 17264401918515033650241407234
        assert self.coefficients[0][self.offset - 17] == -left_cutoff_maximum
        assert left_cutoff_maximum * 1000 < 18 * S
        selected = {
            (0, -31): -151775740200029261809764733416,
            (0, -30): -616455676740679424557814387144,
            (1, -31): -123749354522413387781420795174,
            (0, -20): -14682724915971217464440762764,
            (0, 0): -11434003260824889800421059336,
            (1, 0): 5929686006408956256123618128,
        }
        for (kind, index), expected in selected.items():
            assert self.coefficients[kind][self.offset + index] == expected
        assert self.weak_coefficients == [
            (-5716998075981014029485068972, 6419576770661208625648815669),
            (2964846557635914510021382536, -6485314851979210752736418593),
        ]
        assert max(map(norm_squared, self.weak_coefficients)) * 10**8 < 87**2 * S**2
        report(f"max |c0(m)| on -20 <= m <= 2105: numerator {left_cutoff_maximum} / S")
        report("Coefficient arrays, selected entries, and weak-pair bounds passed.")

    def tail(self, coefficient):
        """Approximate the tail using moments of degrees 2, 4, and 6."""
        value = complex_product(coefficient, self.base_powers[H])
        powers = [ONE]
        for _ in range(6):
            powers.append(complex_product(powers[-1], value))
        pi_power = S
        penalty = 0
        for degree in range(1, 7):
            pi_power = product(pi_power, PI)
            if degree % 2:
                continue
            moment = 0
            for j in range(degree + 1):
                numerator = complex_product(powers[j], conjugate(powers[degree - j]))
                denominator = add(
                    ONE,
                    negate(complex_product(self.base_powers[j], conjugate(self.base_powers[degree - j]))),
                )
                assert norm_squared(denominator) * 10**10 > 19**2 * S**2
                moment += BINOMIAL[degree][j] * quotient(numerator, denominator)[0]
            divisor = (2, 12, 45)[degree // 2 - 1]
            penalty += rounded_ratio(pi_power * moment, S * divisor)
        assert abs(penalty) < 32 * S
        x = rounded_ratio(-penalty, 32)
        value = term = S
        for j in range(1, 41):
            term = rounded_ratio(term * x, S * j)
            value += term
        for _ in range(5):
            value = product(value, value)
        return value

    def single(self, kind):
        """Return the scale-S approximation to P_kind."""
        value = self.tail(self.weak_coefficients[kind])
        for cosine in self.cosines[kind][self.offset - R:self.offset + H]:
            value = product(value, cosine)
        return value

    def moments(self, first, second, shift):
        """Return (P^+_{first,second}(shift), P^-_{first,second}(shift))."""
        start = self.offset - R - shift
        end = self.offset + H
        shifted = complex_product(self.weak_coefficients[second], self.base_powers[shift])
        plus = self.tail(add(self.weak_coefficients[first], shifted))
        minus = self.tail(add(self.weak_coefficients[first], negate(shifted)))
        half = S // 2
        for ca, sa, cb, sb in zip(
            self.cosines[first][start:end],
            self.sines[first][start:end],
            self.cosines[second][start + shift:end + shift],
            self.sines[second][start + shift:end + shift],
        ):
            dot = ca * cb
            cross = sa * sb
            # First round the cosine addition formula, then the running product.
            # These two roundings must remain separate.
            plus = (plus * ((dot - cross + half) // S) + half) // S
            minus = (minus * ((dot + cross + half) // S) + half) // S
        return plus, minus

    def predictor(self):
        """Build the predictor and check its correlation, variance, and Gram sum."""
        biases = tuple(self.single(kind) for kind in range(2))
        assert biases == EXPECTED_BIASES
        main = []
        for shift in range(K + 1):
            main.append(self.moments(0, 0, shift))
            if shift % 250 == 0:
                report(f"Pair moments computed through k={shift}/{K}")
        target1 = self.moments(0, 1, 33)[0]
        constant = -(W // 1000)
        extra = 55 * (W // 10000)
        rows = []
        correlation = constant * biases[0] + extra * target1
        cross = {}
        for shift in range(30, K + 1):
            for sign, moment in enumerate(main[shift]):
                weight = make_weight(moment)
                if not weight:
                    continue
                rows.append((weight, shift, sign))
                correlation += weight * moment
                if shift not in cross:
                    cross[shift] = (
                        self.moments(1, 0, shift - 33) if shift >= 33
                        else self.moments(0, 1, 33 - shift)
                    )
        variance = (constant**2 + extra**2) * S + 2 * constant * extra * biases[1]
        big_gram = 0
        for i, (wi, k, sign) in enumerate(rows):
            # In a conjugate product, equal phase signs require the minus moment.
            variance += 2 * wi * (constant * biases[0] + extra * cross[k][int(sign == 0)])
            for j in range(i + 1):
                wj, ell, other_sign = rows[j]
                contribution = wi * wj * main[abs(k - ell)][int(sign == other_sign)] * (1 + (i != j))
                variance += contribution
                if k >= 50 and ell >= 50:
                    big_gram += abs(contribution)
        total_weight = abs(constant) + extra + sum(abs(row[0]) for row in rows)
        # A phase row is (weight numerator, coefficient kind, shift, sign).
        # kind=None denotes the constant phase. sign=0 is plus; sign=1 is minus.
        small = [(constant, None, 0, 0), (extra, 1, 33, 0)] + [
            (weight, 0, shift, sign)
            for weight, shift, sign in rows if shift < 50
        ]
        small_weight = sum(abs(row[0]) for row in small)
        assert len(rows) == 753
        assert total_weight == 198442946
        assert small_weight == 11816095
        assert correlation == EXPECTED_CORRELATION
        assert variance == EXPECTED_VARIANCE
        assert big_gram == EXPECTED_BIG_GRAM
        assert total_weight * 1000 < 199 * W and small_weight * 1000 < 12 * W
        assert 211810 * W * S < correlation * 10**9 < 211820 * W * S
        assert 143910 * W**2 * S < variance * 10**9 < 143930 * W**2 * S
        assert 105300 * W**2 * S < big_gram * 10**9 < 105310 * W**2 * S
        report(f"bias numerators / S: {biases}")
        report(f"nonzero variable weight rows: {len(rows)}")
        report(f"total absolute weight numerator / W: {total_weight}")
        report(f"small absolute weight numerator / W: {small_weight}")
        report(f"correlation numerator / (W*S): {correlation}")
        report(f"variance numerator / (W^2*S): {variance}")
        report(f"big Gram numerator / (W^2*S): {big_gram}")
        return small

    def factor(self, rows, number_big, lower):
        """Return an upward-rounded finite product for an anisotropy bound."""
        value = S
        error = S // 10**15
        for m in range(lower, 1):
            coefficient = 2 * self.coefficients[0][self.offset + m]
            for _, kind, shift, sign in rows:
                if kind is not None:
                    coefficient += (1 - 2 * sign) * self.coefficients[kind][self.offset + m + shift]
            cosine, sine = cosine_sine(coefficient)
            cosine = abs(cosine) + error
            sine = abs(sine) + error
            if number_big == 1:
                bound = rounded_ratio(1002 * (100 * cosine + 6 * sine), 1000 * 100) + 1
            elif number_big == 2:
                bound = rounded_ratio(1004 * (10036 * cosine + 1200 * sine), 1000 * 10000) + 1
            else:
                bound = cosine
            value = product(value, min(bound, S)) + 1
        return value

    def anisotropy(self, small):
        """Check the three product maxima used for the anisotropy estimate."""
        big = self.factor([], 2, -70)
        cross = max(self.factor([row], 1, -70) for row in small)
        report("Computing anisotropy products over all ordered pairs of small rows.")
        pair = max(self.factor([a, b], 0, -200) for a in small for b in small)
        assert (big, cross, pair) == EXPECTED_FACTORS
        assert big * 1000 < 11 * S
        assert cross * 1000 < 15 * S
        assert pair * 10000 < 32 * S
        report(f"anisotropy factor numerators / S: {(big, cross, pair)}")


def make_weight(moment):
    """Apply the threshold .00026 and shrinkage .68, rounding at scale W."""
    magnitude = max(0, abs(moment) - 26 * (S // 10**5))
    return (1 if moment > 0 else -1) * rounded_ratio(68 * magnitude * W, 100 * S)


def main():
    """Execute every assertion and print the exact certificate numerators."""
    if not __debug__:
        raise RuntimeError("Run without -O: this verifier requires assertions.")
    report("Degree-31 certificate: exact integer arithmetic, S=10^30, E=10^40, W=10^9.")
    verify_pi()
    report("Pi approximation passed.")
    certificate = Certificate()
    small = certificate.predictor()
    certificate.anisotropy(small)
    report("PASS: all degree-31 finite arithmetic checks passed.")


if __name__ == "__main__":
    main()
