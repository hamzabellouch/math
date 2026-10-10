#!/usr/bin/env python3
"""Exact scalar certificate reconstructed from the printed boundary manuscript.

This is a new implementation, not the absent historical scalar_checks.py.
It verifies finite rational/exponential comparisons in sections/periodic.tex,
initialization.tex and conclusion.tex. It does not certify thermal matrices,
trial contractions, transfer identities or the analytic induction itself.
Python's Fraction is used for every mathematical comparison. Decimal display
values are informational only. Run with assertions enabled.
An optional OUTPUT_DIRECTORY argument keeps replay output outside the article:
    python scalar_checks.py OUTPUT_DIRECTORY
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import os
import platform
import sys
import time

if not __debug__ or sys.flags.optimize or os.environ.get("PYTHONOPTIMIZE", "0") not in ("", "0"):
    raise SystemExit("Exact certificate requires assertions enabled.")
# Full rational certificates legitimately exceed Python's decimal-display cap.
sys.set_int_max_str_digits(0)

START = time.monotonic()
CHECKS = []


def encoded(x):
    x = Q(x)
    return {"numerator": str(x.numerator), "denominator": str(x.denominator),
            "display": float(x)}


def lt(name, left, right):
    left, right = Q(left), Q(right)
    if not left < right:
        raise ArithmeticError(f"{name}: strict comparison failed")
    CHECKS.append({"name": name, "left": encoded(left), "right": encoded(right),
                   "positive_margin": encoded(right-left)})


def eq(name, left, right):
    if left != right:
        raise ArithmeticError(f"{name}: equality failed")
    CHECKS.append({"name": name, "equal_value": encoded(left)})


def exp_interval(t):
    t = Q(t)
    if not 0 <= t <= 10:
        raise ValueError("Taylor enclosure proved only for 0 <= t <= 10")
    term = total = Q(1)
    for r in range(1, 81):
        term *= t/r
        total += term
    omitted = term*t/81
    # Every subsequent omitted-term ratio is <= 10/82 < 1/2.
    return total, total+2*omitted


def f(u):
    if not 0 <= u < 1:
        raise ValueError("purity update outside proved domain")
    return u*u/(2*(1-u)**2)


def d(u):
    if not 0 <= u <= Q(".1"):
        raise ValueError("concentration ratio outside proved domain")
    return u/(2-3*u)


def boundary_update(q, e, t):
    if not (0 < q < 1 and 0 <= e < 1 and 0 < t <= 1):
        raise ValueError("boundary update outside proved domain")
    return q/(1-q)*(1/((1-e)**2*t)-1)


ell, U, V = Q(".999"), Q("1.00139"), Q(".872")
mJ, mN = Q("1.0657205"), Q(".2783155")
resJ, resN = mJ-ell**12, mN-V**12
lt("J residual positive", 0, resJ)
lt("J maximal modulus unique", resJ, ell**12)
lt("N first cap is filled", V**12, mN)
lt("N at most two caps", mN, 2*V**12)
lt("rho0 J ratio", resJ, (Q(".874")*ell)**12)
lt("rho0 N ratio", V, Q(".874")*ell)

# D(32) has exponent 8/3; upper-bound its positive cube roots first.
rJ, rN = Q(".426635"), Q(".439736")
lt("D32 J cube root", resJ, rJ**3)
lt("D32 N cube root", resN, rN**3)
D32_upper = (rJ**8 + 3*(V**32+rN**8))/ell**32
D120 = (resJ**10+3*(V**120+resN**10))/ell**120
lt("D32 upper", D32_upper, Q(".0442"))
lt("D120 upper", D120, Q(".00000025"))
lt("b1 dominant mass from purity", Q(".0604996"), 2*Q(".032")*Q(".968"))
lt("b1 dominant root lower", Q(".9856")**9, Q(".968")**4)
tail32_upper = U**64*(1+Q(".0442"))**2/Q(".9856")-1
lt("tail32 upper", tail32_upper, Q(".2092"))
lt("rho1 residual bound", Q(".2092"), Q(".9525")**32)
s = (1+Q(".9525")**60)**-2
Rperiodic_upper = U**120*(1+Q(".00000025"))-1
lt("periodic R positive", 0, Rperiodic_upper)
t_lower = (1+Rperiodic_upper**2)**-2
lt("periodic spatial seed", Q(".9002"), s)
lt("periodic physical seed", Q(".9372"), t_lower)
lt("periodic first coupled output", f(1-Q(".9002")**2*Q(".9372")), Q(".0502"))
lt("periodic second coupled output", f(1-Q(".9372")**2*(1-Q(".0502"))), Q(".0198"))
u = {2: Q(".052")}
for j in range(2, 5):
    u[j+1] = 6*u[j]**2
Gendpoint = sum((1-u[2])**(-r) for r in (1, 2, 3))**2/2
lt("periodic G endpoint", Gendpoint, Q("5.583"))
lt("periodic invariant interval", 6*u[2], 1)
lt("rho2 bound", d(u[2]), Q(".971")**120)

b0, alpha = Q(49, 4), Q(".4042")
expba_lo, expba_hi = exp_interval(b0*alpha)
exp132_lo, exp132_hi = exp_interval(Q(".132"))
P = lambda x: x**3-Q(".14")*x*x-Q(".18")*x
eq("P factorization at U", P(U), U*(U-Q(1, 2))*(U+Q(9, 25)))
lt("P positive at left endpoint", 0, P(ell))
lt("4P-xPprime positive at left endpoint", 0, ell**2-Q(".28")*ell-Q(".54"))
lt("derivative of positive quadratic on interval", 0, 2*ell-Q(".28"))
coefficient_upper = Q(".003745")*expba_hi/P(U)**2
lt("boundary leading coefficient", coefficient_upper, Q("1.133226"))
lt("exponential lower", Q("1.141108"), exp132_lo)
lt("leading coefficient under exponential", coefficient_upper, exp132_lo)
epsilon_upper, R_upper = {}, {}
for m in (34, 78, 142, 240):
    epsilon_upper[m] = Q(".027")*expba_hi*U**m*Q(".874")**(m-6)/ell**6
    R_upper[m] = exp132_hi*U**m+epsilon_upper[m]-1
    lt(f"positive R upper m{m}", 0, R_upper[m])
lt("boundary initial overlap", epsilon_upper[34], Q(".0928"))
purity78 = (1+R_upper[78])**-2
purity142 = (1+R_upper[142]**2)**-2
purity240 = (1+R_upper[240]**4)**-2
lt("boundary purity78", Q(".6180"), purity78)
lt("boundary purity142", Q(".7533"), purity142)
lt("boundary purity240", Q(".7923"), purity240)
lt("boundary e78 output", boundary_update(Q(".953")**44, Q(".093"), purity78), Q(".132129"))
lt("boundary e142 output", boundary_update(Q(".971")**64, Q(".133"), purity142), Q(".137301"))
lt("boundary eta240 output", 1-purity240, Q(".207518"))

rows = [(2, Q(".14"), Q(".21"), Q(".142"), Q(".12"), Q(".155"), Q(".117754"), Q(".147078")),
        (3, Q(".12"), Q(".155"), Q(".0282"), Q(".016"), Q(".026"), Q(".015328"), Q(".025188")),
        (4, Q(".016"), Q(".026"), Q(".0028"), Q(".001"), Q(".001"), Q(".000170"), Q(".000432"))]
for j, E, eta, q_upper, Enext, etanext, Eprinted, etaprinted in rows:
    if j == 2:
        lt("first boundary q root comparison", d(u[3])**49, q_upper**120)
    else:
        lt(f"boundary q square comparison j{j}", d(u[j+1]), q_upper**2)
    Eactual_upper = boundary_update(q_upper, E, 1-eta)
    etaactual_upper = f(1-(1-eta)*(1-u[j])*(1-u[j+1])*(1-Enext))
    lt(f"boundary E output j{j+1}", Eactual_upper, Eprinted)
    lt(f"boundary E rounded closure j{j+1}", Eprinted, Enext)
    lt(f"boundary eta output j{j+1}", etaactual_upper, etaprinted)
    lt(f"boundary eta rounded closure j{j+1}", etaprinted, etanext)

lt("u5 initialization", u[5], Q(".000015"))
x = Q(".01")
lt("q at most 2x via squaring", 6/(2-18*x*x), 4)
Eratio = 2/(1-2*x)*sum((1-x)**(-r) for r in (1, 2, 3))
etaratio = (2+16*x)**2/(2*(1-2*x-16*x*x)**2)
eq("E quadratic endpoint exact", Eratio, Q(42430000, 6792093))
eq("eta quadratic endpoint exact", etaratio, Q(3645000, 1495729))
lt("E quadratic endpoint below10", Eratio, 10)
lt("eta quadratic endpoint below10", etaratio, 10)
lt("quadratic invariant interval", 10*x, 1)
lt("same-field product bound endpoint", 2+26*x, 4)
lt("gap ratio strict constant", Q(4, 10)/(1-4*x), 1)
eq("b5", b0*2**5, 392)
eq("M5", 240*2**3, 1920)
eq("minimum odd length", 2*960+1, 1921)

record = {"provenance": "New exact implementation of printed manuscript recipes; absent historical helper not recovered",
          "python": platform.python_version(), "platform": platform.platform(), "assertions_enabled": True,
          "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          "checks": CHECKS, "success": True, "wall_seconds": time.monotonic()-START}
output = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parent
output.mkdir(parents=True, exist_ok=True)
(output / "scalar-certificate.json").write_text(json.dumps(record, indent=2)+"\n")
print(f"PASS: {len(CHECKS)} exact scalar comparisons and equalities; no floating-point premise")
