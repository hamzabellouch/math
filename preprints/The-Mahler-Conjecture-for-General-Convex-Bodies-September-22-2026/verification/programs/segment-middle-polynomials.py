"""Independent exact-rational reconstruction of input.md lines 1161--1206.

Run with Python 3 and SymPy. Every polynomial and Bernstein coefficient is
rational; numerical decimal displays are reporting aids only.
"""
from pathlib import Path
import json
import math
import sympy as sp

OUT = Path(__file__).resolve().parent
h = sp.Symbol('h')
Q = sp.Rational
r, w, lam, chi = Q('0.22'), Q('4.6'), Q('0.65'), Q('0.064')
G = r*r*w*w
dK = Q('0.80')*Q('1.25')/Q('0.352')**2
dC = Q('0.80')*5*Q('0.043')**2/Q('0.352')**2
L_C = lambda x: 2*Q('0.728')/3-Q('0.812')*x/2
L_N = lambda x: 2*Q('0.24')/3-Q('0.277')*x/2
ds = Q('0.07052')-Q('0.0754')*h
bs = Q('0.281')-Q('0.254')*h
Su = 1+h*h/6+Q('0.0084')*h**4
Hu = 1+h*h/2+Q('0.0421')*h**4
gu = 3*Su*(1+Hu)/4
Ba = Q('0.193')**2*(Q(4,3)+Q('0.05')*h*h)
Bd = Q('0.078')*h**3
s = [Q(1,math.factorial(2*i+1)) for i in range(8)]
a = [Q(1,math.factorial(2*i)) for i in range(8)]
d = [(-4*w*w)**i/math.factorial(2*i+1) for i in range(8)]
e = [2*(-4*w*w)**i/math.factorial(2*i+2) for i in range(8)]
conv = lambda x,y,i: sum(x[j]*y[i-j] for j in range(i+1))
Pu = Q('0.00025') + 2*G/(1+w*w)*(
    sum((s[i]-conv(a,d,i))*h**(2*i-2) for i in range(1,8))
    +sum(conv(s,e,i)*h**(2*i) for i in range(8)))
F = G/(1+w*w)*sum(2*4**i*(1-(-w*w)**i)*h**(2*i-2)
                   /math.factorial(2*i+2) for i in range(1,7))
T4 = ((1+chi)*h*h*F
      -Su**2*(Q('0.0584')*h*h+Q('0.00025')+chi*h*h*Ba
                +(Q('0.08')+Bd)**2/(4*lam))
      -chi*h*h*Pu*Su
      -h**4*(Pu+Su*(gu*L_C(h/2)/3+Ba))**2/(4*lam))
T5 = ((1+chi)*F
      -Su**2*((gu*L_N(h)+12*dK*ds**2+12*dC*bs**2)/3
                +bs**2/(4*lam)+Q('0.027')*h*h)
      -h*h*(Pu+Su*gu*L_C(h)/3)**2/(4*lam)-chi*Pu*Su)

def bernstein(expr):
    p=sp.Poly(expr,h)
    n=p.degree()
    cs=[p.nth(i) for i in range(n+1)]
    origin, width = Q('0.16'), Q('0.38')
    power=[width**i*sum(cs[j]*math.comb(j,i)*origin**(j-i)
                       for j in range(i,n+1)) for i in range(n+1)]
    bs=[sum(Q(math.comb(r,i),math.comb(n,i))*power[i]
            for i in range(r+1)) for r in range(n+1)]
    # Verify independently by polynomial synthesis from the Bernstein basis.
    x=sp.Symbol('x')
    synthesis=sum(bs[i]*math.comb(n,i)*x**i*(1-x)**(n-i)
                  for i in range(n+1))
    assert sp.Poly(synthesis-p.as_expr().subs(h,origin+width*x),x).is_zero
    return p,bs

results={}
claims={'T4':[173,576,770,412], 'T5':[1586,701,408,407]}
for name,expr in [('T4',T4),('T5',T5)]:
    p,coeffs=bernstein(expr)
    group=[]
    for k,start in enumerate(range(0,len(coeffs),8)):
        # The fourth group includes 24:32 for T4, as in the manuscript.
        if start>24:
            break
        end=len(coeffs) if start==24 else start+8
        low=min(coeffs[start:end])
        argmin=start+coeffs[start:end].index(low)
        claim=claims[name][k]
        group.append({'start':start,'end':end-1,'minimum_index':argmin,
                      'minimum_times_1e5':str(sp.N(low*10**5,25)),
                      'claim':claim,'claim_true':bool(low*10**5>=claim)})
    results[name]={'degree':p.degree(),
                   'all_positive':all(b>0 for b in coeffs),
                   'power_coefficients':{str(i):str(p.nth(i))
                                         for i in range(p.degree()+1)},
                   'bernstein_coefficients':[str(b) for b in coeffs],
                   'bernstein_decimals':[str(sp.N(b,25)) for b in coeffs],
                   'groups':group}
    print(name, 'degree =',p.degree(),'all positive =',all(b>0 for b in coeffs))
    for g in group:
        print(g)

# Verify tail estimates from lines 1178--1183 using rational upper bounds.
fac=2*G/(1+w*w)
H=Q('0.54')
tail1=lambda i:(1+Q('9.26')**(2*i+1)/(2*w))/math.factorial(2*i+1)
tail2=lambda i:(1+(1+2*w)**(2*i+3))/(2*w*w*math.factorial(2*i+3))
index8=fac*(tail1(8)*H**14+tail2(8)*H**16)
ratios=[tail1(i+1)*H**2/tail1(i) for i in range(8,50)]
ratios += [tail2(i+1)*H**2/tail2(i) for i in range(8,50)]
results['Pu_tail']={'index8':str(sp.N(index8,25)),
                    'max_ratio_indices_8_to_49':str(sp.N(max(ratios),25)),
                    'bound_using_0.10_ratio':str(sp.N(index8/Q('0.9'),25)),
                    'index8_claim_true':bool(index8<Q('0.000153')),
                    'allowance_sufficient':bool(index8/Q('0.9')<Q('0.00025'))}
print('Pu_tail',results['Pu_tail'])
(OUT/'segment-middle-polynomials-results.json').write_text(json.dumps(results,indent=2)+'\n')
