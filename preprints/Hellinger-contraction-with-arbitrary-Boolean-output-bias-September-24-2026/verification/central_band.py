#!/usr/bin/env python3
"""Exact rational certificates for the central-band argument.
Adapted from low_bias_exact.py in the original audit.
Uses direct polynomial expansion and the defining monomial/Bernstein identity.
All certification calculations are rational; decimals only describe outputs.
"""
from fractions import Fraction as F
from math import comb
import sympy as sp

u,y,t=sp.symbols('u y t')
Q=sp.Rational

def bernstein(poly, vars, bounds, orders):
    v0,v1=vars
    # Separate fresh variables prevents accidental recursive substitution.
    a,b=sp.symbols('a b')
    repl={v0:bounds[0][0]+a*(bounds[0][1]-bounds[0][0]),
          v1:bounds[1][0]+b*(bounds[1][1]-bounds[1][0])}
    p=sp.Poly(sp.expand(poly.subs(repl, simultaneous=True)),a,b)
    n,k=orders
    assert p.degree(a)<=n and p.degree(b)<=k
    power=[[Q(0) for j in range(k+1)] for i in range(n+1)]
    for (i,j),val in p.terms():power[i][j]=val
    along0=[[sum(power[i][j]*Q(comb(h,i),comb(n,i)) for i in range(h+1)) for j in range(k+1)] for h in range(n+1)]
    return [[sum(along0[i][j]*Q(comb(h,j),comb(k,j)) for j in range(h+1)) for h in range(k+1)] for i in range(n+1)]

a=1-u;c=1-y
Am=1+c+c*c/2
Ap=1+c+3*c*c/4
B=1+(a+c)/2+(a*a+a*c+c*c)/4
J=1+3*(a+c)/4
C=Q(34,1000)
S=2*Am+y*(u**4-16*C*B**2-Q(20,100)*(u+y)**2)
polys=[(y-u)*S-Ap*J*(1-y**4)**2*y,
       Q(88,100)*S-(Ap*J)**2*(1-u**4)*y]
expected=[[134,353,365,278,214,46],[179,364,559,765,983,1214,1457]]
for idx,(poly,bounds,orders) in enumerate(zip(polys,
    [[(Q(0),Q(8,10)),(Q(915,1000),Q(1))],[(Q(8,10),Q(1)),(Q(915,1000),Q(1))]],[(5,12),(6,7)])):
    coeffs=bernstein(poly,(u,y),bounds,orders)
    rowmin=[min(row) for row in coeffs]
    floored=[int(sp.floor(v*1000)) for v in rowmin]
    assert floored==expected[idx],(idx,floored)
    assert min(rowmin)>0
    print('central polynomial',idx+1,'degrees=',sp.Poly(poly,u,y).degree_list(),'floored row minima=',floored,'positive=',True)

for val in [Q(1,2),Q(3,4)]:
    P=2-t+val*(1-t)**2
    residue=sp.factor((-(1-t**4)*sp.diff(P,t)-2*(1-t**3*P))/(1-t)**2)
    print('k comparison residual c=',val,':',residue)
    if val==Q(1,2): assert residue==t*(2*t*t-2*t-1)
    else: assert sp.expand(residue-(2*t+1)*(3*t*t-3*t+1)/2)==0

Plo=2-t+(1-t)**2/2
Phi=2-t+3*(1-t)**2/4
# Sufficient numerators of the derivative estimates, replacing k by proper comparison bound.
print('-kprime>=1 numerator:',sp.factor(2*(1-t**3*Phi)-(1-t**4)))
print('-kprime<=2 numerator:',sp.factor(2*(1-t**4)-2*(1-t**3*Plo)))
print('-kprime<=2.5-1.5t numerator:',sp.factor((Q(5,2)-Q(3,2)*t)*(1-t**4)-2*(1-t**3*Plo)))
assert sp.expand(2*(1-t**3*Phi)-(1-t**4)-(1-t)**2*(-3*t**3+6*t*t+4*t+2)/2)==0
assert sp.expand(2*(1-t**4)-2*(1-t**3*Plo)-t**3*(t-5)*(t-1))==0
assert sp.expand((Q(5,2)-Q(3,2)*t)*(1-t**4)-2*(1-t**3*Plo)-(1-t)**2*(5*t**3-3*t*t-t+1)/2)==0
# The last cubic is positive: on [0,.6], 5t^3-3t^2>=-.16;
# on [.6,1], it is t^2(5t-3)+(1-t), a sum of nonnegative terms.
assert sp.factor(5*t**3-3*t*t+Q(16,100))==(5*t+1)*(5*t-2)**2/Q(25)
assert -Q(16,100)-Q(6,10)+1>0

# Rational check at b=.839, as justified by monotonicity in the proof.
b=F(839,1000); r=F(2944,10000)
ylo=F(91595,100000); alo=F(108834,100000)
assert ylo*ylo<b
prod=F(1); trunc=F(1)
for j in range(1,6):
    prod*=F(4*j-1,4*j)
    trunc+=prod*(1-b*b)**j/F(2*j+1)
assert trunc>alo
phim_over_m=1/(b*alo*alo)-1
pstar=(1+b*b)/(2*alo*b*ylo)-1
Mlo=(1-b*b)*alo*alo
assert 0<phim_over_m<F(63,10000)
assert 0<pstar<F(19,1000)
assert pstar/Mlo<F(532,10000)
delta_over_M=r**3/(4*F(1999,1000))*(1+1/(b*F(84,100)))
assert delta_over_M<F(8,1000)
print('constants9: alpha trunc >',alo,'Phi/M upper=',float(phim_over_m),'p upper=',float(pstar),'p/M upper=',float(pstar/Mlo),'Delta/M upper=',float(delta_over_M))

# Lower range bounds implied by crossing and m<=r²/2.
mcap=r*r/2
assert (1-F(1,1000))**2<1-mcap*mcap
assert F(84,100)-F(1,1000)==b
assert (1-r)*(2/r-r)>F(45,10)
print('variance gain coefficient lower=',float((1-r)*(2/r-r)))

# sqrt-free certification of alpha*y <=1.
c=sp.symbols('c')
assert sp.expand(1-(1-c)*(1+c+3*c*c/4))==c*c/4+3*c**3/4
print('alpha*y upper gap=',c*c/4+3*c**3/4)
loss=F(11,10)**2*F(1,1000)/F(84,100)
assert loss<F(4,1000)
assert F(20,100)*F(45,10)-F(88,100)>F(4,1000)
print('Delta comparison loss upper=',float(loss))

# Certify mean bound <.31 by elementary rational square-root upper bounds.
sqrtr=F(543,1000)
sqrt_cv=F(431,1000) # sqrt(.0063/.034) < .431
sqrtqlo=F(9924,10000)
assert sqrtr*sqrtr>r
assert sqrt_cv**2>F(63,10000)/F(34,1000)
assert sqrtqlo**2<F(985,1000)
meanup=(r*sqrtr/2+sqrt_cv/2)/sqrtqlo
assert meanup<F(31,100)
print('mean/ sqrt(q) upper=',float(meanup))

sqrt3up=F(173206,100000)
assert sqrt3up*sqrt3up>3
B4=F(432,100)
assert B4*B4>1+(2*sqrt3up+F(62,100))*B4
final=F(532,10000)/(F(985,1000)*F(34,1000))+F(19,1000)*B4**2/(1-F(19,1000))
assert final<2
print('final coefficient sum upper=',float(final))
print('PASS: central exact certificates and rational constant bounds')
