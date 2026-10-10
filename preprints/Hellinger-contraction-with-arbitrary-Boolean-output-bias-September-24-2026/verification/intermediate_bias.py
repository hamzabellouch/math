#!/usr/bin/env python3
"""Exact certificates for the intermediate-bias argument.
Adapted from low_bias_middle_exact.py in the original audit.
Bernstein conversion is direct monomial expansion plus binomial basis identity.
"""
import sympy as sp
from math import comb
Q=sp.Rational
T,x=sp.symbols('T x')
D=1+x*x; N=1-x*x-2*T*x; z=2*x; k=2*x+T*(1-x*x)
P=D*D*(N**4+k*k*N*N/2)+z*z*(Q(173,360)*N**4+Q(11,24)*k*k*N*N+Q(7,32)*k**4)
def R(e):return D*D+(N-D)*D/2-e*(N-D)**2
first=sp.Poly(sp.expand(R(Q(19,100))*P-D**4*N**4*(1-Q(33,10)*T*T+Q(7,4)*(T+x)**2)),T,x)

def coefficients(poly,vars,orders,bounds):
    A,B=sp.symbols('A B')
    p=sp.Poly(sp.expand(poly.subs({vars[0]:bounds[0][0]+(bounds[0][1]-bounds[0][0])*A,vars[1]:bounds[1][0]+(bounds[1][1]-bounds[1][0])*B},simultaneous=True)),A,B)
    n,m=orders
    assert p.degree(A)<=n and p.degree(B)<=m
    a=[[Q(0)]*(m+1) for i in range(n+1)]
    for (i,j),v in p.terms():a[i][j]=v
    b=[[sum(a[i][j]*Q(comb(h,i),comb(n,i)) for i in range(h+1)) for j in range(m+1)] for h in range(n+1)]
    return [[sum(b[i][j]*Q(comb(h,j),comb(m,j)) for j in range(h+1)) for h in range(m+1)] for i in range(n+1)]

A,B=sp.symbols('A B')
for arrangement,orders,expected in [(0,(8,18),[90,27]),(1,(8,6),[293,120])]:
    for sign,floor_expected in zip([-1,1],expected):
        p=0
        for (i,j),v in first.terms():
            assert (i+j)%2==0 and i+j>=2
            power=(i+j)//2-1
            p+=v*Q(21,100)**i*(sign*Q(1,2))**j*A**power*B**(j if arrangement==0 else i)
        bc=coefficients(p,(A,B),orders,[(0,1),(0,1)])
        mini=min(min(row) for row in bc)
        floor=int(sp.floor(1000*mini))
        assert mini>0 and floor==floor_expected,(arrangement,sign,floor)
        print('first polynomial arrangement=',arrangement,'sign=',sign,'orders=',orders,'floored 1000 minimum=',floor)

for T0,eps,expected in [(Q(9,10),Q(1,100),53),(Q(111,100),Q(2,100),26)]:
    poly=sp.expand(z*z*(R(Q(17,100))*P-Q(168,100)*D**4*N**4*(T+x)**2)+eps*D**6*N**4)
    min_all=None
    for i in range(4):
        for j in range(4):
            bounds=[(i*T0/4,(i+1)*T0/4),(-Q(7,10)+j*Q(28,100),-Q(7,10)+(j+1)*Q(28,100))]
            bc=coefficients(poly,(T,x),(6,20),bounds)
            m=min(min(row) for row in bc)
            assert m>0
            min_all=m if min_all is None else min(m,min_all)
    floor=int(sp.floor(10000*min_all))
    assert floor==expected,(T0,floor)
    print('second polynomial T0=',T0,'eps=',eps,'floored 10000 minimum=',floor)
print('PASS: all six intermediate Bernstein minima independently reproduced')

# Rational endpoint and elementary margin checks, the intermediate-bias scalar bounds.
from fractions import Fraction as F
s0=F(84,100); cm=F(87,1000)
assert F(2944,10000)**2 < cm
assert 4/(s0*(1+s0)**3)+4*(1-s0)*F(6,100)/(1+s0)<F(8,10)
assert (1-cm)/(1+F(6,100))-F(51,100)*F(6,100)>F(8,10)
assert 2*F(16,100)**2/(s0*(1+s0)*F(6,100))+4*F(16,100)*F(2,10)/(1+s0)<F(64,100)
assert (1-cm)/(1+F(2,10))-F(51,100)*F(2,10)>F(64,100)
for mm in [F(1,5),F(2,3)]:
    # Q0 upper endpoint < .866; every expression positive, so compare squares.
    assert (1+cm*mm)**2 < F(866,1000)**2*(1-mm*mm)*(1+mm)**2
assert (1+cm*F(2,3))**2 < F(852,1000)**2*(1-F(2,3)**2)*(1+F(2,3))**2
qstar=2*(2*s0-1)/(s0*(1+s0))
assert qstar>F(879,1000)
assert F(1,100)<(1+s0)*(F(879,1000)-F(866,1000))/2
assert F(2,100)<(1+s0)*(F(879,1000)-F(852,1000))/2
# Root approximation coefficients and negative-term coefficients at guaranteed q.
assert F(657,1000)**2<F(432,1000)
assert 1/(2*(1+F(657,1000))**2)<F(19,100)
assert 1+2/(1+F(657,1000))**2<F(175,100)
# q>=1/sqrt(3.48); a lower bound .732 on sqrt(q) is verified by fourth powers.
assert F(732,1000)**4*F(348,100)<1
assert 1/(2*(1+F(732,1000))**2)<F(17,100)
assert 1+2/(1+F(732,1000))**2<F(168,100)
# 1-3.3w >= (1-3w)/sqrt(1+w) for w=T²<=.21².
assert F(4,10)-F(471,100)*F(21,100)**2>0
print('PASS: rational root-coefficient and middle-band scalar margins')
