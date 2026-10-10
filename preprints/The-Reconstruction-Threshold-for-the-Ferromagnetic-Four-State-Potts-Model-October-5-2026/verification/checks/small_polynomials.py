from fractions import Fraction as F
from itertools import permutations
import json

ZERO=(0,0,0,0)
def add(a,b):
    c=dict(a)
    for i,v in b.items(): c[i]=c.get(i,F(0))+v
    return {i:v for i,v in c.items() if v}
def mul(a,b):
    c={}
    for i,u in a.items():
        for j,v in b.items():
            t=tuple(x+y for x,y in zip(i,j))
            c[t]=c.get(t,F(0))+u*v
    return {i:v for i,v in c.items() if v}
def scale(a,c): return {i:v*c for i,v in a.items() if v*c}
def power(a,k):
    c={ZERO:F(1)}
    for _ in range(k): c=mul(c,a)
    return c
def indices(d):
    for i in range(d+1):
        for j in range(d-i+1):
            for k in range(d-i-j+1):
                yield i,j,k,d-i-j-k
def linear(v):
    return {tuple(int(i==j) for j in range(4)):F(a) for i,a in enumerate(v) if a}
W=linear([1,1,1,1])
X=[linear([1,1,F(1,3),0]),linear([1,0,F(1,3),0]),linear([1,0,F(-1,3),0])]
A=add(add(power(X[0],2),power(X[1],2)),power(X[2],2))
B=mul(mul(X[0],X[1]),X[2])
C=add(add(mul(power(X[0],2),power(X[1],2)),mul(power(X[0],2),power(X[2],2))),mul(power(X[1],2),power(X[2],2)))
basis=[{ZERO:F(1)},A,B,power(A,2),C,mul(A,B),power(A,3),mul(A,C),power(B,2)]
degrees=[0,2,3,4,4,5,6,6,6]
coeffs={
 'H':[0,0,1000,-100,-150,300,-20,70,-510],
 'F':[0,4000,-3000,700,-4000,-800,0,0,0],
 'G':[1000,-1610,-3100,773,4000,-3980,0,0,0],
}
def homogenized(cs,degree):
    r={}
    for c,p,d in zip(cs,basis,degrees):
        if c: r=add(r,scale(mul(p,power(W,degree-d)),F(c,1000)))
    return r
tests=[('H+1/2',6,[500]+coeffs['H'][1:],F(1134673920,2985984000)),
       ('F',5,coeffs['F'],F(0)),
       ('G',14,coeffs['G'],F(21648384,248832000)),
       ('(3-Euler)H',6,[c*(3-d) for c,d in zip(coeffs['H'],degrees)],F(0))]
results=[]
for name,degree,cs,expected in tests:
    p=homogenized(cs,degree)
    low=min(p.get(i,F(0)) for i in indices(degree))
    at=[i for i in indices(degree) if p.get(i,F(0))==low]
    assert low==expected,(name,low,expected)
    results.append(dict(name=name,degree=degree,minimum=str(low),min_indices=at,coefficient_count=len(list(indices(degree)))))

L=[[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]]
for perm in permutations(range(4)):
    # T = L P L^t / 4: x-coordinate action of permuting p.
    T=[[sum(F(L[i][k]*L[j][perm[k]],4) for k in range(4)) for j in range(3)] for i in range(3)]
    assert all(sum(t!=0 for t in row)==1 for row in T)
    assert all(sum(T[i][j]!=0 for i in range(3))==1 for j in range(3))
    nonzero=[t for row in T for t in row if t]
    assert all(abs(t)==1 for t in nonzero)
    assert nonzero[0]*nonzero[1]*nonzero[2]==1
print(json.dumps({'small_checks':results,'all_24_symmetry_actions_verified':True},indent=2))
