import numpy as np
from scipy.sparse import csr_matrix
import itertools
from fractions import Fraction as F
from math import isqrt,factorial,comb

a0=F(700741,500000)
b0=F(49,4)
J=280
Q=2**55
assert 98**281 < factorial(281)
v=[98**j*(factorial(J)//factorial(j)) for j in range(J+1)]
c=[x*Q//sum(v) for x in v]
m=max(i for i,x in enumerate(c) if x)
cc=c[:m+1]

def dmat(words,tw):
    n=len(words[0]); d=len(words)
    lut={w:j for j,w in enumerate(words)}
    data=[]; row=[]; col=[]
    def push(j,k,x):
        data.append(x); row.append(j); col.append(k)
    for j,w in enumerate(words):
        push(j,j,32-3*n-2*sum(w[i-1]*w[i] for i in range(n)))
        for i in range(n):
            for s in (-1,1):
                v=list(w); v[i-1]+=s; v[i]-=s
                if abs(v[i-1])<=1 and abs(v[i])<=1:
                    push(j,lut[tuple(v)],2 if tw and i==0 else -2)
    return csr_matrix((data,(row,col)),shape=(d,d),dtype=np.int64)

def reps(words):
    flip=(sum(words[0])==0)
    n=len(words[0])
    rows=[]; mult=[]
    for j,w in enumerate(words):
        orb={v[i:]+v[:i] for v in (w,w[::-1]) for i in range(n)}
        if flip: orb |= {tuple(-s for s in v) for v in orb}
        if w==min(orb):
            rows.append(j); mult.append(len(orb)*(1 if flip else 2))
    assert sum(mult)==len(words)*(1 if flip else 2)
    return rows,mult

def raw(n,tw,batch):
    W=0
    for M in range(n+1):
        words=[w for w in itertools.product((-1,0,1),repeat=n) if sum(w)==M]
        D=dmat(words,tw)
        rows,mult=reps(words)
        for j in range(0,len(rows),batch):
            rr=rows[j:j+batch]
            idx=rr,list(range(len(rr)))
            X=np.zeros((len(words),len(rr)),dtype=np.int64)
            for ck in reversed(cc):
                X=(D@X)//32
                X[idx]+=ck
            sq=(X.astype(object)**2).sum(axis=0)
            W+=sum(x*m for x,m in zip(sq,mult[j:j+batch]))
    return int(W)

def scale(n):
    x=b0*n*(F(3,2)-a0)
    assert 0<=x<15
    y=z=F(1)
    for j in range(1,101):
        z*=x/j; y+=z
    return y,y+z

table=[
[124885379,65757],[2925,2960742],[12870614,286599],
[54069,1920414],[4639283,510140],[195455,1514846],
[2654823,675419],[377629,1314544],[1900547,787405],
]
eps=F(30,10**6)

def therm(n,tw,batch):
    W=raw(n,tw,batch)
    sl,sh=scale(n)
    d=isqrt(3**n)+1
    err=d*((J+1)*(d+1)+1)
    r=isqrt(W)
    lo=sl*F(max(0,r-err)**2,Q**2)
    hi=sh*F((r+1+err)**2,Q**2)
    cen=F(table[n-4][tw],10**6)
    print(n,tw,W,flush=True)
    assert lo>cen-eps and hi<cen+eps

