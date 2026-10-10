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

for n in range(4,13):
    for tw in range(2):
        therm(n,tw,32)

N=72
I=[(l,a) for l,k in ((1,4),(3,3),(5,1)) for a in range(k)]
labels=[(l,a,d) for l,a in I for d in range(-l,l+1,2)]
diag=dict(zip(I,[-289,-84,-9,33,-22,27,71,-11]))
pairs=[(x,y) for x in I for y in I if y[0]-x[0]==2]
off=dict(zip(pairs,[-11,-35,-28,-23,16,-49,-6,-25,-20,-34,9,-32,1,2,-16]))
A={s:np.zeros((len(labels),len(labels)),dtype=object) for s in (-1,0,1)}
for l,a,d in labels:
 for k,b in I:
    if abs(k-l)>2: continue
    if k==l: p=diag[l,a] if a==b else 0
    if k>l: p=off[(l,a),(k,b)]
    if k<l: p=-off[(k,b),(l,a)]
    for s in A:
        if abs(d+2*s)>k: continue
        r=(d+l)//2
        if k>l: f=(2*(l+1-r)*(l+2-r),2*(r+1)*(l-r+1),(r+1)*(r+2))[s+1]
        if k==l: f=(2*(l-r+1),d,-(r+1))[s+1]
        if k<l: f=(2,-2,1)[s+1]
        A[s][labels.index((l,a,d)),labels.index((k,b,d+2*s))]=p*f


kron=np.kron
B={(s,t):A[s]@A[t] for s in A for t in A}
T=sum(kron(x,x) for x in A.values())
O=sum(s*t*kron(x,x) for (s,t),x in B.items())
for s in (-1,0):
 for t in (0,1):
    v,w=B[s,t],B[s+1,t-1]
    O+=kron(v,w)+kron(w,v)
delta=[d-e for _,_,d in labels for _,_,e in labels]
U=V=0
for diff in set(delta):
    idx=[i for i,d in enumerate(delta) if d==diff]
    idx=np.ix_(idx,idx)
    x,y=T[idx],O[idx]
    xp=x
    for bit in bin(N-2)[3:]:  # leading one bit already
        xp=xp@xp
        if bit=='1': xp=xp@x
    U+=(xp*y.T).sum()
    V+=(xp*(x@x).T).sum()
print(U,V,flush=True)
assert V>0 and 500000*U < -700741*V

M=[[0]*4+[F(z+k*p,4*10**6) for z,p in table] for k in (3,-1)]
cap=[F(100139,100000), F(872,1000)]
for r,c in enumerate(([7,17,-280,-185,1000],[12,0,-394,0,1000])):
    z=cap[r]
    P=[0]*13
    for i,x in enumerate(c):
        for j,y in enumerate(c):
            P[i+j+4]+=x*y
    upp=sum(p*m+abs(p)*eps for p,m in zip(P,M[r]))
    for s in (-1,1):
        tay=[sum(comb(i,j)*p*s**i*z**(i-j) for i,p in enumerate(P) if i>=j) for j in range(13)]
        assert tay[0]>upp and min(tay[1:])>=0

up=[m[12]+eps for m in M]
def capped(n,r,z):
    return (up[r]//z**12)*z**n+(up[r]%z**12)**(n//12)
def non(n): return 3*capped(n,1,cap[1])

lo=F(999,1000)
assert capped(72,0,lo)+non(72)<1 and up[0]>lo**12

def tail(n): return non(n)+(up[0]-lo**12)**(n//12)
p=1-(1+tail(36)/lo**36)**-2
q=1-(cap[0]**72+tail(72))**-2
def f(x):
    assert 0<=x<1
    return x*x/(2*(1-x)**2)
def rnd(x): return -(-x*10**7//1)*F(1,10**7)
for j in range(6):
    assert 0<=p<1 and 0<=q<1
    p=rnd(f(1-(1-p)**2*(1-q)))
    assert p<1
    q=rnd(f(1-(1-q)**2*(1-p)))
    print(p,q)
assert max(p,q)<F(1,100)
