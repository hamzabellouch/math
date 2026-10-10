from functools import lru_cache
from math import comb, factorial, isqrt
from itertools import combinations_with_replacement
import sympy as sy
from sympy.polys.rings import ring
from sympy.polys.domains import QQ
from sympy.polys.matrices import DomainMatrix
import numpy as np

R,h,x2,x3,x4,x5,x6,l,r,s,t=ring('h,x2,x3,x4,x5,x6,l,r,s,t',QQ)
one=R.one
base=(h,x2,x3,x4,x5,x6)
inv=(l,r,s,t)
gens=base+inv
wt=dict(zip(gens,(1,2,3,4,5,6,1,1,2,3)))
@lru_cache(None)
def mons(n,gs):
    if n==0: return (one,)
    if n<0 or not gs: return ()
    g=gs[-1]; d=wt[g]
    return tuple(g**i*m for i in range(n//d+1) for m in mons(n-d*i,gs[:-1]))

c=2*h-l
hb=l-h
S=(one,r,s,t)
p=[3*one]
for i in range(1,11):
    p.append(sum((-1)**(j+1)*S[j]*(p[i-j] if i!=j else i)
                 for j in range(1,min(3,i)+1)))
D=[R.zero]+[(1-(-1)**i)*c**(i-1)-sum(comb(i,j)*p[j]*(-1)**(i-j)
            *sum(h**k*hb**(i-j-1-k) for k in range(i-j)) for j in range(i))
            for i in range(1,11)]
dg=dict(zip(base,[one]+D[2:7]))
@lru_cache(None)
def delta(m):
    if m==one: return R.zero
    ex=next(iter(m)) # m a base monomial
    g=base[next(i for i,a in enumerate(ex) if a)]
    n=m.quo(g)
    return dg[g]*n+(g-c*dg[g])*delta(n)

q=[sum(comb(i,j)*p[j]*(-h)**(i-j) for j in range(i+1)) for i in range(10)]
beta=[0,QQ(1,2),-QQ(1,12),0,QQ(1,720),0,-QQ(1,30240),0,QQ(1,1209600),0]
td=[one]
for i in range(1,10):
    td.append(QQ(1,i)*sum(beta[j]*q[j]*td[i-j] for j in range(1,i+1)))
def rows():
    for i in range(11):
        for m in mons(i,base):
            if i<=6:
                for w in mons(9-i,inv): yield w*(m-h*delta(m))
                for w in mons(10-i,inv): yield w*delta(m)
            else:
                for w in mons(9-i,gens): yield w*m
                for w in mons(10-i,gens): yield w*delta(m)
        if i>=7:
            for w in mons(10-i,gens): yield w*D[i]
        if 4<=i<=9:
            v=sum(QQ((-1)**j,factorial(j))*q[j]*td[i-j] for j in range(i+1))
            for w in mons(9-i,base):
                yield w*td[i]
                yield w*v

M=mons(6,base)
G=mons(3,inv)+mons(4,inv)
J=[0,1,2,4,5,6,7,8,9,10,12,13,15,16,17]
C=[(i,(j,)) for i in range(len(M)) for j in J if j<=6 or M[i].degree(h)>0]
inds={next(iter(m)):i for i,m in enumerate(mons(9,gens))}
def mat(polys):
    data=[{inds[m]:v for m,v in f.items()} for f in polys if f]
    return DomainMatrix(dict(enumerate(data)),(len(data),len(inds)),QQ)
def make():
    A=mat(rows())
    assert A.shape==(1785,581)
    KD=A.nullspace(divide_last=True).transpose()
    assert (A*KD).to_Matrix().is_zero_matrix
    K=KD.to_Matrix()
    assert ker(red(A.to_Matrix())).shape==(581,65)
    assert ker(red(K)).shape==(65,0)
    P=mat(M[i].quo(h**(0 if j<=6 else 1))*G[j] for i,(j,) in C).to_Matrix()*K
    N=sy.Matrix.hstack(*P.T.nullspace()).T.rref()[0]
    assert ker(red(P)).shape==(65,5)
    assert ker(red(N)).shape==(129,60)
    assert K.shape==(581,65) and N.shape==(69,129) and (N*P).is_zero_matrix
    return N

prime=10007
assert all(prime % k for k in range(2,isqrt(prime)+1))
assert 6820*(prime-1)**2 < 2**63-1
def ker(A): # columns give kernel mod prime
    B=A%prime
    m,n=B.shape
    piv=[]
    for j in range(n):
        i=len(piv)
        nz=np.flatnonzero(B[i:,j])
        if not len(nz): continue
        u=(B[i+nz[0],:] * pow(int(B[i+nz[0],j]),-1,prime))%prime
        B[i+nz[0],:]=B[i,:]
        B=(B-B[:,j:j+1]*u)%prime
        B[i,:]=u
        piv.append(j)
        if i+1==m: break
    free=[j for j in range(n) if j not in piv]
    K=np.zeros((n,len(free)),dtype=np.int64)
    K[piv,:]=-B[:len(piv),free]
    K[free,:]=np.eye(len(free),dtype=np.int64)
    return K%prime
def grow(K,C):
    # merge slice restrictions along J
    ix={}
    n=0
    Z=np.empty((0,0),dtype=np.int64)
    for j in J:
        cc=[(i,tuple(sorted(z+(j,)))) for i,z in C]
        overlap=[k for k,a in enumerate(cc) if a in ix]
        extra=[k for k,a in enumerate(cc) if a not in ix]
        A=np.hstack((Z[[ix[cc[k]] for k in overlap],:],-K[overlap,:]))
        V=ker(A); b=Z.shape[1]
        Z=np.vstack((Z@V[:b,:] % prime, K[extra,:]@V[b:,:] % prime))
        for k in extra:
            ix[cc[k]]=n
            n+=1
    return Z,sorted(ix,key=ix.get)
def red(M):
    fun=lambda a: int(a.p)*pow(int(a.q),-1,prime)%prime
    return np.array([[fun(v) for v in row] for row in M.tolist()],dtype=np.int64)
def modN(N):
    Nmod=red(N)
    K=ker(Nmod)
    c=C
    for shape in [(1140,163),(6820,6)]:
        K,c=grow(K,c)
        assert K.shape==shape
        assert len(c)==len(set(c))==shape[0]
    lookup={a:i for i,a in enumerate(c)}
    for pair in combinations_with_replacement(J,2):
        rows=[lookup[(i,tuple(sorted(z+pair)))] for i,z in C]
        assert not np.any((Nmod@K[rows,:]) % prime)

def samples(N):
    G1=(1,4,16,64,6,24,4,3,12,48,192,768,17,68,272,96,9,36)
    G2=tuple(sy.Rational(i,3) for i in
             (3,8,21,54,9,24,6,14,37,97,252,648,37,97,252,96,16,42))
    def X(a): return (1,7-sy.Rational(2,5)*a,45-4*a,275-30*a,11,65-2*a,85,17,95-2*a,25,35)
    X2=(1,sy.Rational(11,5),5,11,-1,-1,10,-3,-1,0,14)
    products=[(X(0),G1),(X(1),G1),(X2,G2)]
    for x,y in products:
        assert not any(N*sy.Matrix([x[i]*y[j] for i,(j,) in C]))
    Z={(5,(15,15,15)):[3,0,0], (7,(15,15,15)):[1,0,0], (9,(15,15,15)):[-5,0,0],
       (7,(10,10,15)):[0,2,0], (7,(10,10,10)):[0,4,1], (9,(10,10,10)):[0,25,0]}
    for k in combinations_with_replacement(J,2):
        assert not any(N*sy.Matrix([Z.get((i,tuple(sorted(z+k))),[0,0,0]) for i,z in C]))
    def six_entries(i,z):
        return [x[i]*sy.prod(y[j] for j in z) for x,y in products]+Z.get((i,z),[0,0,0])
    selected=[(0,(0,0,0)),(0,(0,0,1)),(1,(0,0,0)),
              (5,(15,15,15)),(7,(10,10,15)),(7,(10,10,10))]
    assert sy.Matrix([six_entries(i,z) for i,z in selected]).det()==-sy.Rational(16,5)
    v0=six_entries(0,(0,0,0))
    v1=six_entries(0,(0,0,1))
    v2=six_entries(0,(0,1,1))
    assert all(32*a-20*b+3*c==0 for a,b,c in zip(v0,v1,v2))

if __name__=='__main__':
    N=make(); print("N done", flush=True)
    modN(N); samples(N)
    print("pass")
