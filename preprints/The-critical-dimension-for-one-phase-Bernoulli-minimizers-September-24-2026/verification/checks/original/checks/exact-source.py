from collections import namedtuple,Counter,defaultdict
from functools import lru_cache
import itertools
cache=lru_cache(None)
P,L,X,Y=-1,-2,-3,-4
m=5
class Term(namedtuple('Term','r g w z sig e')):
 __slots__=()
 def types(t):
    l=Counter(i for edge in t.e for i in edge[:2])
    return [sum(t.sig)+sum(k for i,j,k in t.e),l[P],l[L], bool(l[X])+bool(l[Y])]
 def degrees(t):
    return t.types()[0], t.types()[1]+t.g
@cache
def canonical(t):
 '''coeff, term'''
 if any(i==j and k==0 and i in (X,Y) for i,j,k in t.e) or 1 in t.sig:
    return 0,None
 def edges(e):
    return tuple(sorted((min(i,j),max(i,j),k) for i,j,k in e))
 e=edges(t.e)
 for p in e:
    if p[0]==Y:
        f={Y:X,X:Y}
        e=max(e,edges([(f.get(i,i),f.get(j,j),k) for i,j,k in e]))
        break
 factor=m**t.sig.count(0)
 return factor,t._replace(sig=tuple(sorted(i for i in t.sig if i>=3)),e=e)
def make(r,*e,g=0,w=0,z=0,sig=()):
 fac,t=canonical(Term(r,g,w,z,sig,e))
 assert fac==1
 return t
I=make(0);met=make(2,(0,1,0))
def Ak(k):
 return make(2,(0,1,k))
A=Ak(1)
def vec(i):
 return make(1,(i,0,0))
p,l=[vec(i) for i in (P,L)]
b=make(3,*[(i,X,0) for i in range(3)])
q=make(1,(0,X,0),(X,X,1))
g=make(0,g=1)
w=make(0,w=1)
z=make(0,z=1)
@cache
def times(t,h):
 # tensor product, distinguishing two three-tensor copies
 if any(X in edge[:2] for edge in t.e):
    assert not (any(Y in edge[:2] for edge in t.e) and any(X in edge[:2] for edge in h.e)), (t,h)
    assert not any(Y in edge[:2] for edge in h.e)
    def f(i):
        return i+t.r if i>=0 else (Y if i==X else i)
 else:
    def f(i):
        return i+t.r if i>=0 else i
 fac,t=canonical(Term(t.r+h.r,t.g+h.g,t.w+h.w,t.z+h.z,t.sig+h.sig,t.e+tuple((f(i),f(j),k) for i,j,k in h.e)))
 assert fac==1
 return t
def remove(e,*ids):
 return tuple(p for l,p in enumerate(e) if l not in ids)
@cache
def contract(t,i,j):
 assert i!=j and min(i,j)>=0 and max(i,j)<t.r
 pos={}
 for z,(a,b,k) in enumerate(t.e):
    if a>=0:pos[a]=(b,k,z)
    if b>=0:pos[b]=(a,k,z)
 a,k,u=pos[i]
 b,l,v=pos[j]
 def f(c):
    return c-(c>i)-(c>j)
 sig=t.sig
 if u==v:
    e=remove(t.e,u)
    sig=sig+(k,)
 else:
    e=remove(t.e,u,v)+((a,b,k+l),)
 h=t._replace(sig=sig,r=t.r-2,e=tuple((f(i),f(j),k) for i,j,k in e))
 return canonical(h)
@cache
def _dot(t,n,i,j,pos):
 # contract matched intervals from right to left
 if pos==n:return 1,t
 a,t=contract(t,i+n-1-pos,j+n-1-pos)
 if a==0:return 0,None
 b,t=_dot(t,n,i,j-1,pos+1)
 return a*b,t
@cache
def dot(t,h,n,i=0,j=0):
 return _dot(times(t,h),n,i,j+t.r,0)
@cache
def inner(t,h):
 return dot(t,h,t.r)
def dA(t):
 # iterate
 assert t.types()[-1]==0
 f=t.r
 c=t._replace(r=f+1,e=t.e+((X,f,0),))
 for idx,(i,j,k) in enumerate(t.e):
    e=remove(c.e,idx)
    for h in range(k):
        yield 1,c._replace(e=e+((i,X,h),(j,X,k-1-h)))
 for idx,k in enumerate(c.sig):
    yield k,c._replace(sig=remove(c.sig,idx),e=c.e+((X,X,k-1),))
 d=t.degrees()[0]
 if d:yield -d,times(t,q)
def dp(t):
 f=t.r
 c=t._replace(r=f+1)
 for l2,(i,j,k) in enumerate(c.e):
    if P not in (i,j):continue
    h=i+j-P
    s=2 if i==j else 1
    base=remove(c.e,l2)
    yield s,c._replace(w=t.w+1,e=base+((h,f,k+1),))
    yield -s,c._replace(g=t.g+1,z=t.z+1,e=base+((h,f,k),))
 if t.g:
    yield t.g,c._replace(g=t.g-1,z=t.z+1,e=c.e+((f,P,0),))
@cache
def grad(t):
 # derivative slot last
 assert not t.w and not t.z
 res=defaultdict(int)
 for c,h in itertools.chain(dA(t),dp(t)):
    fc,h=canonical(h)
    if fc:res[h]+=fc*c
 return tuple((c,h) for h,c in res.items() if c)
class Poly(dict):
 def __init__(s,t=None,c=None,items=None):
    super().__init__()
    if t is not None:s[t]=c if c is not None else 1
    if items is not None:
        for c,h in items:
            if c:s[h]=s.get(h,0)+c
 def add(s,h):
    iterable=((c,t) for poly in (s,h) for t,c in poly.items() if c)
    return Poly(items=iterable)
 def scale(s,c):
    return Poly(items=((c*v,t) for t,v in s.items()))
 def reduce(s,f):
    items=[]
    for t,c in s.items():
        v,t=f(t)
        if v:items.append((v*c,t))
    return Poly(items=items)
 def op(s,h,f):
    if isinstance(h,Term):h=Poly(h)
    items=[]
    for t,c in s.items():
        for g,d in h.items():
            v,u=f(t,g)
            if v:items.append((v*c*d,u))
    return Poly(items=items)
 def dot(s,h,*args):return s.op(h,inner if not args else lambda t,g:dot(t,g,*args))
 def times(s,h):return s.op(h,lambda t,g:(1,times(t,g)))
def polys(key,t,a):
 # compute pair Poly interior and boundary from normalized multiplier term
 # boundary p normal, g=0, H=-pAp
 H=Poly(make(0,(P,P,1)),-1); z2=z._replace(z=2)
 u=Poly(t);Du=Poly(items=grad(t))
 if key=='f':
    c=Fraction((m-1)**2,4)
    Div=u.times(z2).scale(-c).add(u.times(make(0,(L,L,0))))
    lq=Du.add(u.times(q).scale(2*a)).dot(l)
    return Div.add(lq.scale(-1)),H.times(t) if not t.g else Poly()
 if key=='U':
    Af=u.dot(A)
    Div=Af.times(z2).scale(m)
    Div=Div.add(Du.add(u.times(q).scale(2*a-1)).dot(b))
    bnd=H.times(Af).add(u.dot(Ak(2))).scale(-1).add(u.dot(times(p,p)))
    return Div,bnd if not t.g else Poly()
 first=key=='M'
 fac=w if first else z
 Div=Du.reduce(lambda t:contract(t,0,1)).times(fac)
 Div=Div.add(u.dot(q).times(fac).scale(2*a+first))
 return Div,u.dot(p) if first and not t.g else Poly()
from fractions import Fraction
def sdeg(alpha):return sum(alpha)
def plus(a,b):return tuple(i+j for i,j in zip(a,b))
def base0():return (0,)*(m-1)
def units():return tuple(tuple(int(i==j) for i in range(m-1)) for j in range(m-1))
class SPoly(Poly):
 def add(s,h):return SPoly(items=((c,t) for pol in (s,h) for t,c in pol.items()))
 def scale(s,c):return SPoly(items=((c*v,t) for t,v in s.items()))
 def __mul__(s,h):
    return SPoly(items=((v*y,plus(a,b)) for a,v in s.items() for b,y in h.items()))
one=lambda:SPoly(base0())
@cache
def mul_sum(k):
 if k==0:return one()
 us=SPoly(items=((1,u) for u in units()))
 return mul_sum(k-1)*us
def powmon(u,k):return tuple(k*j for j in u)
@cache
def sigma(k):
 if k==0:return one().scale(m)
 return mul_sum(k).scale((-1)**k).add(SPoly(items=((1,powmon(u,k)) for u in units())))
@cache
def Rp(k):
 if k==0:return one()
 return Rp(k-1)*sigma(2)
@cache
def coef(t):
 # boundary substitution as polynomial in four variables
 assert t.r==0 and not (t.g or t.w or t.z)
 deg=0
 for i,j,k in t.e:
    assert i==j==P
    deg+=k
 s=mul_sum(deg).scale((-1)**deg)
 for k in t.sig:s=s*sigma(k)
 return s
@cache
def hom_monom(u,d):
 k=sdeg(u); dif=d-k
 if dif<0: raise ValueError(d,k)
 s=Rp(dif//2)
 return SPoly(items=((c,tuple(sorted(plus(u,key)))) for key,c in s.items()))
def symhom(s,d):
 return SPoly(items=((c*v,u) for t,c in s.items() if c for u,v in hom_monom(t,d).items()))
def lc(pairs):
 return Poly(items=((d*c,t) for d,u in pairs for t,c in u.items()))
def perm(t,indices):
 def f(i): return indices[i] if 0<=i<len(indices) else i
 return canonical(t._replace(e=tuple((f(i),f(j),k) for i,j,k in t.e)))
def perm_poly(u,indices):return u.reduce(lambda t:perm(t,indices))
def tr_poly(u):return u.reduce(lambda t:contract(t,0,1))
def permutations(r):
 return tuple(itertools.permutations(range(r)))
def even(t):
 return (-1)**len([(a,b) for j,a in enumerate(t) for b in t[j+1:] if a>b])
@cache
def project(r,kind,n,t):
 u=Poly(t)
 def mulhook(v):
    # place 2 -> indices; T=(0,1)c; δ_{02} T_1 etc swap 1 2
    return lc([(-1,perm_poly(v,(0,2,1))),(-1,perm_poly(v,(2,1,0))),(2,v)])
 perms=permutations(r)
 S=lc((even(p) if kind=='anti' else 1,perm_poly(u,p)) for p in perms)
 if kind=='anti':return Poly(items=((c,t) for t,c in S.items()))
 if kind=='hook':S=lc([(3,u),(3,perm_poly(u,(1,0,2))),(-1,S)])
 terms=[({(3,'hook'):2*(n-1),(3,'sym'):n+2,(2,'sym'):n}[(r,kind)],S)]
 delta=Poly(met).times(tr_poly(S))
 if r==2:T=delta
 elif kind=='hook':T=mulhook(delta)
 else:T=lc([(1,delta),(1,perm_poly(delta,(0,2,1))),(1,perm_poly(delta,(2,1,0)))])
 return Poly(items=((c,t) for t,c in lc(terms+[(-1,T)]).items()))
def boundarypol(pol,d):
 full=SPoly(items=((c*s,h) for t,c in pol.items() if c for h,s in coef(t).items()))
 return symhom(full,d)
def Kpol(t,a):
 u=Poly(t);Ku=u.add(perm_poly(u,(1,0)).scale(-1))
 E=Ku.dot(b,3,1)
 h=Poly(times(met,A))
 R0=perm_poly(h,(0,2,1,3)).add(perm_poly(h,(0,3,1,2)))
 V1=Ku.dot(R0).times(times(z,z))
 D=Poly(items=grad(t));D=D.add(perm_poly(D,(1,0)).scale(-1)).reduce(lambda t:contract(t,0,4))
 V2=D.dot(b)
 V3=E.dot(q).scale(2*a-1)
 lam=Poly(make(0,(P,P,1)))
 h=Poly(p).times(lam.times(A).add(Poly(Ak(2),-1)))
 B0=h.add(perm_poly(h,(1,0,2))).add(perm_poly(h,(2,1,0))).add(Poly(times(times(p,p),p)))
 S=Poly() if t.g else Ku.dot(Poly(p).times(B0))
 return lc([(1,s) for s in (V1,V2,V3)]),S

def decode(r,s):
 u=list(map(int,s))
 if r<0:
    assert len(u)==4
    return tuple(u)
 assert len(u)%3==0
 h,sig,j=u[:3]
 back={5:P,6:L,7:X,8:Y}
 edges=tuple((back.get(a,a),back.get(b,b),k) for a,b,k in zip(u[3::3],u[4::3],u[5::3]))
 return Term(r,h,int(j==1),int(j==2),(3,)*sig,edges)
def readV(table):
 for line in table.splitlines():
    if not line.strip():continue
    k,term,c=line.split()
    r={'K':4,'f':0,'U':2,'P':1,'M':1}[k]
    yield k,decode(r,term),int(c)
def readB(table):
 rows=[];name=None
 for line in table.splitlines():
    if not line.strip():continue
    s=line.split()
    if s[0]=='@':
        if rows:yield name,rows
        r=int(s[1]);name=r,s[2],s[3];rows=[]
    else:
        rows.append((decode(r,s[0]),tuple(map(int,s[1:]))))
 if rows:yield name,rows

Chi=Poly(I).add(Poly(times(g,g),-1)).add(Poly(make(0,(P,P,0)),-1))

Modules={'I':Poly(I),'B':Chi}
def gram(desc,t,u,d):
 r,kind,mode=desc
 if r<0:
    s=SPoly(plus(t,u))
    if mode=='H':s=s*mul_sum(1)
    return symhom(s,d)
 proj=Poly(u) if kind=='none' else project(r,kind,m,u)
 return Poly(t).dot(proj).times(Modules[mode])
def accumulate(data,pol,scale):
 for t,val in pol.items():
    if val:data[t]+=val*scale
def evaluate(Vtable,Gtable,qv,den,n=m,d=5,a=Fraction(14,25)):
 # projection sums minus target before adding diagonal allowances
 rhs=[defaultdict(int) for ix in range(2)]
 left=[defaultdict(int) for ix in range(2)]
 for desc,rows in readB(Gtable):
    ix=int(desc[0]<0)
    for i,(t,v) in enumerate(rows):
       for j,(s,h) in enumerate(rows[:i+1]):
          assert len(h)==len(v)
          c=(1 if i==j else 2)*sum(x*y for x,y in zip(h,v))
          if c:accumulate(rhs[ix],gram(desc,t,s,d),c)
 for k,t,c in readV(Vtable):
    G,H=Kpol(t,a) if k=='K' else polys(k,t,a)
    accumulate(left[0],G,c);accumulate(left[1],boundarypol(H,d),c)
 out=[{} for ix in range(2)]
 for ix in range(2):
    rt=rhs[ix];lt=left[ix]
    for t in set(rt)|set(lt):
       val=Fraction(rt[t],den**2)-Fraction(lt[t],qv)
       if val:out[ix][t]=val
 return out
from math import isqrt
def upperroot(x,D=100000):
 s=Fraction(x)*D*D
 n=isqrt(int(s))
 return Fraction(n+(n*n<s),D)
@cache
def bound2(t):
 pdeg=t.types()[1]
 ar=Fraction(m-1,m)
 nlinear=t.types()
 kinds=[0]*t.w+[1]*t.z+[2]*nlinear[2]+[3]*nlinear[3]
 i,j=sorted(kinds)
 c=Fraction(1)
 h=t.g
 if h and pdeg:c*=Fraction(h,h+pdeg)**h*Fraction(pdeg,pdeg+h)**pdeg
 for k in t.sig:c*=Fraction((m-2)**2,m*(m-1)) if k==3 else ar**(k-2)
 for a,b1,k in t.e:
    if a==b1 and a in (X,Y):c*=Fraction(m,m+2) if k==1 else ar**(k-1)
    else:c*=ar**k
 return i,j,upperroot(c)
def magnitudes(out,dg,db,d=5,D=10**7):
 E,H=map(defaultdict_from,out)
 for val,t in zip(dg,[w,z,l,b]):
    fc,t=inner(t,t);E[t]+=fc*val
 accumulate(H,symhom(one(),d),db)
 N=[[Fraction(0) for j in range(4)] for i in range(4)]
 for t,c in E.items():
    if not c:continue
    i,j,mul=bound2(t)
    N[i][j]+=mul*abs(c)/(1+(i!=j))
    N[j][i]=N[i][j]
 berr=sum(map(abs,H.values()))
 return berr,N
def defaultdict_from(pol):
 return defaultdict(Fraction,pol)
def check_table_term(t,r):
 assert t.r==r and r<=4 and t.g>=0 and t.w+t.z<=1
 c=Counter(i for u in t.e for i in u[:2])
 assert not any((j<0 and j not in (P,L,X,Y)) or j>=r for j in c)
 assert all(c[j]==1 for j in range(r))
 nx=bool(c[X])+bool(c[Y])
 assert c[X] in (0,3) and c[Y]==0
 return t.w+t.z+c[L]+nx
def shapes(Vtable,Gtable):
 for k,t,c in readV(Vtable):
    assert check_table_term(t,t.r)==0
    if k=='P':assert t.g>0
 for d,rows in readB(Gtable):
    r,kind,mode=d
    if r==-1:
       assert mode in ('I','H') and kind=='none'
       assert all(sum(t)<=2 for t,h in rows)
    else:
       assert r>=0 and (kind in ('none','anti') or (r,kind) in [(2,'sym'),(3,'sym'),(3,'hook')])
       assert mode in Modules
       for t,h in rows:
           assert check_table_term(t,r)==int(mode in ('I','B'))

def verify(Vtable,Gtable):
 shapes(Vtable,Gtable)
 dg=list(map(Fraction,('2/25','2/25','1/4','1')))
 db=Fraction(1,4)
 out=evaluate(Vtable,Gtable,250000,250000,a=Fraction('29/50'))
 be,N=magnitudes(out,dg,db)
 U=[[2571, 773, 2358, 3087], [773, 2157, 926, 1002], [2358, 926, 4845, 4948], [3087, 1002, 4948, 8037]]
 nu=[2484, 1440, 996, 304]
 assert be*100000<=2651<100000*db
 assert all(all(x*100000<=y for x,y in zip(r,s))
     and sum(y*h for y,h in zip(s,nu))<100000*d*v
     for r,s,d,v in zip(N,U,dg,nu))
