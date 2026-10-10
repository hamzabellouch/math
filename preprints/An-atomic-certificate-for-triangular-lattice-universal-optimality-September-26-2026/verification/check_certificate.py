# Fixed-grid outward intervals for the finite sums, endpoints over G.
import math
G=10**60
def up(a,b): return -((-a)//b)
class I:
 __slots__=('l','h')
 def __init__(s,l,h):
    assert l<=h
    s.l,s.h=l,h
 def __add__(s,t):
    if type(t) is IQ:return t+s
    if type(t) is int:
       t=t*G;return I(s.l+t,s.h+t)
    return I(s.l+t.l,s.h+t.h)
 __radd__=__add__
 def __neg__(s):return I(-s.h,-s.l)
 def __sub__(s,t):return s+(-t)
 def __rsub__(s,t):return -s+t
 def __mul__(s,t):
    if type(t) is IQ:return t*s
    a,b=s.l,s.h
    if type(t) is int:
       a*=t; b*=t;return I(min(a,b),max(a,b))
    c,d=t.l,t.h
    ac,bc,ad,bd=a*c,b*c,a*d,b*d
    return I(min(ac,bc,ad,bd)//G, up(max(ac,bc,ad,bd),G))
 __rmul__=__mul__
 def recip(s):
    a,b=s.l,s.h
    assert a*b>0
    return I(G*G//b,up(G*G,a))
 def __truediv__(s,t):
    if type(t) is int:
       if t<0:return -s/(-t)
       return I(s.l//t,up(s.h,t))
    return s*t.recip()
 def __rtruediv__(s,t):
    return s.recip()*t
 def sqrt(s):
    a=max(0,s.l)*G; b=s.h*G
    assert b>=0
    return I(math.isqrt(a), math.isqrt(b-1)+1 if b>0 else 0)
 def __pow__(s,k):
    # binary powers
    assert type(k) is int
    if k<1: return I(G,G) if k==0 else s.recip()**(-k)
    if k==1:return s
    a=s**(k//2); return (a*a)*s if k%2 else a*a
 def __abs__(s):return I(max(0,s.l,-s.h),max(s.h,-s.l))
# P(a) here brackets an input scalar; PJ below holds the P_j.
def P(a,b=None):
    if type(a) is int:
       a*=G
       if b is None:return I(a,a)
       assert b>0
       return I(a//b,up(a,b))
    if type(a) is str and b is None:
       n=a.index('.')
       u=len(a[n+1:])
       return P(int(a[:n]+a[n+1:]),10**u)
    assert b is None and type(a) is I
    return a
Z=P(0);ONE=P(1)
class IQ: # complex
 __slots__=('x','y')
 def __init__(s,x,y=Z):
    if type(x) is IQ:
       s.x=x.x; s.y=x.y
    else:
       s.x=P(x);s.y=P(y)
 def __neg__(s):return IQ(-s.x,-s.y)
 def __add__(s,t):
    if type(t) is not IQ:return IQ(s.x+t,s.y)
    return IQ(s.x+t.x,s.y+t.y)
 __radd__=__add__
 def __sub__(s,t):return s+(-t)
 def __rsub__(s,t):return (-s)+t
 def __mul__(s,t):
    if type(t) is not IQ:return IQ(s.x*t,s.y*t)
    return IQ(s.x*t.x-s.y*t.y,s.x*t.y+s.y*t.x)
 __rmul__=__mul__
 def __truediv__(s,t):
    return IQ(s.x/t,s.y/t)
 def conj(s):return IQ(s.x,-s.y)
 def __abs__(s):return (s.x*s.x+s.y*s.y).sqrt()
iQ=IQ(0,1)
def Real(x):return x.x if type(x) is IQ else P(x)
def imax(*x):
 if len(x)==1 and type(x[0]) not in (I,int):x=tuple(x[0])
 x=list(map(P,x))
 return I(max(a.l for a in x),max(a.h for a in x))
def imin(*x):
 if len(x)==1 and type(x[0]) not in (I,int):x=tuple(x[0])
 x=list(map(P,x))
 return I(min(a.l for a in x),min(a.h for a in x))
def expo(w):
 w=w/1024
 mag=abs(w)
 assert mag.h<=G
 a=IQ(ONE) if type(w) is IQ else ONE; s=a
 for j in range(1,61):
    a=w*a/j; s=s+a
 tiny=I(-1,1)
 s=s+(IQ(tiny,tiny) if type(w) is IQ else tiny)
 for j in range(10):s=s*s
 return s
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def matmul(A,B):
 cols=list(zip(*B))
 return [[dot(row,col) for col in cols] for row in A]
def evec(j,n):return [P(int(k==j)) for k in range(n)]
def getinv(A):
 n=len(A)
 M=[list(A[j])+evec(j,n) for j in range(n)]
 pivs=[]
 for i,Y in enumerate(M):
    # columns strictly left of the pivot are known unit columns
    a=Y[i];assert a.l*a.h>0,a
    pivs.append(abs(a))
    V=[u/a for u in Y[i+1:]]
    Y[i+1:]=V;Y[i]=ONE
    for k,X in enumerate(M):
       if k==i:continue
       a=X[i]
       X[i+1:]=[b-a*c for b,c in zip(X[i+1:],V)]
       X[i]=Z
 inv=[row[n:] for row in M]
 lt('.12',imin(*pivs))
 lt(imax(*pivs),'1.74')
 return inv
def norm(A):
 return imax(sum(abs(v) for v in col) for col in zip(*A))


def lt(a,b):
 assert P(a).h<P(b).l
def near(a,b,tol='.00001'):
 lt(abs(a-P(b)),tol)
pi0=P('3.14159265358979323846264338327950288419716939937510')
Pi=pi0+I(0,10**10) # 1e-50 exactly
def ar(part):
 x=P(1,part)
 return sum((-1)**j*x**(2*j+1)/(2*j+1) for j in range(41))
# 16*atan(1/5)-4*atan(1/239); total tail less than 10^-58
pit=16*ar(5)-4*ar(239)+I(-100,100)
lt(pi0,pit)
lt(pit,pi0+I(10**10,10**10))
b=P(3).sqrt()/2;B=P(4,3)
h=P('.34');H=P('.54');eta=H-h
ZM=P('.391');WM=P('.0061');EM=P('.00018');VM=P('.00048');PM=P('.0000003')
# R here is the list of residues; T below is the first period of the tail.
R=[0,1,3,4,7,9,12,13,16,19,21,25,27,28,31]
f=R[1:11];L=[0]+f
T=R[11:]+[r+36 for r in L]
jvec=list(range(16)); tv=[P(j,18) for j in jvec]
yj=Pi/36
def phase(s):return expo(iQ*(Pi/18)*s)
phase_mem={}
def ph(j):
 # integer reduce
 assert type(j) is int
 j=j%36
 if j not in phase_mem:phase_mem[j]=phase(j)
 return phase_mem[j]
def addpoly(Pa,Pb):
 return [[a+b for a,b in zip(u,v)] for u,v in zip(Pa,Pb)]
def sm(a,U):return [[a*x for x in u] for u in U]
def combine(a,A,b,B):return [[a*x+b*y for x,y in zip(u,v)] for u,v in zip(A,B)]
# P
Pfull=[IQ(1)]
for a in R:
 e=ph(a)
 temp=[IQ(0)]*(2+len(Pfull))
 for j,x in enumerate(Pfull):
    temp[j]=temp[j]-e*x
    temp[j+1]=temp[j+1]+2*x
    temp[j+2]=temp[j+2]-e.conj()*x
 Pfull=temp
PJ=Pfull[15:]
U=[p*(2 if j else 1) for j,p in enumerate(PJ)] # folded P atoms (V)
# Q,D
it=[iQ*Pi*t for t in tv]
Q={};D={}
for n in R:
 X=[p*ph(j*n) for j,p in enumerate(PJ)]
 Q[n]=Real(dot([t*t for t in it],X))
 D[n]=Real(dot([t*t*t for t in it],X))/(3*Q[n])
def q(n):return Q[n%36]
def d(n):return D[n%36]
# M low basis all L incl n=0
def makecol(j,n):
    vals=[PJ[l]*ph((l-j)*n) for l in range(j+1,16)]
    C=dot(list(range(1,len(vals)+1)),vals)*((-4*yj)*yj) if vals else IQ(0)
    A=iQ*yj*(PJ[j]+2*sum(vals))
    return [X*(2 if j else 1) for X in [C,A]]
M=[sum((makecol(j,n) for n in L),[]) for j in jvec]
Mu=[[abs(e) for e in row] for row in M]
Pmag=[abs(e) for e in U]
# high density fold variation bound columns
W=[[P(0),P(0)]]
for j in range(1,16):
    vals=[abs(e) for e in PJ[j:]]
    W.append([2*(Pi/18)**2*dot([P(2*s+1,2) for s in range(len(vals))],vals),2*Pi*sum(vals)/18])

class Waves:
 def __init__(a,k,v):
    a.k=k;a.v=v
    a.rho=[];a.lam=[];a.zeta=[]
    a.wa=[];a.lb=[];a.wb=[];a.eps=[]
    a.epsa=Pi*(k-h)
    for t in tv:
       den=k*k+t*t;X=B/den
       a.rho.append(IQ(t,k-h))
       a.lam.append(IQ(k,t)/(b*den))
       a.zeta.append(IQ(-X*t,k*X-v))
       a.wa.append(Pi*(t*t+(k-h)**2).sqrt())
       a.lb.append(X.sqrt())
       a.wb.append(Pi*(v*v+(B-2*k*v)*X).sqrt())
       a.eps.append(Pi*(k*X-v))
 def coeff(a,N,S,repeat=False):
    vals=[]
    for e,l,w in zip(a.eps,a.lb,a.wb):
       val=sum((1+abs(d(n))+w)*expo(-e*n)/q(n) for n in N)*l
       vals.append(val/(1-expo(-36*e)) if repeat else val)
    return imax(*matmul([vals],S)[0])
 def loS(a,MM):
    rows=[]
    w=[iQ*Pi*r for r in a.zeta]
    for n in f:
       b=[l*expo(x*n) for l,x in zip(a.lam,w)]
       tab=matmul([[-v for v in b],[(d(n)-r)*v for r,v in zip(w,b)]],MM)
       rows+=sm(P(1)/q(n),[[Real(v) for v in row] for row in tab]) # interval row scaled by recip
    return rows
 def curv(a,s,S):
    A=[w*w*expo(-a.epsa*s)/2 for w in a.wa]
    B=[w*w*l*expo(-e*s)/2 for w,l,e in zip(a.wb,a.lb,a.eps)]
    return [imax(*row) for row in matmul([A,B],S)]
 def terr(a,m,y,S,degr):
    N=degr+3
    def tail(w,e):
       x=w*y
       assert abs(x).h < G*(N+1)
       return w*w * (x**(N-2)) * expo(-e*m) / math.factorial(N) / (1-x/(N+1))
    y=abs(y)
    A=[tail(w,a.epsa) for w in a.wa]
    B=[tail(w,e)*l for w,l,e in zip(a.wb,a.lb,a.eps)]
    return sum(imax(*row) for row in matmul([A,B],S))
 def tayrows(a,m,y,N):
    def tab(w,l):
       x=iQ*Pi*w
       v=x*x*expo(x*m)*l/2
       vals=[v]
       for k in range(N):v=(x*y)*v/(k+3);vals.append(v)
       return vals
    return [list(zip(*[tab(w,v) for w,v in zip(ws,ls)])) for ws,ls in [(a.rho,[1]*16),(a.zeta,a.lam)]]
 def coeffpoly(a,m,y,N,F1,F2):
    A,B=a.tayrows(m,y,N)
    return [[Real(x) for x in row] for row in addpoly(matmul(A,F1),matmul(B,F2))]

Fc=Waves(h,h);Fl=Waves(H,h);Lc=Waves(h,H);Ll=Waves(H,H)

pairs=[]
for j,m in enumerate(f[:7]):
    Y1=P(-1) if j==0 else P(f[j-1]-m,2)
    pairs+=[(m,Y1),(m,P(f[j+1]-m,2))]

def envtable():
 ZetaMax=(Pi*(1/b-h)).recip()
 zs=(1+2*ZM).sqrt()-1
 lt(ZetaMax,ZM)
 for j,a in zip([2,3,6],[WM,VM,PM]):lt(expo(-j/ZM),a)
 lt((ZM-zs)*expo(-2/zs),'.00015')
 lt('.157',imin(Q.values())); lt(imax(Q.values()),40)
 lt(imax(abs(x) for x in D.values()),'2.83')
 svals=[]
 for l,r in zip(R,R[1:]+[36]):
    s=P(l+r,2)
    es=[phase(s*j) for j in jvec]
    svals.append(4*Real(dot(es,U))/((r-l)*(r-l)))
 vals='.165 .120 .054 .482 .656 1.11 .337 3.13 9.26 8.19 19.08 2.34 .706 6.80 14.1'.split()
 for x,y in zip(vals,svals):lt(x,y)
 lt(16,imin(q(n) for n in [16,19,21]))
 lt(norm(W),119)
 lt(Lc.coeff(f,W),335)
 pm=[[x] for x in Pmag]
 lt(10**8*Fc.coeff(T,W,True),'2.3')
 lt(10**7*Fc.coeff(T,pm,True),'1.27')
 lt(10**15*Fl.coeff(T,Mu,True),7)
 alias=(1+Pi*eta)*expo(-36*Pi*eta)/(1-expo(-36*Pi*eta))
 lt(10**10*alias,'2.5')
 g=q(1)*sum((ZM+1+ZM*abs(Pi*eta-d(n)))*expo(Pi*eta*n+(1-n)/ZM)/q(n) for n in f[4:])
 # far: interval floor covers tiny values by 1e-60, enough
 gt=q(1)*sum((ZM+1+ZM*abs(d(n)))*expo((1-n)/ZM)/q(n) for n in T)/(1-expo(-36/ZM))
 lt(10**8*g,'8.1'); lt(10**29*gt,'9.2')
 for i,s0 in enumerate([P(0),P(1),P(2),P('14.5'),P(23)]):
    curl=sum(Fl.curv(s0,Mu))
    curc=Fc.curv(s0,[[x] for x in Pmag])[1]
    j=0 if s0.h==0 else 15
    curt=60*(Fc.wa[-1]**2+(Fc.wb[j]**2)*Fc.lb[j]*expo(-s0*Fc.eps[j]))
    lt(curl,[1498,'45.1','13.8','.00458','.000022'][i])
    lt(curc,[13530,151,31,'.00122','.000004'][i])
    lt(curt,[26500,1160,800,800,800][i])
 for m,y in pairs:
    err=3*Fl.terr(m,y,Mu,20)+P('.006')*Fc.terr(m,y,[[x] for x in Pmag],20)
    lt(err,'.00161' if m==1 else '.0000075')

EE=[evec(i,8) for i in range(8)]
def basis(i,x=ONE):return [t*x for t in EE[i]]
def zeros(m):return [basis(0,Z) for _ in range(m)]
fixes=[[basis(1,P('.44')),basis(1,P(0)),basis(1,c)] for c in [-P('.006'),P('.006')]]
def target():
 Tmat=zeros(20)
 for j,n in enumerate(f[:4]):
    coeff=q(1)*expo(Pi*eta*n)/q(n)
    Tmat[2*j]=basis(2*j,coeff)
    Tmat[2*j+1]=[a+b for a,b in zip(basis(2*j+1,-coeff),basis(2*j,coeff*(Pi*eta-d(n))))]
 return Tmat

def approx():
 SL=Ll.loS(M);SC=Lc.loS([[x] for x in U])
 A=[row[2:] for row in SL];B0=[row[:2]+c for row,c in zip(SL,SC)]
 bb1=addpoly(target(),matmul(B0,fixes[1]))
 bb2=matmul(B0,fixes[0])
 des=[]
 E=[evec(i,len(A)) for i in range(len(A))]
 for sign in (1,-1):
    v=getinv(combine(1,E,-sign,A))
    lt(norm(v),'16.16' if sign==1 else '3.89')
    des.append(matmul(v,combine(1,bb1,sign,bb2)))
 return [fixes[i][:2]+combine(P(1,2),des[0],s*P(1,2),des[1])+fixes[i][2:] for i,s in enumerate([1,-1])]

def approxnorm(X):
 R=list(zip(*X))
 ns=[sum(abs(v) for v in col) for col in R]
 comb=imax(sum(abs(a*z+b) for a,b in zip(*R[:2])) for z in [Z,ZM])
 val=comb+dot(ns[2:],[P('.0024'),WM,VM*ZM,VM,PM,PM])
 return val

def bern(X):
 N=len(X)-1
 return matmul([[P(math.comb(j,r),math.comb(N,r)) for r in range(N+1)] for j in range(N+1)],X)

def vmin(row):
 u,x,a,g,c,v,p,r=row
 return x+ZM*imin(0,u)+EM*imin(0,-a)+WM*imin(0,g+ZM*a)+VM*imin(0,v,v+ZM*c)+PM*(imin(0,p)+imin(0,r))
def test(X):return imin(vmin(row) for row in bern(X))

def powsol(Xs,N=20):
 Fs=[matmul(M,X[:-1]) for X in Xs]
 Cs=[matmul([[u] for u in U],X[-1:]) for X in Xs]
 for m,y in pairs:
    H=[addpoly(Fl.coeffpoly(m,y,N,Fs[i],Fs[1-i]),Fc.coeffpoly(m,y,N,Cs[i],Cs[1-i])) for i in [0,1]]
    X=H[0]
    V=test(H[1])
    lower=['.174' if y.h<0 else '.011','.00097','.00097','.0028','.0039','.0020','.0020']
    pos=f.index(m)
    lt(lower[pos],V)
    neg=sm(-1,X)
    if m==1 and y.l>0:
       def sub(z):
          return [[Z,b+a*z,*rest] for a,b,*rest in neg]
       a0=sub(Z);d0=sub(ZM)
       def sh(Arr,k):
          return zeros(k)+Arr+zeros(2-k)
       def B(Arr,j):
          X2=sh(Arr,2)
          if j==0:return X2
          X2=combine(1,X2,(2*j)*ZM,sh(Arr,1))
          if j==2:X2=combine(1,X2,6*ZM**2,sh(Arr,0))
          return X2
       J=[sh(a0,1),combine(P(2,3),B(a0,1),P(1,3),B(d0,0)),combine(P(1,3),B(a0,2),P(2,3),B(d0,1)),B(d0,2)]
       for j,A in enumerate(J):
          A[0][1]+=q(1)*(j*ZM if j else ONE)
          if j:A[1][1]+=q(1)
       for x,v in zip(['.046','.056','.024','.027'],map(test,J)):lt(x,v)
       vals='-.04466 .02932 -.26629 .24478 .31068 .13285 .01134 -.00831'.split()
       for x,v in zip(bern(H[1])[20],vals):near(x,v,'.00002')
       continue
    if m==1:neg[0][1]+=q(1)/(2*ZM)
    if m==3:neg[0][3]+=P('.8')*q(1)
    lt(['.057','.00055','.00047','.0028','.0039','.0020','.0020'][pos],test(neg))

envtable()
data=approx()
for x,v in zip(data,['2.58','2.80']):lt(approxnorm(x),v)
near(q(1),'.32468'); near(d(1),'.32851')
for x,vals in zip(data,[['2.33481','-.50286'],['-.34812','-.31862']]):
 for a,e in zip(x[2][:2],vals):near(a,e,'.00002')
powsol(data)
