# Python 3.8+, no approximate arithmetic
from math import comb,factorial,isqrt
from fractions import Fraction

# bivariate power coefficients (m,x)
class Poly(dict):
    def __init__(self,d):
        if isinstance(d,dict): super().__init__((k,v) for k,v in d.items() if v)
        else: super().__init__({(0,0):d} if d else {})
    def __add__(p,q):
        d=dict(p)
        for k,v in Poly(q).items(): d[k]=d.get(k,0)+v
        return Poly(d)
    __radd__=__add__
    def __mul__(p,q):
        d={}
        for (i,j),v in p.items():
            for (k,l),w in Poly(q).items():
                ij=(i+k,j+l)
                d[ij]=d.get(ij,0)+v*w
        return Poly(d)
    __rmul__=__mul__
    def __neg__(p): return p*(-1)
    def __sub__(p,q): return p+(-Poly(q))
    def __rsub__(p,q): return (-p)+q

m=Poly({(1,0):1}); x=Poly({(0,1):1}); D=10**8
def make(row,group,s0,s1):
    L,U,V,alpha,lam,mu=group
    P=Poly(D); a=Poly(1); b=m
    for v in row:
        P=P+v*(b-b.get((0,0),0)); a,b=b,2*m*b-a
    B=(1-m*m)*P
    E=Poly({(k-2,0):v for (k,i),v in B.items() if k>=2 and k%2==0})
    A=Poly(0); C=Poly(0)
    for (k,i),v in B.items():
        for j in range(1,k+1):
            if j%2: C=C+Poly({(k-j,j-1):comb(k,j)*v})
            else: A=A+Poly({(k-j,j-2):-comb(k,j)*v})
    def J(s): return (2*L*D)-s*C
    def W(s): return mu*J(s)*J(s)-(2*L)**2*A*(1000*B+(2*alpha-1000)*x*C+(lam-1000)*x*x*A)
    return [P,E,J(s1),W(s0),W(s1)], B

def transform(axis,A,T):
    if axis==0: return [[sum(w*q for w,q in zip(row,col)) for col in zip(*A)] for row in T]
    return [[sum(w*q for w,q in zip(row,col)) for row in T] for col in A]
def bern(p,a,b,c,d,den):
    # m=(a+b*s)/den, x=t*(c+d*s)/den, common factor den^N N! K!
    N=max(i+j for i,j in p); K=max(j for i,j in p)
    R=[[0]*(K+1) for _ in range(N+1)]
    for (i,j),v in p.items():
        for k in range(i+1):
            u=v*den**(N-i-j)*a**(i-k)*b**k*comb(i,k)
            for l in range(j+1): R[k+l][j]+=u*c**(j-l)*d**l*comb(j,l)
    for axis,n in enumerate((N,K)):
        R=transform(axis,R,[[comb(k,i)*(factorial(n)//comb(n,i)) for i in range(n+1)] for k in range(n+1)])
    return R
def split(A,axis):
    n=len(A if axis==0 else A[0])-1
    if not n: return (A,)
    T=[[comb(i,k)*2**(n-i) for k in range(n+1)] for i in range(n+1)]
    return transform(axis,A,T),transform(axis,A,[row[::-1] for row in reversed(T)])
def checkmat(A,depth):
    if all(min(row)>0 for row in A): return
    if depth==0: raise ValueError('coefficient sign')
    for B in split(A,0):
        for C in split(B,1): checkmat(C,depth-1)
def verify(p,index,depth,s1):
    ends=[(-16,0),(-14,2),(-6,6),(6,6),(14,2),(16,0)]
    if index==0: ends=[ends[0],ends[-1]]
    if index==1:
        den=2**depth; N=max(i+j for i,j in p); sc=den**N*factorial(N)*D*1000
        for i in range(den):
            R=bern(p,i,1,0,0,den)
            h=-s1*min(min(row) for row in R)
            if h>0 and (sc<=h or ((sc-h)*den)**2<=h*h*(den*den-i*i)): raise ValueError('E')
        return
    for ((a,c),(b,d)) in zip(ends,ends[1:]): checkmat(bern(p,a,b-a,c,d-c,16),depth)

# base-column check, scaled intervals
Z=10**12
class I:
    def __init__(x,a,b=None):
        x.a=a
        x.b=b if b!=None else a
    def __neg__(x): return I(-x.b,-x.a)
    def __add__(x,y):
        y=put(y); return I(x.a+y.a,x.b+y.b)
    __radd__=__add__
    def __sub__(x,y): return x+(-put(y))
    def __rsub__(x,y): return put(y)+(-x)
    def __mul__(x,y):
        y=put(y); v=[a*b for a in (x.a,x.b) for b in (y.a,y.b)]
        return I(min(v)//Z,-((-max(v))//Z))
    __rmul__=__mul__
    def inv(x):
        if x.a<=0: raise ValueError('reciprocal')
        return I(Z*Z//x.b,-((-Z*Z)//x.a))
    def __truediv__(x,y): return x*put(y).inv()
    def __pow__(x,n):
        if n<0: return (x**(-n)).inv()
        y=put(1)
        for i in range(n): y=y*x
        return y
    def root(x):
        return I(isqrt(x.a*Z),1+isqrt(x.b*Z-1) if x.b>0 else 0)
def put(x): return x if isinstance(x,I) else I(x*Z)

def base(B,group,s0,s1,bound):
    L,U,V=(I(k*(Z//1000)) for k in group[:3]); N=128
    for it in range(N):
        lo=(s0*N+(s1-s0)*it)*(Z//1000); hi=lo+(s1-s0)*(Z//1000)
        s=I(lo//N,-((-hi)//N)); s2=s*s
        d=s2/(2*(1+(1-s2).root()))
        for A in ({7},{7,6},{7,6,5}):
            m0=Fraction(len(A),4)-1; Y={u:I(0) for u in (1,-1)}
            for i in range(8):
                P=0
                for j in range(8):
                    if (i in A)!=(j in A):
                        k=bin(i^j).count('1')
                        P+=I(Z//4)*(d**(k-1))*((1-d)**(2-k))
                e=s2*P; h=2*(P*(1-e)).root(); g=s*h
                q=(1 if i in A else -1)*(1-2*e)/(1+g*(L+g*(U+g*V)))
                for u in Y: Y[u]+=h*(1+u*q)
            for u in Y:
                b=sum(v*(u*m0)**k for (k,_),v in B.items())/D
                lhs=Fraction((I(Z//8)*Y[u]).a,Z)
                if (lhs-b)*10000<bound: raise ValueError('base')

def data(s): return [list(map(int,line.split())) for line in s.strip().splitlines()]
rows=data("""
5   26797227 21421001 5128970 9234452 692060 4904060 -868991 3430822 -1620202 2642536 -1572003 1611382 -790463 573913 -196263 125941 -28650 17140
17   26545421 20782313 4702871 8733755 262302 4632398 -1223407 3219225 -1751136 2367765 -1499679 1323103 -650254 364146 -98062 32125
39   23422612 23811053 2720392 9481334 342747 3521407 293182 1243280 94220 628296 -211618 367918 -115140 71341
70   28627418 18132350 6560313 4688850 3090858 280132 2014606 -721794 1092862 -413975 251954 -30987
108   25845226 21339334 2692615 7536216 -587180 2879744 -642549 859994 -135519 99765
160   28111431 22222528 3686628 6969749 260698 2311757 -230942 626183 -39197 65219
220   31980620 22310973 3943312 6252289 221019 1801879 -204196 345834
300   37050025 22730221 6023971 4990611 1410047 1047683 133030 195650
400   46891988 25975928 8279226 5707508 1896038 1189721 225195 190389
490   57774207 30017282 10752796 6552311 2404507 1338857 310628 193643
570   67261317 34557385 13515609 7744945 3024441 1590294 428436 214704
630   76105766 38746702 15974003 8801748 3567377 1794423 517893 232715
700   92621845 50731247 23924150 14690765 6918336 4309886 1672440 1096916 239750 209175
750   100973193 55145076 26634158 15924290 7601086 4546032 1797080 1099352 246042 192495
800   114390772 63949520 33959789 20265973 11129205 6354835 3302519 1693517 778655 305292 118236
827   126357200 73807375 40646383 25693312 14417512 9123323 4734690 2955541 1274070 786030 225052 144665
840   140455073 85610577 50361189 33435466 20391097 13705759 8022488 5381807 2815510 1892888 793925 548406 137909 116217
""")
info=data("""
5         1   0   0    3    4      7
17        1   0   0    2    3      7
39        1   0   0    1    1      8
70        1   0   0    1    2     10
108       0   0   0    1    1      7
160       0   0   0    0    1     14
220       0   0   0    0    0     78
300       0   0   0    0    0     69
400       0   0   0    0    0    146
490       0   0   0    0    0    224
570       0   2   0    0    0    233
630       0   3   0    0    0    255
700       1   4   0    0    0    236
750       1   5   0    1    0    222
800       1   5   0    1    0    191
827       1   6   0    1    1    177
840       1   6   0    1    1    176
""")
groups=data("""
70 940 -440 300 960 1000 956
160 940 -440 300 930 1050 953
300 886 -398 250 860 1150 985
490 842 -335 180 770 1150 1024
630 842 -335 180 690 1150 1058
750 842 -335 180 632 1160 1087
840 842 -335 180 583 1160 1111
""")

if len(rows)!=17 or len(info)!=len(rows): raise ValueError('rows')
s0=0
for row,depth in zip(rows,info):
    s1=row[0]
    if depth[0]!=s1: raise ValueError('endpoints')
    group=next(params[1:] for params in groups if params[0]>=s1)
    polys,B=make(row[1:],group,s0,s1)
    for i,p in enumerate(polys): verify(p,i,depth[i+1],s1)
    base(B,group,s0,s1,depth[-1]); s0=s1
print("pass")
