"""Independent scalar-rational audit of the two supplied Haldane initializations.

This checks the consequences of the asserted thermal/trial inputs; it does not
recompute matrix exponentials or trial contractions.
"""
from fractions import Fraction as F
from math import comb

def out(name, value):
    print(f"{name}: {float(value):.15g}")

def checked(name, margin):
    assert margin > 0, (name, margin)
    out(name, margin)

def purity_update(u):
    assert 0 <= u < 1
    return u*u/(2*(1-u)**2)

def capped_mass(m, cap, exponent):
    assert m >= 0 and cap > 0 and exponent >= 1
    count = m // cap
    return count*cap**exponent+(m-count*cap)**exponent

def source_1():
    table = [[124885379,65757],[2925,2960742],[12870614,286599],
        [54069,1920414],[4639283,510140],[195455,1514846],
        [2654823,675419],[377629,1314544],[1900547,787405]]
    eps=F(30,10**6)
    moments=[[F(0)]*4+[F(z+k*p,4*10**6) for z,p in table] for k in (3,-1)]
    caps=[F(100139,100000),F(872,1000)]
    quartic=[7,17,-280,-185,1000]
    for sign,expected in ((1,[559,2902,5165,3815,1000]),
                          (-1,[895,3978,6275,4185,1000])):
        actual=[sum(comb(i,j)*a*sign**i for i,a in enumerate(quartic) if i>=j)
                for j in range(5)]
        assert actual==expected and min(actual)>0
    assert caps[0]>1
    assert 12-394*caps[1]**2+1000*caps[1]**4>0
    assert caps[1]**2>F(197,1000)
    for r, coefficients in enumerate(([7,17,-280,-185,1000],[12,0,-394,0,1000])):
        P=[0]*13
        for i,a in enumerate(coefficients):
            for j,b in enumerate(coefficients):
                P[i+j+4]+=a*b
        bound=sum(c*m+abs(c)*eps for c,m in zip(P,moments[r]))
        out(f"source1 filter {r} upper",bound)
        for sign in (-1,1):
            shifted=[sum(comb(i,j)*c*sign**i*caps[r]**(i-j)
                for i,c in enumerate(P) if i>=j) for j in range(13)]
            checked(f"source1 filter {r} sign {sign} margin",shifted[0]-bound)
            assert all(x>=0 for x in shifted[1:])
        print(f"source1 filter {r} coefficients: {P}")
    up=[row[12]+eps for row in moments]
    out("source1 invariant twelfth mass",up[0]);out("source1 other twelfth mass",up[1])
    def cap(n,r,z): return capped_mass(up[r],z**12,n//12)
    def non(n): return 3*cap(n,1,caps[1])
    lo=F(999,1000)
    checked("source1 dominant-existence margin",1-cap(72,0,lo)-non(72))
    checked("source1 invariant residual positive",up[0]-lo**12)
    checked("source1 invariant dominant unique",2*lo**12-up[0])
    def tail(n): return non(n)+(up[0]-lo**12)**(n//12)
    for n in (36,72):
        out(f"source1 nontrivial {n} mass",non(n));out(f"source1 tail {n}",tail(n))
    p=1-(1+tail(36)/lo**36)**-2
    q=1-(caps[0]**72+tail(72))**-2
    out("source1 initial p",p);out("source1 initial q",q)
    def ceil7(x): return F(-(-x*10**7//1),10**7)
    expected=[(F(151249,2500000),F(433453,2500000)),
        (F(343303,5000000),F(1632381,10000000)),
        (F(44601,625000),F(361773,2500000)),
        (F(632939,10000000),F(1055161,10000000)),
        (F(375793,10000000),F(445941,10000000)),
        (F(84513,10000000),F(27493,5000000))]
    for j, expected_pair in enumerate(expected,1):
        p=ceil7(purity_update(1-(1-p)**2*(1-q)))
        q=ceil7(purity_update(1-(1-q)**2*(1-p)))
        assert (p,q)==expected_pair
        print(f"source1 round {j}: p={p}; q={q}")
    checked("source1 final margin to .01",F(1,100)-max(p,q))

def source_2():
    table=[[8945303,346734,939987],[3741281,567167,984108],[2327547,721090,1002613]]
    eps=F(1,100000)
    invariant=[]; conjugate=[]; nontrivial=[]
    for z,p,c in table:
        z,p,c=(F(v,10**6) for v in (z,p,c))
        invariant.append((z+3*p+8*c)/12)
        conjugate.append((z+3*p-4*c)/12)
        nontrivial.append((z-p)/4)
    print("source2 sector centers (I,O,N):",list(zip(invariant,conjugate,nontrivial)))
    U=F(100245,100000);V=F(88643,100000)
    mi=F(1042655,10**6);mo=F(40041,10**6);mn=F(401625,10**6)
    for label,mom,m in (("I",invariant,mi),("O",conjugate,mo),("N",nontrivial,mn)):
        checked(f"source2 {label} tenth-moment margin",m-mom[-1]-eps)
    for label,m,cap in (("I",mi,U), ("N",mn,V)):
        checked(f"source2 {label} m above cap^10",m-cap**10)
        checked(f"source2 {label} m below 2cap^10",2*cap**10-m)
    for label,mom,a,b,v in (("I",invariant,-2,10,U),("N",nontrivial,-25,100,V)):
        upper=sum(c*m for c,m in zip((a*a,2*a*b,b*b),mom))+eps*(abs(a)+abs(b))**2
        assert b>0 and a+b*v*v>0
        checked(f"source2 {label} filter margin",v**6*(a+b*v*v)**2-upper)
    def bounds(k):
        ib=capped_mass(mi,U**10,k//10)
        ob=mo**(k//10)
        nb=capped_mass(mn,V**10,k//10)
        assert ib==U**k+(mi-U**10)**(k//10)
        assert nb==V**k+(mn-V**10)**(k//10)
        return ib+2*ob+3*nb,ib+2*ob
    m,p=bounds(30);q,_=bounds(120)
    out("source2 Z30 upper",m);out("source2 twisted Z30 upper",p);out("source2 Z120 upper",q)
    D=F(1450,1000);E=F(1202,1000);Ti=F(1225,1000);T0=F(1264,1000);Rq=F(684,10000)
    checked("source2 untwisted temperature-power margin",D**2-m**5)
    checked("source2 twisted temperature-power margin",E**2-p**5)
    assert (D+3*E)/4<=T0 and (D+11*E)/12<=Ti
    assert q>=1
    checked("source2 temporal tail margin",Rq**2-(q-1)**5)
    checked("source2 .88 dominance margin",1-D*F('.88')**3)
    checked("source2 dominant uniqueness margin",2*F('.88')-D)
    def R(t):
        assert t<Ti<T0<D
        return max(x*x+y*y/F(2)+(D-t-x-y)**2/F(3) for x,y in
            ((0,0),(Ti-t,0),(Ti-t,T0-Ti),(0,T0-t)))
    for t,s in ((F('.88'),F('.99')),(F('.99'),F('.998'))):
        out(f"source2 R({t})",R(t))
        checked(f"source2 dominant upgrade {t} to {s}",1-s**4-R(t)**2)
    out("source2 R(.998)",R(F('.998')))
    S=(1+R(F('.998'))/F('.998')**2)**-2
    T=(1+Rq)**-2
    out("source2 spatial purity lower",S);out("source2 temporal purity lower",T)
    checked("source2 spatial 7/8 margin",S-F(7,8));checked("source2 temporal 7/8 margin",T-F(7,8))

if __name__=='__main__':
    source_1()
    source_2()
