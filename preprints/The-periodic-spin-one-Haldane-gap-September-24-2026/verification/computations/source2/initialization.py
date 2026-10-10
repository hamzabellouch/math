from fractions import Fraction as F

eps=F(1,100000)
def sectors(z,p,c):
    n=(z-p)/4
    i=(z+3*p+8*c)/12
    o=i-c
    return i,o,n
centers=[[8945303,346734,939987],[3741281,567167,984108],[2327547,721090,1002613]]
I,O,N=zip(*(sectors(*(F(x,10**6) for x in row)) for row in centers))
U=F(100245,100000); V=F(88643,100000)
mi=F(1042655,10**6); mo=F(40041,10**6); mn=F(401625,10**6)
assert all(S[-1]+eps < m for S,m in ((I,mi),(O,mo),(N,mn)))
assert U**10<mi<2*U**10 and V**10<mn<2*V**10
def filt(moments,a,b,v):
    h=sum(w*m for w,m in zip((a*a,2*a*b,b*b),moments))+eps*(abs(a)+abs(b))**2
    assert b>0 and a+b*v*v>0 and h< v**6*(a+b*v**2)**2
filt(I,-2,10,U)
filt(N,-25,100,V)
def bounds(k):
    ib=U**k+(mi-U**10)**(k//10)
    ob=mo**(k//10)
    nb=V**k+(mn-V**10)**(k//10)
    return ib+2*ob+3*nb,ib+2*ob
m,p=bounds(30)
q,_=bounds(120)
D=F(1450,1000); E=F(1202,1000)
T=F(1225,1000); T0=F(1264,1000); Rq=F(684,10000)
assert m**5<D**2 and p**5<E**2
assert (D+3*E)/4<=T0 and (D+11*E)/12<=T
assert q>=1 and (q-1)**5<Rq**2
assert D*F('.88')**3<1 and 2*F('.88')>D
def R(t):
    return max(x*x+y*y/F(2)+(D-t-x-y)**2/F(3)
               for x,y in [(0,0),(T-t,0),(T-t,T0-T),(0,T0-t)])
for a,b in ((F('.88'),F('.99')),(F('.99'),F('.998'))):
    assert b**4+R(a)**2<1
assert (1+R(b)/b**2)**(-2)>F(7,8) and (1+Rq)**(-2)>F(7,8)
