import sympy as S
vs=S.symbols('s t u v')
pol=lambda a:S.Poly(a,*vs,domain=S.ZZ)
s,t,u,v=map(pol,vs)
def probs(s,t): return [6*s+3*t+2,3*t+2,pol(2)]
def xy(p):
    P=sum(p)
    X=(3*sum(i*i for i in p)-P*P).exquo_ground(2)
    Y=(27*S.prod(p)-P**3+3*X*P).exquo_ground(2)
    return X,Y,P
p=probs(s,t); q=probs(u,v)
edge=[sum(q)-i for i in q]
x,y,P=xy(p); z,B,E=xy(edge)
for ed in (edge,[edge[0],edge[2],edge[1]]):
    os=[xy([p[i]*ed[(i+j)%3] for i in range(3)]) for j in range(3)]
    Ts=[o[2] for o in os]
    base=P*E*S.prod(Ts)**3
    out=[pol(0),pol(0),pol(0)]
    for j,(xx,yy,T) in enumerate(os):
        f=S.prod(Ts[:j]+Ts[j+1:])**3*P**4*E**4
        out[0]+=xx*T**2*f
        out[1]+=yy*T*f
        out[2]+=xx**2*f
    def mon(i,j,k,l):
        return base*x**i*y**j*z**k*B**l*P**(4-2*i-3*j)*E**(4-2*k-3*l)
    dx=out[0]-mon(1,0,0,0)-mon(0,0,1,0)
    de=out[1]-mon(0,1,0,0)-mon(0,0,0,1)
    dn=out[2]-mon(2,0,0,0)-mon(0,0,2,0)
    xz=mon(1,0,1,0); W=mon(0,1,1,0)+mon(1,0,0,1)
    A=mon(2,0,1,0); F=mon(1,0,2,0); H=A+F
    yB=mon(0,1,0,1)
    def odd(p):
        r=2*p[0]-p[1]-p[2]; g=p[1]-p[2]
        return g*(r**2-g**2)
    im=(27*odd(p)*odd(ed)*base*P*E).exquo_ground(64)
    checks=[
        13*xz-2*dn, 11*xz-de, 250*de+79*xz,
        -20*xz-40*W+40*yB+51*H-20*(dx-2*im),
        6*xz-6*W+yB+H-(de+im),
        2*(de+im)-12*xz+12*W-2*yB+19*H,
        -4*xz+44*W-14*yB+52*A+111*F-(5*(dn+10*im)-4*(de+im))
    ]
    assert all(min(f.coeffs())>=0 for f in checks)
