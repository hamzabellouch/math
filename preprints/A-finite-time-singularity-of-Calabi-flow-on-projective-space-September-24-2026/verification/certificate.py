# interval recurrence
scale=2**256
def pt(a): return (a*scale,a*scale)
O,I=pt(0),pt(1)
def neg(x):return (-x[1],-x[0])
def plus(x,y):return (x[0]+y[0],x[1]+y[1])
def timesn(x,n):
    return (n*x[0],n*x[1]) if n>=0 else (n*x[1],n*x[0])
def sums(L):
    a=b=0
    for x,y in L:a+=x;b+=y
    return (a,b)
def mul(x,y):
    p=x[0]*y[0];q=x[1]*y[0];r=x[0]*y[1];s=x[1]*y[1]
    return (min(p,q,r,s)//scale, -(min(-p,-q,-r,-s)//scale))
def inv(x):
    assert x[0]*x[1]>0
    return (scale*scale//x[1], -(-scale*scale//x[0]))
def divn(x,n):
    assert n>0
    return (x[0]//n,-(-x[1]//n))
def rat(a,b): return divn(pt(a),b)
def mag(x):return max(x[1],-x[0])
def mid(x):
    a=(x[0]+x[1])//2
    return (a,a)
def widen(x,z):
    a=z[1] # nonnegative
    return (x[0]-a,x[1]+a)
def width(x):return x[1]-x[0]
# p and linear P
A,B,C=pt(30),rat(751,4),rat(-1215,4)
k=rat(-94617116666041,10**15)
d=rat(400682721856639,10**15)
ks=[rat(25190,10**8),rat(-63731,10**8)]
ds=[rat(721855,10**8),rat(359157,10**8)]

def origin():
    # z stores series for W=1+p; return p,p',p'' at s=1 and variation cols
    z=[[plus(I,d)]+ds,[k]+ks]; b=[]
    for i in range(59):   # b_i coeff reciprocal W
        q=recip(z,b,i)
        den=pt(27*(i+1)*(i+11)*(i+12))
        z.append([mul(inv(den),timesn(plus(x,O if j or i else pt(-1)),8)) for j,x in enumerate(q)])
    ans=[]
    for a in range(3):
        ans.append([sums(divn(timesn(plus(v[j],O if i or j else pt(-1)),(4,6*i,3*i*(3*i-2))[a]),4) for i,v in enumerate(z))
                    for j in range(3)])
    assert max(width(v) for t in ans for v in t)*10**20<scale
    return [mid(x[0]) for x in ans], [[mid(y) for y in x[1:]] for x in ans]+[ds]

def recip(z,b,i):
    # z list 1+p and tangent cols; b reciprocal
    jlen=len(z[0]);f=inv(z[0][0])
    first=neg(mul(f,sums(mul(z[t][0],b[i-t][0]) for t in range(1,i+1)))) if i else f
    q=[first]
    q+= [neg(mul(f,sums([mul(z[t][j],(first if t==0 else b[i-t][0])) for t in range(i+1)]+
                        [mul(z[t][0],b[i-t][j]) for t in range(1,i+1)]))) for j in range(1,jlen)]
    b.append(q)
    return q

def horner(c):
    # step=1/8
    x=O
    for y in reversed(c): x=plus(y,divn(x,8))
    return x

degree=46
def evolve(V,T,R,h):
    # h positive integer inverse block length ell=1/h; current s h=R/8; theta=(s-sc)*h, z_j=coeff
    # V p,p_theta,p_thetatheta; T corresponding variations, 4 cols (vs scaled and d)
    assert all(x[0]>rat(-76,100)[1] and x[1]<rat(4,10)[0] for x in V[:1]) and mag(V[1])*100<6*scale and mag(V[2])*1000<10*scale
    assert max(mag(v) for t in T for v in t)<6*scale
    z=[([plus(x,I) if i==0 else x]+T[i]) if i!=2 else [divn(y,2) for y in [x]+T[i]] for i,x in enumerate(V)]
    E=[plus(d,I),O,O,O,I] # z variable = p+1, term C(z-(1+d)), tangent
    b=[]
    # ratio s/ell = R/8 (could exact integer); multiply equation by 4*(ratio+theta)^3:
    # 4 r^3 z''' +120 r^2 z'' +751 r z' -1215 (z-E) = 4/h^3 * r^3(b-1)
    for i in range(degree-2):
        recip(z,b,i)
        new=[]
        for j in range(5):
            def F(t):
                return plus(b[t][j],pt(-1) if j==t==0 else O) if t>=0 else O
            # multiply equation terms by 8^3
            x=divn(sums(timesn(F(i-p),4*(1,24,192,512)[p]*R**(3-p)) for p in range(4)),h**3)
            # (R+8theta)^3, coefficients 3R²*8; etc
            x=sums([x,
                timesn(z[i+2][j],-((4*i*24+120*8)*R**2*(i+1)*(i+2))),
                timesn(z[i+1][j],-((4*i*(i-1)*3+120*i*2+751)*64*R*(i+1))),
                timesn(z[i][j],-512*(4*i*(i-1)*(i-2)+120*i*(i-1)+751*i-1215)),
                timesn(E[j] if i==0 else O,-1215*512)])
            new.append(divn(x,4*(i+1)*(i+2)*(i+3)*R**3))
        z.append(new)
    z[0][0]=plus(z[0][0],pt(-1))
    # Cauchy remainder derived for all coefficients of STATE at degree degree-2 (differentiate z twice)
    # assert analytic sup all state <32 on radius .5; ratio=.25; err ≤ 32*(4/3)*.25^(degree-1)
    err=rat(48,4**(degree-1))
    res=[]
    for a in range(3):
        res.append([widen(horner([timesn(z[i][j],(1,i,i*(i-1))[a]) for i in range(a,degree+1)]),err) for j in range(5)])
    return [x[0] for x in res], [x[1:] for x in res]

def makeflows():
    U,Z=origin()
    hlist=sum(([h]*32 for h in (32,16,8)),[])+[4]*(4*(56-8))
    allm=[];mins=[]
    for index,h in enumerate(hlist):
        V=[divn(x,h**i) for i,x in enumerate(U)]
        T=[[I if i==j else O for j in range(4)] for i in range(3)]
        # scaled variations vs scaled input
        if index==0:s32=32
        R=(s32*h)//4; assert R*4==s32*h
        mini=2*scale
        for t in range(8):
            mini=min(mini,V[0][0]+scale-(scale//100+1))  # variation across substep < .01 analytically
            V,T=evolve(V,T,R+t,h)
        V=[timesn(x,h**i) for i,x in enumerate(V)]
        assert max(map(width,V))*10**19<scale
        U=[mid(x) for x in V]
        M=[[divn(timesn(x,h**i),h**j if j<3 else 1) for j,x in enumerate(row)] for i,row in enumerate(T)]+[[O,O,O,I]]
        assert max(width(x) for row in M for x in row)*10**15<scale
        allm.append([[mid(x) for x in row] for row in M])
        mins.append((h,mini));s32+=32//h
    return allm,mins,U,Z

def mm(x,y):
 return [[sums(mul(w,z) for w,z in zip(t,c)) for c in zip(*y)] for t in x]
def norm(x):return max(sum(mag(z) for z in t) for t in x)

def check(allm,mins,U,Z):
 assert norm(Z)<scale//50
 for i in range(1,len(allm)+1):
    T=[[I if m==n else O for n in range(4)] for m in range(4)]
    D=K=0
    for j in reversed(range(i)):
        h,r=mins[j];assert r>scale*23//100
        dT=norm([t[:3] for t in T[:3]])
        D+=dT
        K+=dT*scale**2//(h*r**3)+1  # rounds up to integer
        T=mm(T,allm[j])
        assert norm(T)<=8500*scale
    z=mm(T,Z)
    assert norm(z)<=scale*27//10
    assert D<=scale*570000 and K<=246000
 d1=mul(C,d);d2=mul(d1,plus(pt(567),d1))
 d3=sums([mul(rat(2025,4),d2),timesn(mul(d1,d2),2),neg(mul(mul(d1,d1),d1))])
 d4=sums([mul(rat(567,2),d3),timesn(mul(d1,d3),2),mul(d2,d2),timesn(mul(mul(d1,d1),d2),-3),mul(mul(d1,d1),mul(d1,d1))])
 pr=[[divn(timesn(x,(1,-3*m,3*m*(3*m+1))[a]),56**(3*m+a)) for a in range(3)] for m,x in enumerate([d1,d2,d3,d4],1)]
 res=[[plus(u,neg(sums(c)))] for u,c in zip(U,zip(*pr))]
 l=[[rat(v,10**5) for v in row] for row in [[30756,-27384,33447],[34622,13692,-16724],[-2925,-34040,-28850]]]
 assert norm(res)<rat(1,5*10**10)[0]
 assert norm(mm(l,res))<rat(3,10**12)[0]
 z=mm(l,z[:3])
 assert norm(z[:1])*1000<116*scale
 assert norm([[plus(w,neg(I) if i==j else O) for i,w in enumerate(t)] for j,t in enumerate(z[1:])])*10**3<scale

check(*makeflows())
