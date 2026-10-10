import numpy as np

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
