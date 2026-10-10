from fractions import Fraction as F
from itertools import product
from collections import defaultdict
from struct import unpack
from math import factorial

Q=2**56
c=[84**j*(factorial(256)//factorial(j)) for j in range(257)]
probs=[Q*v//sum(c) for v in c]
while probs[-1]==0: probs.pop()

def part(n,g):
    sectors=defaultdict(list)
    for x in product((-1,0,1),repeat=n):
        if sum(x)>=0: sectors[sum(x)].append(x)
    tot=0
    for m,basis in sectors.items():
        d={x:i for i,x in enumerate(basis)}
        cnt=defaultdict(int)
        for x in basis:
            rev=x[::-1]
            r=min(y[k:]+y[:k] for y in (x,rev) for k in range(n))
            cnt[d[r]] += (1 if m==0 else 2)
        allreps=list(cnt)
        adj=[]
        for x in basis:
            lists={0:[],1:[],-1:[]}
            for j in range(n):
                k=(j+1)%n
                for delta in (-1,1):
                    if abs(x[j]-delta)>1 or abs(x[k]+delta)>1: continue
                    y=list(x); y[j]-=delta; y[k]+=delta
                    phase=(delta if k==0 and g!=0 else 0)
                    if phase==-1 and g==1: phase=1
                    lists[phase].append(d[tuple(y)])
            diag=16-3*n//2-sum(x[j-1]*x[j] for j in range(n))
            adj.append((diag,lists[0],lists[1],lists[-1]))
        for start in range(0,len(allreps),192):
            reps=allreps[start:start+192]
            w=len(reps)
            stride=((1<<(64*w))-1)//(2**64-1)
            bias=(1<<63)*stride; mask=(2**60-1)*stride; b16=bias>>4
            u=[0]*len(basis); v=[0]*len(basis)
            for q in probs[::-1]:
                get=u.__getitem__
                if g==0:
                    y=[diag*a-sum(map(get,i)) for a,(diag,i,j,k) in zip(u,adj)]
                elif g==1:
                    y=[diag*a-sum(map(get,i))+sum(map(get,j)) for a,(diag,i,j,k) in zip(u,adj)]
                else:
                    gev=v.__getitem__
                    y=[diag*a-sum(map(get,i))+sum(map(gev,j))+sum(map(get,k))-sum(map(gev,k)) for a,(diag,i,j,k) in zip(u,adj)]
                    z=[diag*a-sum(map(gev,i))+sum(map(gev,j))-sum(map(get,j))+sum(map(get,k)) for a,(diag,i,j,k) in zip(v,adj)]
                    v=[(((a+bias)>>4)&mask)-b16 for a in z]
                u=[(((a+bias)>>4)&mask)-b16 for a in y]
                for t,idx in enumerate(reps):
                    u[idx]+=q<<(64*t)
            fmt='<'+str(w)+'Q'; mult=[cnt[k] for k in reps]
            for i,row in enumerate(u):
                us=unpack(fmt,(row+bias).to_bytes(8*w,'little'))
                vs=unpack(fmt,(v[i]+bias).to_bytes(8*w,'little'))
                for c,a,b in zip(mult,us,vs):
                    a-=2**63; b-=2**63
                    tot+=c*(a*a-a*b+b*b)
    return tot

def table():
    centers=[[8945303,346734,939987],[3741281,567167,984108],[2327547,721090,1002613]]
    for row,n in zip(centers,(6,8,10)):
        x=F(1500000-1401482,10**6)*F(21*n,2)
        lo=sum(x**j/factorial(j) for j in range(101))
        hi=lo+2*x**101/factorial(101)
        for g,num in enumerate(row):
            t=part(n,g); print(t)
            assert lo*t/Q**2>F(num-2,10**6) and hi*t/Q**2<F(num+2,10**6)
if __name__=='__main__':
    table()
