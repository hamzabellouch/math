from fractions import Fraction as F
Q=1<<224;R=F(31,25); N=45
def loadS(n,path):
 it=iter(open(path));A={};B={}
 for i,j in ([(i,j) for i in range(n+1) for j in range(i%3,min(i,n-i)+1,3)] if SORT=='ij'
             else [((k+h)//2,(k-h)//2) for k in range(n+1) for h in range(k%2,k+1,2) if h%3==0]):
   x=F(next(it).strip())*(R**(i+j-2)) *18 # S/2 *36
   for i0,j0 in [(i,j),(j,i)]:
    if i0*j0: A[i0-1,j0-1]=A.get((i0-1,j0-1),0)+x*i0*j0
    if i0>=2:B[i0-2,j0]=B.get((i0-2,j0),0)+x*i0*(i0-1)
 assert list(it)==[]
 return A,B
import os
env=os.environ.get;SORT=env('RSORT','ij')
A,B=loadS(int(env('RDEG','22')),env('RS','/tmp/newc22'))
print([float(sum(map(abs,f.values())))for f in [A,B]])
from collections import defaultdict
from math import comb,factorial,pi
K=236
U=1<<115;T=1<<69;N=128;J=14
def uq(p):
 return {k:int(U*v)for k,v in p.items()}
A,B=uq(A),uq(B)
with open('/tmp/qP') as f0:
 P={(i,k-i):F(int(next(f0)),Q)*R**k for k in range(K+1) for i in range(k+1)}
r={(0,0):F(1,3),(1,0):R/6,(0,1):R/6}
D={k:2*v+r.get(k,0)for k,v in P.items()}
for (i,j),x in r.items():
 for (m,n),y in r.items():
  D[m+i,n+j]-=x*y
D=uq(D)
L=defaultdict(int)
for (i,j),v in D.items():
 a=(i-j)%3
 if a==1 or not v:continue
 for (m,n),u in (B if a else A).items():
  L[i+m,j+n]+=u*v*(2 if a else 1)//U
Pe=uq({k:2*v+r.get(k,0)for k,v in P.items()})
Pb=uq({k:-3*v for k,v in P.items()if (k[0]-k[1])%3==0})
def err(f):
 vals=[(i+j,abs(v)/U)for (i,j),v in f.items()]
 ell=sum(x for k,x in vals)
 a=sum(x*(k*pi/(6*N))**(J+1)/factorial(J+1)for k,x in vals)
 b=sum(x*comb(k,J+1)/(2*N)**(J+1)for k,x in vals)
 vals=[(i+j,F(abs(v),U))for (i,j),v in f.items()]
 assert all(k<320 for k,x in vals)
 m=J+1; piup=F(22,7)
 assert sum(x for k,x in vals)<1<<36 and sum(x*((k*piup/(6*N))**m/factorial(m)+4*F(comb(k,m),(2*N)**m)) for k,x in vals)<F(1,10**10)
 return ell,a,b
allf=[[(0,L)],[(0,Pb),(4*N,Pe)],[(0,A)],[(0,B)],[(0,B)]]
assert all(sum(map(abs,f.values())) < U * 2**36 for f in [A,B,D,L,Pe,Pb])
print([[err(f)for _,f in row]for row in allf])
def atan(q):
 return sum((-1)**j*(U//(q**(2*j+1)*(2*j+1))) for j in range(36))
h=(16*atan(5)-4*atan(239))//(6*N)
def cs(mm,b,spin,imag):
 z=h*((mm*(b+spin))%(12*N))
 u=[U,z]
 for i in range(2,84):u.append(-u[-2]*z*z//(U**2*i*(i-1)))
 c=sum(u[imag::2]);s=(-1 if imag else 1)*sum(u[(1-imag)::2]);a=[c]
 for i in range(1,J+1):
  c,s=(-s*h*mm//(i*U),c*h*mm//(i*U))
  a.append(c)
 return a
def series(row,s,imag):
 d=max(i+j for _,f in row for i,j in f)
 g=[[0]*(J+1) for k in range(d+1)]
 for spin,f in row:
  tr={m:cs(m,2*s+1,spin,imag)for m in set(i-j for i,j in f)}
  for (i,j),v in f.items():
   if v:
    for p,x in enumerate(tr[i-j]):
     g[i+j][p]+=v*x
 return [[v*T//U**2 for v in a] for a in g]
def export(s,path):
 with open(path,'w') as dest:
  print(T,N,J,len(allf),file=dest)
  for i,row in enumerate(allf):
   m=series(row,s,i==4)
   print(len(m),file=dest)
   for a in m:print(*a,file=dest)
if __name__=='__main__':
 import sys
 if len(sys.argv)>1:export(int(sys.argv[1]),'/tmp/roogjet')
