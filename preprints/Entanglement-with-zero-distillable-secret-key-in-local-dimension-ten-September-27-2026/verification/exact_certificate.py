from itertools import combinations, permutations

M = [
 [[6,0,0,0],[0,6,0,0],[0,0,6,0],[0,0,0,6],[0,0,0,0],[0,0,0,0]],
 [[-12,0,0,0],[0,-6,0,0],[0,0,6,0],[0,0,0,12],[-6,0,6,6],[-6,-6,6,0]],
 [[0,6,-2,0],[6,6,0,2],[-2,0,10,0],[0,2,0,24],[0,0,0,6],[0,-6,6,-6]],
 [[0,0,-4,-3],[0,-2,-3,-4],[-4,-3,11,6],[-3,-4,6,25],[6,6,0,0],[0,-6,6,6]]
]

def checksym():
 for i,j in combinations(range(4),2):
  for a,b in combinations(range(4),2):
   assert sum(M[i][r][a]*M[j][r][b]-M[j][r][a]*M[i][r][b] for r in range(6))==0

mons=[(a,b,d-a-b) for d in range(5) for a in range(d+1) for b in range(d-a+1)]
idx={u:i for i,u in enumerate(mons)}
eps=[(0,0,0),(1,0,0),(0,1,0),(0,0,1)]
def add(u,v):
 return tuple(a+b for a,b in zip(u,v))
def coefficients():
 R=[]
 for rows in combinations(range(6),4):
  coeff=[0]*35
  for perm in permutations(range(4)):
   sg=(-1)**sum(perm[i]>perm[j] for i,j in combinations(range(4),2))
   D={(0,0,0):sg}
   for r,c in zip(rows,perm):
    E={}
    for k in range(4):
     if M[k][r][c]:
      for u,v in D.items():
       t=add(u,eps[k])
       E[t]=E.get(t,0)+v*M[k][r][c]
    D=E
   for u,v in D.items(): coeff[idx[u]]+=v
  R.append(coeff)
 return R

def mult1(R,p):
 B=[[v%p for v in row] for row in R]
 detH=1
 for i in range(15):
  piv=next(j for j in range(i,15) if B[j][20+i])
  if piv!=i:
   B[i],B[piv]=B[piv],B[i]
   detH=(-detH)%p
  c=B[i][20+i]; detH=detH*c%p
  inv=pow(c,p-2,p)
  B[i]=[(x*inv)%p for x in B[i]]
  for j in range(15):
   if j!=i:
    c=B[j][20+i]
    B[j]=[(x-c*y)%p for x,y in zip(B[j],B[i])]
 T=[[0]*20 for _ in range(20)]
 for j,u in enumerate(mons[:20]):
  k=idx[add(u,(1,0,0))]
  if k<20: T[k][j]=1
  else:
   for i in range(20): T[i][j]=-B[k-20][i]%p
 return detH,T
def mm(A,B,p):
 BT=list(zip(*B))
 return [[sum(x*y for x,y in zip(row,col))%p for col in BT] for row in A]
def char(T,p):
 power=[[int(i==j) for j in range(20)] for i in range(20)]
 c=[1]
 tr=[0]
 for k in range(1,21):
  power=mm(power,T,p)
  tr.append(sum(power[i][i] for i in range(20))%p)
  c.append((-pow(k,p-2,p)*sum(c[i]*tr[k-i] for i in range(k)))%p)
 return c

# lists for polynomials below are low degree first, mod p
def trim(f):
 while f and f[-1]==0: f.pop()
 return f
def sub(f,g,p):
 h=f[:] + [0]*max(0,len(g)-len(f))
 for i,x in enumerate(g): h[i]=(h[i]-x)%p
 return trim(h)
def mul(f,g,p):
 if not f or not g: return []
 h=[0]*(len(f)+len(g)-1)
 for i,x in enumerate(f):
  for j,y in enumerate(g): h[i+j]=(h[i+j]+x*y)%p
 return trim(h)
def rem(f,g,p):
 h=f[:]; inv=pow(g[-1],p-2,p)
 while len(h)>=len(g):
  k=len(h)-len(g); a=h[-1]*inv%p
  for j,y in enumerate(g): h[k+j]=(h[k+j]-a*y)%p
  trim(h)
 return h
def gcd(f,g,p):
 while g: f,g=g,rem(f,g,p)
 return f
def pth(u,f,p):
 n=p; a=u; b=[1]
 while n:
  if n%2: b=rem(mul(b,a,p),f,p)
  a=rem(mul(a,a,p),f,p); n//=2
 return b
def gcddegrees(coef,p):
 f=coef[::-1]
 z=[0,1]
 u=z
 ds=[]
 for k in range(1,21):
  u=pth(u,f,p)
  ds.append(len(gcd(f,sub(u,z,p),p))-1)
 return ds

checksym()
R=coefficients()
for p in (41,131,139):
 detH,T=mult1(R,p)
 c=char(T,p)
 print(p,detH)
 print(c)
 print(gcddegrees(c,p))
