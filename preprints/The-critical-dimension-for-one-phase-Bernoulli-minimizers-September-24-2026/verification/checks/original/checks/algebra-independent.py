#!/usr/bin/env python3
"""Independent checks of the bernoulli-critical-dimension algebra; no submitted code is executed.

The tables are the only shared mathematical input. Sparse ordinary polynomials
are used only for the boundary; full coordinate matrices for projections.
"""
from pathlib import Path
from collections import Counter
from fractions import Fraction as F
from itertools import product, permutations
from hashlib import sha256
import json
import numpy as np

ROOT=Path(__file__).resolve().parents[1]
data=(ROOT/'certificate-inputs.txt').read_bytes()
assert sha256(data).hexdigest()=='3b1e67b40af1740a1faab1ee8bbe85aa7c90dcb289fb5df2c8880de6956a8ffc'
text=data.decode()
fences=text.split('~~~')
V=fences[1].strip(); B=fences[3].strip()
Q=250000
zero=(0,0,0,0)
def add(a,b):
 c=Counter(a)
 for t,x in b.items():c[t]+=x
 return {t:x for t,x in c.items() if x}
def scale(a,c):return {t:x*c for t,x in a.items() if x*c}
def mul(a,b):
 c=Counter()
 for t,x in a.items():
  for u,y in b.items():c[tuple(a+b for a,b in zip(t,u))]+=x*y
 return {t:x for t,x in c.items() if x}
def power(a,n):
 r={zero:1}
 for _ in range(n):r=mul(r,a)
 return r
one={zero:1}
x=[{tuple(int(i==j) for i in range(4)):1} for j in range(4)]
lam={t:-1 for xi in x for t in xi}
eigen=[lam]+x
R=power(lam,2)
for xi in x:R=add(R,power(xi,2))
trace3={}
for y in eigen:trace3=add(trace3,power(y,3))

ranks={'f':0,'U':2,'K':4,'M':1,'P':1}
Vrows=[]
shape_counts=Counter()
for line in V.splitlines():
 k,s,c=line.split();c=int(c); r=ranks[k]
 assert len(s)%3==0
 h,b,j=map(int,s[:3]);edges=[tuple(map(int,s[i:i+3])) for i in range(3,len(s),3)]
 counts=Counter(a for e in edges for a in e[:2])
 assert all(counts[i]==1 for i in range(r))
 assert all(i<r or i==5 for i in counts)
 assert j==0
 if k in ('U','K'):assert counts[5]%2==0
 if k=='P':assert h>0
 Vrows.append((k,r,h,b,edges,c));shape_counts[k]+=1

# Evaluate a raw table tensor component at diagonal A, p=e_0, g=0.
# No graph contraction/canonicalization from the submission is used.
def component(row,idx):
 k,r,h,b,edges,c=row
 if h:return {}
 out=power(trace3,b)
 for a,b,exp in edges:
  ia=idx[a] if a<r else 0
  ib=idx[b] if b<r else 0
  if ia!=ib:return {}
  out=mul(out,power(eigen[ia],exp))
 return out

def total_component(kind,idx):
 out={}
 for row in Vrows:
  if row[0]==kind:out=add(out,scale(component(row,idx),row[-1]*Q))
 return out
# All polynomials below have been scaled by Q^2.
f=total_component('f',())
S=scale(mul(lam,f),-1)
S=add(S,total_component('U',(0,0)))
S=add(S,total_component('M',(0,)))
for i in range(1,5):
 s0=add(mul(lam,eigen[i]),scale(power(eigen[i],2),-1))
 S=add(S,mul(s0,total_component('U',(i,i))))
 # The only nonzero V entries here are permutations of (0,i,i),
 # with value s0. The C_{0,0,i,i} contribution vanishes by skewness.
 cs=total_component('K',(0,i,0,i))
 cs=add(cs,scale(total_component('K',(i,0,0,i)),-1))
 cs=add(cs,total_component('K',(0,i,i,0)))
 cs=add(cs,scale(total_component('K',(i,0,i,0)),-1))
 S=add(S,mul(s0,cs))

# Parse every Gram row, verify degrees and slots independently.
blocks=[]
for line in B.splitlines():
 if line.startswith('@'):
  _,r,kind,mode=line.split();blocks.append((int(r),kind,mode,[]));continue
 s,*vals=line.split();r,kind,mode,rows=blocks[-1]
 vals=list(map(int,vals));rows.append((s,vals))
 if r>=0:
  assert len(s)%3==0
  h,b,j=map(int,s[:3]);edges=[tuple(map(int,s[i:i+3])) for i in range(3,len(s),3)]
  counts=Counter(a for e in edges for a in e[:2])
  assert all(counts[i]==1 for i in range(r))
  assert all(i<r or i in (5,6,7) for i in counts)
  assert counts[7] in (0,3)
  assert int(j in (1,2))+counts[6]+int(counts[7]>0)==1
  assert mode in ('I','B')
 else:
  assert r==-1 and len(s)==4 and sum(map(int,s))<=2
  assert mode in ('I','H') and kind=='none'
for r,kind,mode,rows in blocks:
 assert len({len(v) for s,v in rows})==1

Lambda={}
for r,kind,mode,rows in blocks:
 if r!=-1:continue
 for col in range(len(rows[0][1])):
  J={}
  for s,vs in rows:J=add(J,{tuple(map(int,s)):vs[col]})
  Js=power(J,2)
  if mode=='H':Js=mul(Js,scale(lam,-1))
  Lambda=add(Lambda,Js)
E=add(add(Lambda,{zero:Q*Q//4}),scale(S,-1))
# Averaging x monomials is exactly represented by sorted multi-index keys;
# homogenize each even or odd degree to 4 or 5 respectively using R=1.
Eb=Counter()
for alpha,c in E.items():
 assert sum(alpha)<=5
 term=mul({alpha:c},power(R,(5-sum(alpha))//2))
 for beta,v in term.items():Eb[tuple(sorted(beta))]+=v
Eb={t:c for t,c in Eb.items() if c}
assert len(Eb)==11
assert sum(abs(c) for c in Eb.values())==1656725282

# Build full integer coordinate matrices of the tensor projections.
# E_j is passed directly through the formulas; no table expansion is shared.
def transform(t,kind):
 r=t.ndim
 if kind=='none':return t.copy()
 sym=sum((np.transpose(t,p) for p in permutations(range(r))),np.zeros_like(t))
 if kind=='anti':
  out=np.zeros_like(t)
  for p in permutations(range(r)):
   inv=sum(p[i]>p[j] for i in range(r) for j in range(i+1,r))
   out+=(-1)**inv*np.transpose(t,p)
  return out
 if kind=='hook':sym=3*(t+np.swapaxes(t,0,1))-sym
 if r==2:return 5*sym-np.eye(5,dtype=np.int64)*np.trace(sym)
 v=np.trace(sym,axis1=0,axis2=1)
 out=(8 if kind=='hook' else 7)*sym
 for i,j,k in product(range(5),repeat=3):
  if kind=='hook':out[i,j,k]-=2*(i==j)*v[k]-(i==k)*v[j]-(j==k)*v[i]
  else:out[i,j,k]-=(i==j)*v[k]+(i==k)*v[j]+(j==k)*v[i]
 return out
projection_results=[]
for r,kind,fac,expected_rank in [(1,'none',1,5),(2,'anti',2,10),(2,'sym',10,14),(3,'sym',42,30),(3,'hook',48,35)]:
 n=5**r;cols=[]
 for j in range(n):
  t=np.zeros(n,dtype=np.int64);t[j]=1
  cols.append(transform(t.reshape((5,)*r),kind).reshape(-1))
 P=np.stack(cols,axis=1)
 assert np.array_equal(P,P.T)
 assert np.array_equal(P@P,fac*P)
 assert int(np.trace(P))==fac*expected_rank
 projection_results.append({'rank':r,'kind':kind,'positive_scale':fac,'image_dimension':expected_rank,'matrix_sha256':sha256(P.tobytes()).hexdigest()})

# Explicit rational equality case of the 5/7 contraction estimate.
A=[F(4),F(-1),F(-1),F(-1),F(-1)];zet=[F(1),F(0),F(0),F(0),F(0)]
Z={}
for i,j,k in product(range(5),repeat=3):
 sym=(zet[i]*A[j]*(j==k)+zet[j]*A[i]*(i==k)+zet[k]*A[i]*(i==j))/3
 v=[F(2,3)*A[s]*zet[s] for s in range(5)]
 Z[i,j,k]=sym-((i==j)*v[k]+(i==k)*v[j]+(j==k)*v[i])/7
assert all(sum(Z[i,j,j] for j in range(5))==0 for i in range(5))
q=[sum(Z[i,j,j]*A[j] for j in range(5)) for i in range(5)]
znorm=sum(v*v for v in Z.values());anorm=sum(v*v for v in A)
ratio=sum(v*v for v in q)/(znorm*anorm)
assert ratio==F(5,7)

U=[[2571,773,2358,3087],[773,2157,926,1002],[2358,926,4845,4948],[3087,1002,4948,8037]]
nu=[2484,1440,996,304];d=[F(2,25),F(2,25),F(1,4),F(1)]
margin=[d[i]-F(sum(U[i][j]*nu[j] for j in range(4)),100000*nu[i]) for i in range(4)]
assert all(c>0 for c in margin)
epsilon=min(margin[1:3]);assert epsilon==F(438907,12000000)
scaled=[321268243322644,96616799870252,294707669526536,385792585960684,269583307398596,115717471031956,125155603107368,605509501361296,618424270356936,1004504025266456]
for val,(i,j) in zip(scaled,((i,j) for i in range(4) for j in range(i,4))):assert F(val,2*Q**2)<=U[i][j]
result={
 'input_sha256':sha256(data).hexdigest(),
 'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
 'table_I_sha256':sha256(V.encode()).hexdigest(),
 'table_II_sha256':sha256(B.encode()).hexdigest(),
 'table_I_row_counts':dict(shape_counts),
 'table_II_block_count':len(blocks),
 'table_II_row_count':sum(len(rows) for r,kind,mode,rows in blocks),
 'boundary_scaled_sorted_coefficients':{str(t):c for t,c in sorted(Eb.items())},
 'boundary_key_count':len(Eb),
 'boundary_Q_squared_absolute_sum':sum(abs(c) for c in Eb.values()),
 'projection_results':projection_results,
 'X_A_bound_sharp_squared_ratio':str(ratio),
 'weighted_diagonal_margins_from_displayed_upper_matrix':list(map(str,margin)),
 'epsilon_for_z_and_ell_from_displayed_upper_matrix':str(epsilon),
 'not_verified':['Full interior graph coefficient expansion and all ten aggregate sums from original tables','Analytic free boundary reduction/cutoffs and invoked external classification/existence theorems'],
 'shared_implementation_dependencies':'None of the submitted code; shared inputs are input.md and the two coefficient tables. Python standard library and NumPy 64-bit integer matrix arithmetic; matrix products here have small bounded integer entries.'
}
print(json.dumps(result,indent=2,sort_keys=True))
