"""Independent structural and magnitude audit of the existing exact replay keys.
Does not execute the submitted engine or claim to recreate its coefficients.
"""
from pathlib import Path
from collections import Counter
from fractions import Fraction as F
from math import isqrt
from hashlib import sha256
import json
base=Path(__file__).resolve().parent
raw=(base/'exact-results.json').read_bytes()
assert sha256(raw).hexdigest()=='73e21b8c154994f482ad0ed7582990191b71f6c1e2cd84b905a3aee3d92aec6a'
record=json.loads(raw)
P,L,X,Y=-1,-2,-3,-4
counts=Counter(); topology=Counter(); N=[[F(0) for j in range(4)] for i in range(4)]
for row in record['all_interior_keys']:
 r,g,w,z,traces,edges=row['term']
 assert r==0 and all(isinstance(a,int) and a>=0 for a in (g,w,z))
 assert all(k>=3 for k in traces)
 assert all(i in (P,L,X,Y) and j in (P,L,X,Y) and k>=0 for i,j,k in edges)
 ports=Counter(a for e in edges for a in e[:2])
 assert ports[X] in (0,3) and ports[Y] in (0,3)
 nodes=[v for v in (X,Y) if ports[v]]
 assert len(nodes)<=2
 selfedges=[(i,k) for i,j,k in edges if i==j and i in (X,Y)]
 assert all(k>0 for i,k in selfedges)
 assert all(sum(i==v for i,k in selfedges)<=1 for v in nodes)
 cross=sum({i,j}=={X,Y} for i,j,k in edges)
 assert all(2*sum(i==v for i,k in selfedges)+cross<=3 for v in nodes)
 kinds=[0]*w+[1]*z+[2]*ports[L]+[3]*len(nodes)
 assert len(kinds)==2
 i,j=sorted(kinds);assert row['pair']==[i+1,j+1]
 counts[i,j]+=1;topology[len(nodes),len(selfedges),cross]+=1
 sq=F(1);theta=F(4,5)
 for k in traces:sq*=F(9,20) if k==3 else theta**(k-2)
 for a,b,k in edges:
  if a==b and a in nodes:sq*=F(5,7) if k==1 else theta**(k-1)
  else:sq*=theta**k
 b=ports[P]
 if g and b:sq*=F(g,g+b)**g*F(b,g+b)**b
 grid_sq=sq*100000**2
 ceil=isqrt(grid_sq.numerator//grid_sq.denominator)
 if ceil*ceil<grid_sq:ceil+=1
 upper=F(ceil,100000)
 assert upper==F(row['root_upper'])
 c=abs(F(row['coefficient']))
 N[i][j]+=c*upper/(1+(i!=j))
 if i!=j:N[j][i]=N[i][j]
assert sum(counts.values())==1714
expected=[321268243322644,96616799870252,294707669526536,385792585960684,269583307398596,115717471031956,125155603107368,605509501361296,618424270356936,1004504025266456]
scaled=[N[i][j]*2*100000*250000**2 for i in range(4) for j in range(i,4)]
assert scaled==expected
print(json.dumps({'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'coefficient_input_sha256':sha256(raw).hexdigest(),'nonzero_keys':sum(counts.values()),'topologies_nX_selfedges_crossedges':{str(k):v for k,v in sorted(topology.items())},'pair_counts':{str(k):v for k,v in sorted(counts.items())},'scaled_D0_entries':list(map(str,scaled)),'limitations':'Coefficients are the existing submitted-engine replay output. This check independently validates every retained key graph class, every magnitude factor/upper root, and aggregation; it does not independently generate the coefficients.'},indent=2,sort_keys=True))
