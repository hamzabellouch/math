import ast, hashlib, itertools
from pathlib import Path
import numpy as np
from scipy.sparse import csr_matrix, eye, kron
p=Path(__file__).resolve().with_name('original-computation.py')
code=p.read_text()
module=ast.parse(code)
ns={'np':np,'csr_matrix':csr_matrix}
exec(compile(ast.Module(body=[x for x in module.body if isinstance(x,ast.FunctionDef) and x.name in ('dmat','reps')],type_ignores=[]),'source-functions','exec'),ns)
Z=csr_matrix(np.diag([-1,0,1]),dtype=np.int64)
P=csr_matrix(np.array([[0,0,0],[1,0,0],[0,1,0]],dtype=np.int64))
N=P.T.tocsr(); I=eye(3,dtype=np.int64,format='csr')
def product(n, terms):
 out=csr_matrix([[1]],dtype=np.int64)
 for j in range(n): out=kron(out,terms.get(j,I),format='csr')
 return out
checks=0
for n in (4,5,6):
 words=list(itertools.product((-1,0,1),repeat=n)); lut={w:i for i,w in enumerate(words)}; dim=len(words)
 for tw in (0,1):
  H=csr_matrix((dim,dim),dtype=np.int64)
  for j in range(n):
   k=(j-1)%n; sign=-1 if tw and j==0 else 1
   H+=product(n,{k:Z,j:Z})+sign*(product(n,{k:P,j:N})+product(n,{k:N,j:P}))
  for M in range(-n,n+1):
   ids=[i for i,w in enumerate(words) if sum(w)==M]; ww=[words[i] for i in ids]
   got=ns['dmat'](ww,tw)
   expected=(32-3*n)*eye(len(ids),dtype=np.int64,format='csr')-2*H[ids,:][:,ids]
   assert (got-expected).nnz==0
   checks+=1
  for q in range(n):
   rows=[]; signs=[]; k=(-q)%n
   for w in words:
    v=w[q:]+w[:q]; rows.append(lut[v])
    signs.append(-1 if tw and sum(v[:k])%2 else 1)
   U=csr_matrix((signs,(rows,list(range(dim)))),shape=(dim,dim),dtype=np.int64)
   assert (H@U-U@H).nnz==0
   checks+=1
  for fun in (lambda w:w[::-1],lambda w:tuple(-x for x in w)):
   rows=[lut[fun(w)] for w in words]
   U=csr_matrix((np.ones(dim,dtype=np.int64),(rows,list(range(dim)))),shape=(dim,dim))
   assert (H@U-U@H).nnz==0
   checks+=1
 total=0; orbit_count=0
 for M in range(n+1):
  ww=[w for w in words if sum(w)==M]; rows,mult=ns['reps'](ww)
  total+=sum(mult); orbit_count+=len(rows)
 assert total==3**n
 print(f'n={n}: both twists; every magnetization block and all rotations/reflection/negation passed; representatives={orbit_count}; represented_columns={total}')
print('exact sparse matrix checks:',checks)
print('source SHA-256:',hashlib.sha256(p.read_bytes()).hexdigest())
