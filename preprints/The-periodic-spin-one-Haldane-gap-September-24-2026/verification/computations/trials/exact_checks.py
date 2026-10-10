"""Independent small-chain contraction and structural checks for the 72-site trial."""
import json, hashlib
from itertools import product
from pathlib import Path
import numpy as np

source=Path('original_trial.py').read_text()
ns={}
exec(compile(source.split('\nkron=')[0], 'matrix-definitions', 'exec'), ns)
A=ns['A']; labels=ns['labels']
S=(-1,0,1)
data={'labels':labels,'matrices':{str(s):A[s].tolist() for s in S}}
Path('matrix-data.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
charge=[x[2] for x in labels]
for s in S:
    for i,j in product(range(len(labels)),repeat=2):
        assert A[s][i,j]==0 or charge[j]-charge[i]==2*s
B={(s,t): A[s]@A[t] for s,t in product(S,repeat=2)}
T=sum(np.kron(A[s],A[s]) for s in S)
O=sum(s*t*np.kron(B[s,t],B[s,t]) for s,t in product(S,repeat=2))
for s,t in product((-1,0),(0,1)):
    O+=np.kron(B[s,t],B[s+1,t-1])+np.kron(B[s+1,t-1],B[s,t])
delta=[a-b for a,b in product(charge,repeat=2)]
for i,j in product(range(len(delta)),repeat=2):
    if delta[i]!=delta[j]: assert T[i,j]==O[i,j]==0
blocks={d:[i for i,x in enumerate(delta) if x==d] for d in sorted(set(delta))}
N=4
amplitudes={}
for word in product(S,repeat=N):
    p=A[word[0]]
    for s in word[1:]: p=p@A[s]
    amp=int(np.trace(p))
    assert amp==0 or sum(word)==0
    assert amp==int(np.trace(A[word[1]]@A[word[2]]@A[word[3]]@A[word[0]]))
    amplitudes[word]=amp
norm_direct=sum(a*a for a in amplitudes.values())
energy_direct=0
for word,amp in amplitudes.items():
    for j in range(N):
        k=(j+1)%N
        energy_direct+=word[j]*word[k]*amp*amp
        for step in (-1,1):
            w=list(word);w[j]+=step;w[k]-=step
            if abs(w[j])<=1 and abs(w[k])<=1:
                energy_direct+=amp*amplitudes[tuple(w)]
norm_transfer=bond_transfer=0
for inds in blocks.values():
    ix=np.ix_(inds,inds)
    tb=T[ix];ob=O[ix];t2=tb@tb
    norm_transfer+=int((t2*t2.T).sum())
    bond_transfer+=int((t2*ob.T).sum())
assert norm_direct>0 and norm_direct==norm_transfer
assert energy_direct==N*bond_transfer
result={'length':N,'block_dimensions':{str(d):len(v) for d,v in blocks.items()},'total_dimension':len(delta),'matrix_sha256':hashlib.sha256(Path('matrix-data.json').read_bytes()).hexdigest(),'norm_direct':str(norm_direct),'norm_transfer':str(norm_transfer),'energy_direct':str(energy_direct),'bond_transfer':str(bond_transfer),'checks':'charge selection, exact T/O block preservation, cyclic amplitude invariance, zero total magnetization, all 81 physical amplitudes, full 4-site Hamiltonian energy'}
Path('exact-checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
