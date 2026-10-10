from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import importlib.util, hashlib, json, time, resource
base=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('submitted',base/'exact-source.py')
s=importlib.util.module_from_spec(spec);spec.loader.exec_module(s)
V=(base/'exact-table-I.txt').read_text();G=(base/'exact-table-II.txt').read_text()
start=time.monotonic()
print('START exact literal verify a=29/50',flush=True)
ret=s.verify(V,G)
print('PASS submitted verify returned',repr(ret),'elapsed_seconds',time.monotonic()-start,flush=True)
print('MAXRSS_KIB',resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,flush=True)
out=s.evaluate(V,G,250000,250000,a=F(29,50))
dg=[F(2,25),F(2,25),F(1,4),F(1)]; db=F(1,4)
E,H=map(s.defaultdict_from,out)
for val,t in zip(dg,[s.w,s.z,s.l,s.b]):
 fc,t=s.inner(t,t);E[t]+=fc*val
s.accumulate(H,s.symhom(s.one(),5),db)
E={t:c for t,c in E.items() if c};H={t:c for t,c in H.items() if c}
counts=Counter();N=[[F(0) for j in range(4)] for i in range(4)]
entries=[]
for t,c in sorted(E.items()):
 i,j,root=s.bound2(t);counts[i,j]+=1;N[i][j]+=root*abs(c)/(1+(i!=j));N[j][i]=N[i][j]
 entries.append({'term':list(t),'coefficient':str(c),'coefficient_times_Q2':str(c*250000**2),'pair':[i+1,j+1],'root_upper':str(root)})
expected_counts=[89,53,123,170,64,85,106,238,414,372]
expected_scaled=[321268243322644,96616799870252,294707669526536,385792585960684,269583307398596,115717471031956,125155603107368,605509501361296,618424270356936,1004504025266456]
pairs=[(i,j) for i in range(4) for j in range(i,4)]
actual_counts=[counts[i,j] for i,j in pairs]
actual_scaled=[N[i][j]*2*10**5*250000**2 for i,j in pairs]
assert actual_counts==expected_counts
assert actual_scaled==expected_scaled
print('PAIR COUNTS SCALED_ENTRY')
for (i,j),cnt,scaled in zip(pairs,actual_counts,actual_scaled):print(str(i+1)+str(j+1),cnt,scaled)
be=sum(map(abs,H.values()))
assert len(H)==11 and be*250000**2==1656725282
print('BOUNDARY_KEYS_Q2')
for key,val in sorted(H.items()):print(key,val*250000**2)
print('BOUNDARY_ABS_SUM_Q2',be*250000**2)
print('BOUNDARY_ABS_SUM',be)
U=[[2571,773,2358,3087],[773,2157,926,1002],[2358,926,4845,4948],[3087,1002,4948,8037]];nu=[2484,1440,996,304]
margins=[];ratios=[]
for i in range(4):
 for j in range(4):assert N[i][j]*100000<=U[i][j]
 upper=sum(F(U[i][j],100000)*nu[j] for j in range(4));allow=dg[i]*nu[i]
 margins.append(allow-upper);ratios.append((allow-upper)/allow)
 assert upper<allow
 print('ROW',i+1,'UPPER_PRODUCT',upper,'DIAGONAL_PRODUCT',allow,'MARGIN',allow-upper,'RELATIVE_MARGIN',(allow-upper)/allow)
assert be*100000<=2651 and F(2651,100000)<db
print('BOUNDARY_1_4_MARGIN',db-be)
print('EPSILON0_USING_DISPLAY_UPPER_MATRIX',min(ratios))
print('EPSILON_SUFFICIENT_FOR_I',min(ratios)*min(dg[1:3]))
print('TOTAL_NONZERO_INTERIOR_KEYS',len(E))
result={'counts':actual_counts,'scaled_entries':list(map(str,actual_scaled)),'boundary_keys':[{ 'key':list(k),'coefficient_times_Q2':str(v*250000**2)} for k,v in sorted(H.items())],'boundary_abs_sum':str(be),'D0':[[str(v) for v in row] for row in N],'diagonal_dominance_margins':list(map(str,margins)),'all_interior_keys':entries}
(base/'exact-results.json').write_text(json.dumps(result,indent=2)+'\n')
print('RESULT_SHA256',hashlib.sha256((base/'exact-results.json').read_bytes()).hexdigest())
print('END elapsed_seconds',time.monotonic()-start,'MAXRSS_KIB',resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
