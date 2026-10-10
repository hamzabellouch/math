#!/usr/bin/env python3
"""Segment auxiliary tables from independently reproduced scalar enclosures.
Depends on scalar_intervals.py and scalar-samples.json, produced by the separate
one-variable reviewer. All subsequent operations are outward rational intervals.
Also checks exact rational threshold endpoint comparisons and short-width budget.
"""
from pathlib import Path
from fractions import Fraction as F
import json
from scalar_intervals import I,SCALE
base=Path(__file__).parent
raw=json.loads((base/'scalar-samples.json').read_text())['samples'][:145]
rows=[{key:I(*val) for key,val in row.items()} for row in raw]
s=I('3.6'); tc=I('.021'); dk=1/I('.352')**2; dc=I('.80')*5*I('.043')**2/I('.352')**2;qM=I('.2559')
for i,row in enumerate(rows):
    row['t']=I(i)/40; row['D']=row['K']+tc*row['C'];row['q2']=row['q']**2; row['dD']=row['dot_K']+tc*row['dot_C']
for key in ['K','q','q2']:
    total=I(0)
    for i,row in enumerate(rows):
        if i: total=total+(row['a']-rows[i-1]['a'])*(row[key]-rows[i-1][key])
        row['P'+key]=row[key]-40*total/row['x'] if i else row[key]
for i,row in enumerate(rows):
    D0=rows[0]['D'];C0=rows[0]['C'];K0=rows[0]['K']
    row['B0']=row['PK']-(row['K']+K0)/2+dk*(row['D']-D0)**2+dc*(row['C']-C0)**2
    row['B1']=-(row['K']-K0)/2+dk*(row['D']-D0).positive()*(row['D']+D0+I('.0214')).positive()
    tanh=row['x']/row['a'] if i else I(0)
    row['Z1']=tanh*(I('.0178')-row['PK'])
    row['qexpr']=row['Pq2']-(row['q']+qM)*row['Pq']+(row['q']**2+qM**2)/2

def hull(vs):
    vs=list(vs);return I.raw(min(v.lo for v in vs),max(v.hi for v in vs))
def clip(v,top):
    top=I(top);return I.raw(min(v.lo,top.lo),min(v.hi,top.hi))
checks=[]
def check(name,got,low=None,high=None):
    ok=(low is None or got.lo>=I(low).lo) and (high is None or got.hi<=I(high).hi)
    checks.append(dict(name=name,passed=ok,enclosure=got.json(),claimed=[low,high]))
check('D-D0',hull(row['D']-rows[0]['D'] for row in rows),'-1e-8','.0314')
for name,high,formula,ix in [('PK','.01767',lambda z:z['PK'],145),('B0','.01773',lambda z:z['B0'],145),('B0-.0146t2','.00001',lambda z:z['B0']-I('.0146')*z['t']**2,145),('B1+halfP','.000001',lambda z:z['B1']+(z['PK']-I('.0049')).positive()/2,57),('B1+78Z12','.000001',lambda z:z['B1']+78*z['Z1']**2,57),('q expression','.01587',lambda z:z['qexpr'],57)]:
    check(name,hull(formula(z) for z in rows[:ix]),high=high)
check('dD',hull(z['dD'] for z in rows),low='-.0213')
check('Z1',hull(z['Z1'] for z in rows[:57]),'0','.00742')
for name,fn,low in [('minusC',lambda z:-z['C'],'.000005'),('q',lambda z:z['q'],'.000012'),('clipped D',lambda z:clip(z['D'],'-.01065'),'0'),('clipped P',lambda z:clip(z['PK'],'.0049'),'0')]:
    check('sample difference '+name,hull(fn(rows[i])-fn(rows[i-1]) for i in range(1,145)),low=low)
thresholds={'D':[61,54,44,37,29,21,14,0],'E':[247,224,192,167,141,116,90,42],'N':[216,178,143,115,77,42,17,0],'C':[664,545,444,347,234,152,97,21]}
claims={'D':[0,105,419,716,1124,1598,2069,3167],'E':[0,351,1326,2363,3673,5133,6885,10779],'N':[0,577,1576,2624,4378,6352,8026,9323],'C':[0,1776,4528,8066,13250,17831,21389,27670]}
args={'D':('dD',1,'.00040'),'E':('dot_C',-1,'.00120'),'N':('n_K',-1,'.00217'),'C':('n_C',1,'.00741')}
Hs=list(map(lambda x:F(x,1000),[0,75,150,200,250,300,350,400,540]))
ab={'D':['.07052','.0754'],'E':['.281','.254'],'N':['.24','.277'],'C':['.728','.812']}
for kind,vs in thresholds.items():
    key,sgn,eps=args[kind]
    for col,(v,claim) in enumerate(zip(vs,claims[kind])):
        total=sum(((1 if i in [0,144] else 2)*(sgn*row[key]+I(eps)-I(v)/1000).positive()/80 for i,row in enumerate(rows)),I(0))
        check(f'concentration {kind} column {col}',total*100000,high=str(claim))
        a,b=map(F,ab[kind])
        for H in Hs[col:col+2]:
            slack=2*H*(a-b*H-F(v,1000))-F(claim,100000)
            check(f'concentration threshold comparison {kind} {col} H={H}',I(str(slack)),low='0')
for name,G,L,o,claim in [('K','.238','.066','.0345','.000051'),('q','.53','.193','.1784','.000128'),('q2','.347','.099','.060','.000076')]:
    check('averaged-profile chord error '+name,(2*I(G)+2*I(L)+I(o))/12800,high=claim)
B0err=I('.000051')+I('.000019')/2+dk*I('.000020')*(2*I('.0314')+I('.000020'))+dc*I('.000062')*(2*I('.160')+I('.000062'))
check('B0 profile chord error',B0err,high='.000075')
B1err=I('.000019')/2+dk*I('.058')*I('.000020');check('B1 chord error',B1err,high='.000020')
prodErr=dk*I('.000021')*(2*I('.032')+I('.000021'))+dc*I('.320')*I('.000124')
check('B1 reduction error',prodErr,high='.000014')
Zerr=I('.000051')+(I('.0178')+I('.007')+I('.238')/12800)/12800+((I('.066')+I('.0345')/4)/40+2*I('.238')/12800)/(4*40)
check('Z1 chord error',Zerr,high='.000066')
check('s1 error accumulation',I('.000014')+I('.000020')+I('.000001')+78*I('.000066')*(2*I('.00742')+I('.000066')),high='.00015')
qerr=I('.000076')+2*qM*I('.000128')+(qM+I('.53')/12800)*I('.000042')+I('.193')/(4*40)*((I('.193')+I('.1784')/4)/40+2*I('.53')/12800)+I('.000042')*(2*qM+I('.000042'))/2
check('q-average expression error',qerr,high='.00018')
G=I('.22')**2*I('4.6')**2;H=I('.16');w=I('4.6');P=4+I('.15')*H**2;Q=I('.193')**2*P/G
short=(1+I('.064'))*(1-2*w**4*H**2/(15*(1+w**2)))/(1+H**2/3)-I('.064')*(P+Q)-(G*H**2/3*(P+Q+I('.79')*I('1.012')/G)**2+3/G*(I('.247')+I(2)/3*(G+I('.193')*I('.53')*I('1.012'))*H**2)**2)/(4*I('.65'))
check('short-width budget',short,low='.55')
result={'method':'outward rational intervals from separately generated scalar-samples.json','checks':checks,'passed':sum(x['passed'] for x in checks),'failed':sum(not x['passed'] for x in checks)}
(base/'segment-auxiliary-interval-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed':result['passed'],'failed':result['failed'],'failures':[x for x in checks if not x['passed']]},indent=2))
