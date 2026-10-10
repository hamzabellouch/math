"""Exact rational checks for scalar tail, interpolation and pointwise ledgers."""
from scalar_intervals import I, k, PI, LOG2
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
import json

checks=[]
def record(name,left,right):
    left=left if isinstance(left,I) else I(left); right=right if isinstance(right,I) else I(right)
    checks.append({'name':name,'pass':left.hi<right.lo,'left':left.json(),'right':right.json()})
def add(*vs):return [sum(v[j] for v in vs) for j in range(len(vs[0]))]
def scale(s,v):return [s*x for x in v]
def mul(a,b):return [sum(F(comb(j,l))*a[l]*b[j-l] for l in range(j+1)) for j in range(min(len(a),len(b)))]
P=[F(2)**j for j in range(5)]; Id=[F(1),F(0),F(0),F(0),F(0)]; J=[F(0),F(1),F(0),F(0),F(0)]
xi=F(1,4096)
N=add(Id,scale(F('3.1')*xi,P)); M=add(Id,scale(F('1.02')*xi,P)); H=add(scale(F('4.59'),Id),J,scale(F('1.05')*xi,P))
A=add(scale(F('1.55'),mul(P,add(N,Id))),scale(F('6.2'),P),scale(F('.5'),mul(P,mul(N,N))),scale(2*F('1e-6')*xi,mul(P,N)))
C=add(scale(F('1.02'),mul(P,add(M,Id))),mul(P,mul(N,N)))
for j in range(5):record(f'A vector j={j}',A[j],10*P[j]);record(f'C vector j={j}',C[j],F('3.2')*P[j])
for j in range(5):record(f'm vector j={j}',mul(P,N)[j],F('1.02')*P[j])
record('n-1 derivative vector',3+7*30*xi+6*630*xi**2+22680*xi**3,'3.1')
z=F('1.02')*xi
record('log m vector',F('1.02')*(1+4*z+z*z)/(1-z)**4,'1.04')
E_K=scale(xi,add(scale(F('1e-6'),P),mul(P,add(scale(F('11.05'),P),scale(F('3.2'),mul(P,H))))))
Ed=add(scale(F('.5'),P),scale(xi,add(scale(F('1e-6'),P),scale(F(10),mul(P,P)),mul(mul(P,P),mul(mul(N,N),H)))))
Eg=mul(P,add(scale(F('.5'),N),scale(F('.25')*xi,mul(P,mul(N,N))),scale(F('.5'),mul(mul(M,M),H))))
Ec=add(Ed[:3],scale(F('6.5')*xi,mul(P[:3],[Eg[j+1]+Eg[j+2] for j in range(3)])))
for title,vec,bounds in [('K tail',E_K,['.0064','.027','.11']),('d tail',Ed,['.51','1.02','2.1']),('C tail',Ec,['.55','1.16','2.61'])]:
    for j,bound in enumerate(bounds):record(f'{title} j={j}',vec[j],bound)

# Finite elementary series remainder certificates.
record('exp26 remainder using e<3',F(3,factorial(27)),'1e-27')
record('large-x phi cutoff',10**26,F('1.645')**121)
def atan_rational(x,n):
    v=sum(((-1)**j*x**(2*j+1)/F(2*j+1) for j in range(n)),F(0))
    tail=x**(2*n+1)/F(2*n+1)
    return I(v-tail,v+tail)
pienc=16*atan_rational(F(1,5),32)-4*atan_rational(F(1,239),10)
record('pi lower',I.raw(PI.lo,PI.lo),I.raw(pienc.lo,pienc.lo))
record('pi upper',I.raw(pienc.hi,pienc.hi),I.raw(PI.hi,PI.hi))

# Interpolation and q-product ledgers, all exactly rational.
R=lambda x:F('.536')*F(x)+F('.00001')
e=F('19.2')/12800; delta=F(1,40)
dqerr=F('2.164')*R('.00092')+F('.1338')*e+F('2.8')*delta*F('.01037')/4
sqerr=(2*F('.1908')+F('.0016'))*F('.0016')+F('.0127')**2/4
ddqerr=F('2.164')*R('.00421')+F('.415')*e+F('2.8')*delta*F('.03670')/4+2*(F('2.164')*F('.000654')+F('.1908')**2*e+F('2.8')*delta*(2*F('.1908')*F('.0127'))/4)
record('dot q chord',dqerr,'.0016');record('dot q square chord',sqerr,'.000654');record('ddot q chord',ddqerr,'.0095')
record('q chord',(F('.508')+F('.0095'))*delta**2/8,'.000042')
record('nq chord',F('.0095')+F('.0016')+F('.1908')/12800+delta*F('.0127')/4,'.012')
Sqerr=2*F('.000042')+(1+1/F('3.6')**2)*F('.0016')+F('.1908')*2/12800+F('1.08')*delta*F('.0127')/4+(F('.0095')+F('.508')*2/12800+delta*F('.047')/4)/F('3.6')**2
record('Sq chord',Sqerr,'.003')
ec=R('.00222'); es=R('.000673')+F('.021')*ec
ue=F('1.507')*R('.00402')+12*F('.80')/F('.352')**2*(F('1.25')*es*(2*(F('.06542')+F('.021')*F('.2456'))+es)+5*F('.043')**2*ec*(2*F('.2456')+ec))
record('U star error',ue,'.010');record('U star final',F('.547'),F('.54')*F('.22')**2*F('4.6')**2)
record('nK positivity at t>=1.4',R('.00402'),'.00315')
for t in [F('-.022'),F('.064')]:record('sign chord error '+str(t),(F('.238')+abs(t)*F('.79'))/12800,'.000024')
record('discriminant chord error',(F('.74')*F('.79')+F('2.6')*F('.238'))/12800,'.0001')
record('tail discriminant',F('.352')**2,F('.74')*F('.499')-F('.37')**2-F('2.6')*F('.0008'))
record('tail Ustar',12*F('.8')/F('.352')**2*(F('1.25')*(F('.002')+F('.021')*F('.001'))**2+5*F('.043')**2*F('.001')**2),'.001')
record('tail integral bound',(6*LOG2+1)/64,'.086')
record('global integral bound',F('.335')+F('.086'),'.422')
record('Sq pi positive margin','.25',4*I('.365')+4*k*I('.113')-I('.113')**2-I('1.104')**2)
den=I('.602')+I('.022')+I('1.16')*I('-.022')+I('.125')
record('e0 auxiliary',I('1.053')*I('1.16')**2/(8*den),'.256')
record('alpha auxiliary',I('.256')+(LOG2+I('.25'))*I('2.26')/4,'.80')

# The pointwise inequality is concave in each retained H,V2 rectangle.
rows=[(77,81,113,132,725,743,804),(80,88,125,166,740,785,814),(87,100,159,220,782,848,831),(99,116,213,288,845,920,853),(115,134,281,359,917,986,877),(133,171,352,464,983,1055,927),(170,211,457,504,1041,1059,992),(210,245,497,513,1009,1044,1072),(244,256,506,514,999,1012,1104)]
rows=[[I(n)/1000 for n in row] for row in rows]
bm=(1+I('.064'))*(I('.602')-3*I('.022'))/(3*(3*(I('.602')+I('.022'))-4*I('.365')))
claimed=[11,14,33,64,63,39,54,45,40]
pointwise=[]
for zi,zrow in enumerate(rows):
    candidates=[]
    for xi,xrow in enumerate(rows):
        qlo,qhi,slo,shi,vlo,vhi,rhi=xrow
        Hlo=4*I('.365')+4*k*qlo+2*(k-qlo)*zrow[2]-2*I('.22')*zrow[6]
        Hhi=4*I('.365')+4*k*qhi+2*(k-qhi)*zrow[3]+2*I('.22')*zrow[6]
        cost=2*(I('.602')+I('.022')+(I('.602')+I('.022')-I('1.16'))*I('-.022'))+2*bm*zrow[3]*shi+2*I('.256')*(2*I('.043'))**2+I('.043')*I('.5')/2
        for Hval in [Hlo,Hhi]:
            for Vval in [vlo,vhi]:
                Jval=Hval+Vval-2*I('1.16')
                val=Hval-cost+I('.021')*Jval-(I('.043')/(2*I('.5'))+1/I('2.26'))*Jval**2
                candidates.append(val)
    mn=I.raw(min(v.lo for v in candidates),min(v.hi for v in candidates))
    pointwise.append(mn.json());record(f'H J margin zrow {zi}',F(claimed[zi],1000),mn)

result={'passed':sum(z['pass'] for z in checks),'failed':sum(not z['pass'] for z in checks),'checks':checks,'tail_vectors':{name:[str(v) for v in vec] for name,vec in [('K',E_K[:3]),('d',Ed[:3]),('C',Ec)]},'pointwise_margins':pointwise}
Path(__file__).with_name('scalar-algebra-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed':result['passed'],'failed':result['failed'],'failures':[z for z in checks if not z['pass']]},indent=2))
