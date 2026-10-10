#!/usr/bin/env python3
"""Exact rational verification of the paper's numerical inequalities.

Python standard library only. Run without -O: assertions are the checks.
The finite logarithm and exponential bounds are described in CERTIFICATES.md.
All arithmetic entering assertions is rational or integral; decimal displays
are explanatory only. This script does not certify the structural tensor proof.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib,json
if not __debug__:
    raise SystemExit('Run without -O: this checker uses assertions.')

def log_bounds(q):
    q=F(q); assert q>0
    a=0
    while q>2:q/=2;a+=1
    while q<1:q*=2;a-=1
    def unit(x):
        s=(x-1)/(x+1)
        low=2*sum((s**(2*j+1)/F(2*j+1) for j in range(8)),F(0))
        high=low+2*s**17/(17*(1-s*s))
        return low,high
    lo,hi=unit(q);l2,h2=unit(F(2))
    if a>=0:return lo+a*l2,hi+a*h2
    return lo+a*h2,hi+a*l2
def dec(q):return float(q)
def assert_log(q,lo,hi):
    a,b=log_bounds(q)
    assert F(lo)<a<=b<F(hi),(q,float(a),float(b),lo,hi)
def exp_neg_partial(x,n):
    # 0 <= x <= 1 makes term magnitudes decrease. Odd partial sums are
    # lower bounds and even partial sums are upper bounds for exp(-x).
    assert 0 <= F(x) <= 1
    term=F(1);value=term
    for k in range(1,n+1):term*= -F(x)/k;value+=term
    return value

# Listed elementary logarithm bounds, all certified by the submitted series.
for args in [('2','.69314','.69316'),('3','1.098','1.0987'),
             ('19','2.9444','2.9445'),('49.2878','3.89765','3.89772'),
             ('49.2890','3.89765','3.89772'),('9/7','.250','.252')]:
    assert_log(*args)
assert log_bounds(F(10))[0]>F('2.3025')
assert log_bounds(F('2.95'))[0]>F('1.0817')

# Seven-completion dual-exponent certificate using only rational enclosures.
rho8=1-F(3,4)**4;rho24=rho8**3
assert F('.3194')<rho24<F('.3195')
delta_factor=3*(1-rho8)/(1-rho24)
assert F('.348')<delta_factor*F('.250')
assert delta_factor*F('.252')<F('.354')
rho48=1-(1-rho24)**2
assert 1-rho48>F('.463')
assert F('.536')<rho48<F('.537')
assert exp_neg_partial(F('.354'),7)>F('.701')
assert exp_neg_partial(F('.348'),6)<F('.707')
assert log_bounds((1+F('.701'))**2-1)[0]>F('.635')
assert log_bounds((1+F('.707'))**2-1)[1]<F('.651')
assert 2*F('.651')/(1+rho48)<F('.86')
rho96=rho48**2
rho288=1-(1-rho96)**3
assert 1-rho288>F('.360')
assert exp_neg_partial(F('.86'),7)>F('.4225')
assert log_bounds((1+F('.4225'))**3-1)[0]>F('.628')
alpha_lower=2/F('.6932')*(F('.5625')*F('1.098')/4+
                         F('.463')*F('.635')/48+
                         F('.360')*F('.628')/288)
assert alpha_lower>F('.465')
assert alpha_lower == F(1548637,3327360)

# t=2/3 point with rational enclosures for cube roots and logarithms.
ul,uh=F('1.58739'),F('1.58742')
vl,vh=F('7.1203'),F('7.1205')
assert ul**3<4<uh**3 and vl**3<19**2<vh**3
zl=8+12*ul+6*ul**2+vl
zh=8+12*uh+6*uh**2+vh
assert F('49.2878')<zl<zh<F('49.2890')
l2,h2=log_bounds(F(2));l19,h19=log_bounds(F(19))
gl=(12*ul*(1+ul)*l2+vl*l19)/zh
gh=(12*uh*(1+uh)*h2+vh*h19)/zl
assert F('1.11844')<gl<=gh<F('1.11856')
hl=F('3.89765')-F(2,3)*F('1.11856')
hh=F('3.89772')-F(2,3)*F('1.11844')
assert F('3.1519')<hl<hh<F('3.1522')
k_lower=2*F('1.11844')/F('3.1522')
w_upper=6*F('1.0987')/F('3.1519')
assert k_lower>F('.709') and w_upper<F('2.092')

# Square witness uses exact monomial counts.
d=[2,2,1];stages=[]
for center,m in [(0,2),(1,3),(2,2),(0,2),(1,3)]:
    old=d;d=[old[center]**m if j==center else
             (old[center]+old[j])**m-old[center]**m for j in range(3)]
    stages.append(d)
assert stages[2]==[20691584,13993344,10144225]
assert all(a>=10**12*b for a,b in zip(stages[3],[428,774,522]))
N=d[0]+d[2]
nlower=10**36*(1202**3+1296**3-2*774**3)
assert N>=nlower>F('2.95')*10**45
square_upper=216*F('1.0987')/(F('1.0817')+45*F('2.3025'))
assert square_upper<F('2.267')

# Supporting-plane comparisons at every grouped endpoint claimed in the table.
v=F('.258')/F('.55');u=1-F('.45')*v/2
assert 0<v<u<1
def plane(k):
    k=F(k)
    return 2+v*(k-F('.45')) if k<=1 else u*(1+k)+v
rows=[('.5','2.04'),('.527','2.05'),('.528','2.05'),('.55','2.06'),
('.60','2.09'),('.65','2.12'),('.7','2.12'),('.75','2.18'),('.8','2.18'),
('.85','2.24'),('.9','2.24'),('.95','2.24'),('1','2.36'),
('1.1','2.44'),('1.2','2.44'),('1.5','2.71'),('2','3.16'),
('2.5','3.60'),('3','4.05')]
margins={k:F(e)-plane(k) for k,e in rows}
assert min(margins.values())>0
def interp(x,x0,y0,x1,y1):
    return F(y0)+(F(x)-F(x0))*(F(y1)-F(y0))/(F(x1)-F(x0))
shortcut={
'.465':F(2),
'.709':F('2.092'),
'.93':interp('.93','.709','2.092','1','2.267')}
slack={k:plane(k)-w for k,w in shortcut.items()}
assert min(slack.values())>0
out={'status':'passed','arithmetic':'exact fractions and integers',
'scope':'Numerical certificate inequalities only; no certification of tensor extraction or completeness of literature baseline.',
'alpha_lower_from_stated_certificate':str(alpha_lower),'alpha_lower_decimal':dec(alpha_lower),
'curve_k_lower_exact':str(k_lower),'curve_k_lower':dec(k_lower),
'curve_w_upper_exact':str(w_upper),'curve_w_upper':dec(w_upper),
'square_count':str(N),'square_w_upper_from_stated_certificate':dec(square_upper),
'square_w_upper_exact':str(square_upper),
'baseline_rounding_margins_exact':{k:str(x) for k,x in margins.items()},
'baseline_rounding_margins':{k:dec(x) for k,x in margins.items()},
'new_shortcut_to_baseline_margins_exact':{k:str(x) for k,x in slack.items()},
'new_shortcut_to_baseline_margins':{k:dec(x) for k,x in slack.items()},
'log_series_terms':8}
out['script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
rendered=json.dumps(out,indent=2,sort_keys=True)+'\n'
Path(__file__).with_suffix('.json').write_text(rendered,encoding='utf-8')
print(rendered,end='')
