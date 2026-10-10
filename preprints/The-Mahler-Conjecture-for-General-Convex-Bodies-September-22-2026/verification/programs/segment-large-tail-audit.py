"""Independent arithmetic audit of input.md tail segment estimates, lines 883-913.
No dependencies beyond Python's standard library. Decimal inputs are exact.
Square-root evaluations are only for displaying values; claimed circle bounds
are additionally checked by comparisons of squares of rational quantities.
"""
from fractions import Fraction as F
from decimal import Decimal, getcontext
from itertools import product
getcontext().prec = 60

def q(s): return F(str(s))
def dec(x): return Decimal(x.numerator) / Decimal(x.denominator)
def show(s, x): print(s, dec(x))
r=q('.22'); w=q('4.6'); tc=q('.021'); tr=q('.043')
tp=q('.064'); lam=q('.65'); ms=q('.352'); G=r*r*w*w

# Circumference estimates use only the rational sinh/coth bounds in the text.
for s,c,fmin,pamin,pamax,pdmax in [
    ('1.335','1.25','.0449','.0818','.1074','.0132'),
    ('1.904','1.13','.0456','.0830','.1062','.0129')]:
    s,c,fmin,pamin,pamax,pdmax=map(q,(s,c,fmin,pamin,pamax,pdmax))
    fl=r*r/(1+w*w)*(w*w-1/s**2)
    assert fl > fmin
    # p_a extrema are 2r^2[1-(1 +/- sqrt(1+w^2 c^2))/(2(1+w^2))].
    root2=1+w*w*c*c
    lower_cap=2*(1+w*w)*(1-pamin/(2*r*r))-1
    upper_cap=2*(1+w*w)*(pamax/(2*r*r)-1)+1
    assert lower_cap > 0 and lower_cap**2 > root2
    assert upper_cap > 0 and upper_cap**2 > root2
    # |p_d| <= r^2(c+sqrt(c^2+w^2))/(1+w^2).
    pd_cap=pdmax*(1+w*w)/(r*r)-c
    assert pd_cap > 0 and pd_cap**2 > c*c+w*w
    show('circle variance lower bound',fl)

for intervals,o,kbar,claim in [
    ((('-.007','.0275'),('0','.0008')),'.160','.0084','.0144'),
    ((('-.0001','.0191'),('-.0001','.0191')),'.006','.0275','.0277')]:
    o,kbar,claim=map(q,(o,kbar,claim))
    vals=[]
    for a,b in product(*intervals):
        a,b=map(q,(a,b))
        gamma=q('.80')/ms**2*(q('1.25')*(abs(b-a)+tc*o)**2+5*tr**2*o**2)
        vals.append(kbar-(a+b)/2+gamma)
    val=max(vals)
    assert val < claim
    show('endpoint vertex maximum e_K + Gamma',val)

bplus=q('.0356')**2+10/(q('65.8')-q('6.86'))*(q('.1784')**2-q('.0356')**2)
assert bplus < q('.0068')
show('first-tail b_plus bound',bplus)

for row,claim in [
    (('.0449','.0818','.1074','.0132','-.081','.160','.080','.0194','.016'),'.018'),
    (('.0456','.0830','.1062','.0129','-.006','.160','.003','.032','.016'),'.031')]:
    f,pl,pu,pd,cl,cu,cd,ba,bd=map(q,row)
    square=max(abs(cl-pu-ba),abs(cu-pl))**2+(cd+pd+bd)**2
    budget=(1+tp)*f-square/(4*lam)-tp*(pu+ba)
    assert budget > q(claim)
    show('budget remaining after square and t_plus terms',budget)

smallgamma=q('.80')/ms**2*(q('1.25')*(2*(q('.0211')+tc*q('.0084')))**2+5*tr**2*(2*q('.0084'))**2)/q('.18')
largegamma=q('.80')/ms**2*(q('1.25')*(q('.0192')+tc*q('.006'))**2+5*tr**2*q('.006')**2)/q('.0332')
assert max(smallgamma,largegamma)<q('.10')
show('same-tail small-h Gamma/f upper bound',smallgamma)
show('same-tail large-h Gamma/f upper bound',largegamma)

def flratio(h):
    return (1-2*w**4*h*h/(15*(1+w*w)))/(1+h*h/3)
assert flratio(q('.4'))*G/3 > q('.18')
assert flratio(q('.16'))*G*q('.16')**2/3 > q('.008')
assert (4+q('.15')*q('.3')**2+2*q('.3'))/flratio(q('.3')) < q('6.65')
assert r*r/(1+w*w)*(w*w-1/q('.410')**2)>q('.0332')
assert r*r/(1+w*w)*(w*w-1/q('.304')**2)>q('.02256')
assert q('.150')/q('.02256')<q('6.65')

# For c=coth(.3)<3.434, bound the two radical terms separately by rationals.
c=q('3.434'); aroot=q('15.829'); broot=q('5.741')
assert aroot**2>1+w*w*c*c and broot**2>c*c+w*w
sumcap=2*r*r*(1-(1-aroot)/(2*(1+w*w)))+r*r*(c+broot)/(1+w*w)
assert sumcap<q('.150')
show('same-tail p_a+|p_d| rational upper bound',sumcap)

# Exact rational conservative bound for final radicals.
# sqrt(.150*6.65)<.999 and .00645/sqrt(.008)<.073.
assert q('.999')**2>q('.150')*q('6.65')
assert q('.073')**2*q('.008')>q('.00645')**2
final=q('.10')+(q('.999')+q('.073'))**2/(4*lam)+tp*(q('6.65')+q('.00045')/q('.008'))
assert final < 1+tp
show('same-tail final normalized upper bound (rationally rounded)',final)
print('All exact rational checks passed.')
