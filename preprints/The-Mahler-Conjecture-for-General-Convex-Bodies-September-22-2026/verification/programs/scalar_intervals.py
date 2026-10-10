"""Reproduce scalar certificates using integer, outward-rounded rational intervals.

No floating point or external special-function implementation enters the proof
checks. Endpoints are integers divided by SCALE. JSON decimal strings preserve
them exactly. The elementary-series rules are those specified in input.md.
"""
from fractions import Fraction
from math import isqrt, comb
import json
from pathlib import Path

SCALE=10**70
def ceildiv(a,b): return -((-a)//b)
class I:
    def __init__(self,a,b=None,raw=False):
        if raw: self.lo,self.hi=a,b; return
        a=Fraction(str(a)); b=a if b is None else Fraction(str(b))
        self.lo=(a.numerator*SCALE)//a.denominator
        self.hi=ceildiv(b.numerator*SCALE,b.denominator)
    @classmethod
    def raw(cls,a,b): return cls(a,b,True)
    def __add__(a,b):
        b=iv(b); return I.raw(a.lo+b.lo,a.hi+b.hi)
    __radd__=__add__
    def __neg__(a): return I.raw(-a.hi,-a.lo)
    def __sub__(a,b): return a+-iv(b)
    def __rsub__(a,b): return iv(b)+-a
    def __mul__(a,b):
        b=iv(b); p=[a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi]
        return I.raw(min(p)//SCALE,ceildiv(max(p),SCALE))
    __rmul__=__mul__
    def inv(a):
        assert a.lo>0 or a.hi<0
        return I.raw(SCALE*SCALE//a.hi,ceildiv(SCALE*SCALE,a.lo))
    def __truediv__(a,b): return a*iv(b).inv()
    def __rtruediv__(a,b): return iv(b)*a.inv()
    def __pow__(a,n):
        assert n>=0 and isinstance(n,int)
        if n==0:return I(1)
        if n%2==0:
            lo=0 if a.lo<=0<=a.hi else min(abs(a.lo),abs(a.hi))**n
            hi=max(abs(a.lo),abs(a.hi))**n
        else:lo,hi=a.lo**n,a.hi**n
        den=SCALE**(n-1)
        return I.raw(lo//den,ceildiv(hi,den))
    def sqrt(a):
        assert a.lo>=0
        lo=isqrt(a.lo*SCALE); hi=isqrt(a.hi*SCALE)
        if hi*hi<a.hi*SCALE:hi+=1
        # The submission specifies consecutive multiples of 10^-26.
        quantum=10**44
        lo=(lo//quantum)*quantum; hi=ceildiv(hi,quantum)*quantum
        return I.raw(lo,hi)
    def positive(a):return I.raw(max(0,a.lo),max(0,a.hi))
    def abs(a):return I.raw(0 if a.lo<=0<=a.hi else min(abs(a.lo),abs(a.hi)),max(abs(a.lo),abs(a.hi)))
    def intersect(a,b):
        b=iv(b); lo,hi=max(a.lo,b.lo),min(a.hi,b.hi)
        assert lo<=hi
        return I.raw(lo,hi)
    def json(a):return [decimal(a.lo),decimal(a.hi)]
def iv(x):return x if isinstance(x,I) else I(x)
def decimal(n):
    sign='-' if n<0 else ''; n=abs(n)
    return sign+str(n//SCALE)+'.'+str(n%SCALE).zfill(70)
def sym(x): x=iv(x); return I.raw(-x.hi,x.hi)
def exp26(x):
    x=iv(x); term=I(1); total=term
    for m in range(1,27):term=term*x/m; total=total+term
    return total+I('-1e-27','1e-27')
def logseries(z):
    y=(z-1)/(z+1); total=I(0)
    for m in range(25):total=total+2*y**(2*m+1)/(2*m+1)
    err=2*y.abs()**51/(51*(1-y**2))
    return total+sym(err)
LOG2=logseries(I(2))
def log(z):
    z=iv(z); assert z.lo>0; k=0
    while z.lo<SCALE:z=z*2;k-=1
    while z.lo>=2*SCALE:z=z/2;k+=1
    assert z.hi<=I('2.01').hi
    return logseries(z)+k*LOG2
PI=I('3.14159265358979323846264338','3.14159265358979323846264339')
ROOT2PI=(2*PI).sqrt(); LOGROOT2PI=log(2*PI)/2
b,c,k,r,s,w=I('.602'),I('.365'),I('.237').sqrt(),I('.22'),I('3.6'),I('4.6')
tc,tr,ms,lam=I('.021'),I('.043'),I('.352'),I('.65')

def sample(i):
    E=exp26(I(i)/160)**4
    x=(s*(E-1/E)/2).intersect(I(0,90)); a=s*(E+1/E)/2
    phi=exp26(-x**2/128)**64/ROOT2PI if i<=73 else I(0,'1e-26')
    if i<=30:
        term=x; total=I(0)
        for m in range(40):
            total=total+term/(2*m+1); term=-term*x**2/(2*m+2)
        L=total+I.raw(0,(term/81).hi)
        Y=(I('.5')-L/ROOT2PI)/phi
    else:
        T=I.raw(0,(34/x).hi)
        for m in range(33,0,-1):T=m/(x+T)
        Y=1/(x+T)
    u=(Y*phi).intersect(I(0,'.5')); p=1-u
    h=sum((u**m/(m+2) for m in range(45)),I(0))+I.raw(0,(2*u**45/47).hi)
    B=1-x*Y; j=x**2/2+LOGROOT2PI-log(Y)-p
    d=B**2*j+(1-p*B)**2*h
    K=d+Y**2*(j+p**2*h)-1
    gp=Y*(B*j-(1-p*B)*p*h); gpp=x*gp-K
    C=-d+I('6.5')*gpp
    Rv=phi/p-B/Y; V2=2-(phi/p)*(x+phi/p)-B/Y**2
    D1=x*(2*d-1)-Rv-2*gp; D2=2*d+2*x*D1-2*gpp-V2
    G3=x*gpp+3*gp-D1; G4=x*G3+4*gpp-D2
    out={'x':x,'a':a,'d':d,'K':K,'C':C,'Rv':Rv,'V2':V2}
    for name,P,Q in [('d',D1,D2),('K',D1-2*gp,D2-2*gpp),('C',-D1+I('6.5')*G3,-D2+I('6.5')*G4)]:
        out['dot_'+name]=a*P; out['ddot_'+name]=a**2*Q+x*P; out['n_'+name]=a**2*Q
    ell=(b-r**2-d).sqrt(); q=k-ell
    dq=out['dot_d']/(2*ell); ddq=(out['ddot_d']/2+dq**2)/ell; nq=(out['n_d']/2+dq**2)/ell
    Sq=2*q+x/a*(1+1/a**2)*dq-ddq/a**2
    rho=r*((2+w**2/a**2)**2+(1+1/a**2)**2*w**2*x**2/a**2).sqrt()
    Us=I('1.507')*(-out['n_K']).positive()+12*I('.80')/ms**2*(I('1.25')*(out['dot_K']+tc*out['dot_C'])**2+5*tr**2*out['dot_C']**2)
    out.update(q=q,dot_q=dq,ddot_q=ddq,n_q=nq,Sq=Sq,rho=rho,Us=Us,
               tm=lam*I('-.022')**2+I('-.022')*C+K,
               tp=lam*I('.064')**2+I('.064')*C+K,
               disc=-I('.74')*C-I('.37')**2-4*lam*K)
    return out

def main():
    samples=[sample(i) for i in range(152)]
    path=Path(__file__).with_name('scalar-samples.json')
    path.write_text(json.dumps({'scale':str(SCALE),'method':'outward rational fixed-grid interval arithmetic','samples':[{n:v.json() for n,v in z.items()} for z in samples]},indent=2)+'\n')
    checks=[]
    def check(name,got,lo=None,hi=None):
        ok=(lo is None or got.lo>=I(lo).lo) and (hi is None or got.hi<=I(hi).hi)
        checks.append({'name':name,'pass':ok,'enclosure':got.json(),'claimed':[lo,hi]})
    def hull(vs):return I.raw(min(v.lo for v in vs),max(v.hi for v in vs))
    table=[('d','.3862','.5','.000260',None),('dot_d','-.1338','.1338','.00092','.01037'),('ddot_d','-.415','.415','.00421','.03670'),('K','-.00692','.02737','.000148',None),('dot_K','-.06542','.06542','.000673',None),('ddot_K','-.2355','.2355','.00373',None),('n_K','-.2355','.2355','.00402',None),('C','-.5','-.3413','.00049',None),('dot_C','-.2456','.2456','.00222',None),('ddot_C','-.780','.780','.0129',None),('n_C','-.780','.780','.0138',None),('Rv','-.318','.318','.00167',None),('V2','-1.06','1.06','.00186',None),('q','.0777','.25525',None,None),('dot_q','-.1908','.1908',None,'.0127'),('ddot_q','-.508','.508',None,'.047'),('n_q','-.508','.508',None,None)]
    for name,lo,hi,sec,first in table:
        vals=[z[name] for z in samples]; check(name+' values',hull(vals),lo,hi)
        if sec:
            refl=-vals[1] if name.startswith('dot_') or name=='Rv' else vals[1]
            v=[refl]+vals
            check(name+' second differences',hull([(v[i+1]-2*v[i]+v[i-1]).abs() for i in range(1,len(v)-1)]),'0',sec)
        if first:check(name+' first differences',hull([(vals[i+1]-vals[i]).abs() for i in range(151)]),'0',first)
    for name,lo,hi in [('Us',None,'.537'),('tm','.00090',None),('tp',None,'-.00074'),('disc','.132',None)]:check(name,hull([z[name] for z in samples]),lo,hi)
    for name,lo,hi in [('K','0','.019'),('dot_K','-.0207','.0207'),('n_K','.00315',None),('C','-.5','-.49512'),('dot_C','-.0071','.0071'),('q','.2353',None)]:check(name+' 56:144',hull([z[name] for z in samples[56:145]]),lo,hi)
    check('q 45:144',hull([z['q'] for z in samples[45:145]]),'.2204',None)
    for ix,bound in [(56,'.126'),(144,'.335')]:
        val=samples[ix]['x']*(samples[ix]['K'].positive()+I('.238')/12800)
        val=val-40*sum(((samples[j]['a']-samples[j-1]['a'])*(samples[j]['K'].positive()-samples[j-1]['K'].positive()) for j in range(1,ix+1)),I(0))
        check('positive-part integral '+str(ix),val,None,bound)
    rows=[(0,4,77,81,113,132,725,743,804),(4,8,80,88,125,166,740,785,814),(8,12,87,100,159,220,782,848,831),(12,16,99,116,213,288,845,920,853),(16,20,115,134,281,359,917,986,877),(20,28,133,171,352,464,983,1055,927),(28,40,170,211,457,504,1041,1059,992),(40,68,210,245,497,513,1009,1044,1072),(68,144,244,256,506,514,999,1012,1104)]
    for row in rows:
        a,b,qlo,qhi,slo,shi,vlo,vhi,rhi=row
        for name,lo,hi,err in [('q',qlo,qhi,'.000042'),('Sq',slo,shi,'.003'),('V2',vlo,vhi,'.00101')]:
            check(f'{name} row {a}:{b}',hull([z[name] for z in samples[a:b+1]])+I('-'+err,err),str(Fraction(lo,1000)),str(Fraction(hi,1000)))
        check(f'rho row {a}:{b}',samples[b]['rho'],None,str(Fraction(rhi,1000)))
    result={'checks':checks,'passed':sum(z['pass'] for z in checks),'failed':sum(not z['pass'] for z in checks)}
    Path(__file__).with_name('scalar-interval-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'passed':result['passed'],'failed':result['failed'],'failures':[z for z in checks if not z['pass']]},indent=2))
if __name__=='__main__':main()
