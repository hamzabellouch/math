"""Exact symbolic checks of the profile formulas, scaling, and printed tables.

The companion original certificate remains unchanged. This independent audit
loads its definitions without running its certification driver.
"""
from pathlib import Path
from fractions import Fraction
from math import factorial,comb
import argparse,json,re,time
import sympy as s
if not __debug__:
    raise RuntimeError("Assertions must be enabled; run Python without -O.")
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output", type=Path, default=Path("profile_formula_audit.results.json"),
                    help="destination JSON file (default: current directory)")
args=parser.parse_args()
root=Path(__file__).resolve().parent
source=(root/'profile_certificate.py').read_text()
assert source.count('\nif len(rows)')==1
ns={}; exec(compile(source.split('\nif len(rows)')[0],str(root/'profile_certificate.py'),'exec'),ns)
m,x=s.symbols('m x'); D=10**8

def coeffs(q):
    return {ij:v for ij,v in s.Poly(q,m,x).terms() if v}
def expr(d):
    return sum(v*m**i*x**j for (i,j),v in d.items())
def ev(d,a,b):
    return sum(Fraction(v)*a**i*b**j for (i,j),v in d.items())
def beval(A,u,v):
    N=len(A)-1; K=len(A[0])-1
    um=[Fraction(comb(N,i))*u**i*(1-u)**(N-i) for i in range(N+1)]
    vm=[Fraction(comb(K,j))*v**j*(1-v)**(K-j) for j in range(K+1)]
    return sum(um[i]*sum(Fraction(w)*vm[j] for j,w in enumerate(row)) for i,row in enumerate(A))
start=time.monotonic(); prev=0; records=[]
for row,depth in zip(ns['rows'],ns['info']):
    endpoint=row[0]; group=next(g[1:] for g in ns['groups'] if g[0]>=endpoint)
    L,U,V,alpha,lam,mu=[s.Rational(v,1000) for v in group]
    P=1+s.Rational(1,D)*sum(c*(s.chebyshevt(j,m)-s.chebyshevt(j,0)) for j,c in enumerate(row[1:],1))
    B=s.Poly((1-m*m)*P,m,x)
    assert B.eval({m:0,x:0})==1 and B.eval({m:1,x:0})==0 and B.eval({m:-1,x:0})==0
    plus=s.Poly(B.as_expr().subs(m,m+x),m,x); minus=s.Poly(B.as_expr().subs(m,m-x),m,x)
    E,rem=s.div((B+s.Poly(B.as_expr().subs(m,-m),m,x))/2-1,s.Poly(m*m,m,x)); assert rem.is_zero
    C,rem=s.div(plus-minus,s.Poly(2*x,m,x)); assert rem.is_zero
    A,rem=s.div(2*B-plus-minus,s.Poly(2*x*x,m,x)); assert rem.is_zero
    J1=1-s.Rational(endpoint,1000)*C/(2*L)
    expected=[s.Poly(P,m,x),E,J1]
    for endpoint2 in (prev,endpoint):
        J=1-s.Rational(endpoint2,1000)*C/(2*L)
        expected.append(mu*J*J-A*(B+(2*alpha-1)*s.Poly(x,m,x)*C+(lam-1)*s.Poly(x*x,m,x)*A))
    actual,codeB=ns['make'](row[1:],group,prev,endpoint)
    scales=[D,D,2*group[0]*D,1000*(2*group[0])**2*D**2,1000*(2*group[0])**2*D**2]
    assert dict(codeB)==coeffs(D*B.as_expr())
    for i,(p,q,scale) in enumerate(zip(actual,expected,scales)):
        assert dict(p)==coeffs(scale*q.as_expr()),(endpoint,i,'symbolic mismatch')
        ends=[(-16,0),(-14,2),(-6,6),(6,6),(14,2),(16,0)]
        if i==0: boxes=[(-16,32,0,0,16)]
        elif i==1: boxes=[(0,1,0,0,1)]
        else: boxes=[(a,b-a,c,d-c,16) for (a,c),(b,d) in zip(ends,ends[1:])]
        for a,b,c,d,den in boxes:
            M=ns['bern'](p,a,b,c,d,den); N=len(M)-1; K=len(M[0])-1
            u,v=Fraction(2,7),Fraction(3,5)
            factor=den**N*factorial(N)*factorial(K)
            assert beval(M,u,v)==factor*ev(p,(a+b*u)/den,v*(c+d*u)/den),(endpoint,i,'bern')
            for axis in (0,1):
                children=ns['split'](M,axis); n=N if axis==0 else K
                for right,child in enumerate(children):
                    parent_u=(u+right)/2 if axis==0 and n else u
                    parent_v=(v+right)/2 if axis==1 and n else v
                    assert beval(child,u,v)==2**n*beval(M,parent_u,parent_v),(endpoint,i,axis,right,'split')
    records.append({'s0_thousandths':prev,'s1_thousandths':endpoint,'group':group,'degrees':[max(sum(ij) for ij in p) for p in actual],'x_degrees':[max(j for i,j in p) for p in actual]})
    print(f'row {endpoint}: symbolic formulas, scaling, Bernstein values, subdivisions pass',flush=True)
    prev=endpoint
assert prev==840
# Confirm the printed profile and six-column tables are identical to code data.
text=(root/'data'/'profile_tables.txt').read_text()
blocks=re.findall(r'```(?:[^\n]*)\n(.*?)```',text,re.S)
profile_blocks=[block for block in blocks if block.startswith('5   26797227')]
assert len(profile_blocks)==1
assert ns['data'](profile_blocks[0])==ns['rows']
table_blocks=[block for block in blocks if block.startswith('1000s_1')]
assert len(table_blocks)==1
assert ns['data']('\n'.join(table_blocks[0].splitlines()[1:]))==ns['info']
print('printed tables match code data')
args.output.write_text(json.dumps({'status':'pass','wall_seconds':time.monotonic()-start,'sympy_version':s.__version__,'rows':records},indent=2)+'\n')
print('pass')
