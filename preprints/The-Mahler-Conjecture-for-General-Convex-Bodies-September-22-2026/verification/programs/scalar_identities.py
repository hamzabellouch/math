"""Independent formal differentiation of the submitted original profiles."""
import sympy as S
from pathlib import Path
import json
x,p,phi=S.symbols('x p phi',real=True)
def derivative(f):return S.diff(f,x)+phi*S.diff(f,p)-x*phi*S.diff(f,phi)
def N(f):return x*derivative(f)-derivative(derivative(f))
X=p/phi;Y=(1-p)/phi;f=-(1-p)-S.log(p);j=-p-S.log(1-p)
d=(1+x*X)**2*f+(1-x*Y)**2*j
g=(1-X**2*f-Y**2*j)/2
v=S.log(X*Y)
checks={
    '(N+2)g=d':N(g)+2*g-d,
    'dprime=2xd-vprime-2gprime':derivative(d)-2*x*d+derivative(v)+2*derivative(g),
    'Nd-vsecond=-(N+2)(d+gsecond)':N(d)-derivative(derivative(v))+N(d+derivative(derivative(g)))+2*(d+derivative(derivative(g))),
}
result={name:bool(S.simplify(S.together(expr))==0) for name,expr in checks.items()}
Path(__file__).with_name('scalar-identity-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2)); assert all(result.values())
