#!/usr/bin/env python3
"""Arb enclosures of the finite matrices, residuals and Bernstein coefficients.

Inputs are the public mathematical manifest and displayed integer tables.
Call run_certificate(); importing this module does not run a certificate.
"""
from pathlib import Path
from math import comb
from types import SimpleNamespace
import json
import time

import flint
from flint import arb, acb, arb_mat, ctx
from certificate_data import load_data, provenance, write_result


def run_certificate():
    ctx.prec = 192
    ROOT = Path(__file__).resolve().parent
    source_data = load_data()
    SOURCE = source_data["source_path"]
    EXPECTED_SHA = source_data["source_sha256"]

    pi = arb.pi()
    b = arb(3).sqrt() / 2
    h = arb(2) / 5
    B = arb(4) / 3
    I = acb(0, 1)
    A = [0, 1, 3, 4, 7, 9]
    P = list(map(acb, [5, 0, 0, -2, 0, 0, 1]))
    P[1] = -1 + 2 * I * b
    P[2] = 1 + 2 * I * b
    P[4] = -arb(1) / 2 + I * b
    P[5] = -1 - 2 * I * b
    ts = [arb(j) / 6 for j in range(7)]
    ERR = arb(0, "1e-22")

    rows = source_data["rows"]
    nodes = [x[0] for x in rows]
    tab = [{n: (arb(row[1 + 2*i]) / 10**10, arb(row[2 + 2*i]) / 10**10)
            for n, row in zip(nodes, rows)} for i in range(2)]
    tab[0][0] = (arb(1), arb(44)/100)
    tab[1][0] = (arb(0), -arb(368)/1000)
    C = [-arb(13)/1000, arb(17)/1000]


    def enclose(x):
        """Human-readable ball; comparisons elsewhere use the full ball."""
        return str(x)


    def max_ball(items):
        items=list(items)
        out=items[0]
        for item in items[1:]:
            out=out.max(item)
        return out


    def assert_upper(x, bound, description):
        assert x < arb(str(bound)), (description, str(x), bound)


    def assert_lower(x, bound, description):
        assert x > arb(str(bound)), (description, str(x), bound)


    printed_brackets=[]

    def assert_printed_bracket(name,value,lower,upper):
        assert_lower(value,lower,name)
        assert_upper(value,upper,name)
        record={'name':name,'enclosure':enclose(value),'lower':lower,'upper':upper}
        printed_brackets.append(record)
        return record

    def exp_pi(t):
        return (I*pi*t).exp()


    Q, D = {}, {}
    for a in A:
        Q[a] = (pi/6)**2
        D[a] = arb(0)
        for d in A:
            if a == d:
                continue
            x = pi*(arb(a-d)/12)
            Q[a] *= (2*x.sin())**2
            D[a] += pi/6*x.cos()/x.sin()


    def make_grid():
        N = 256
        weights, xs = [], []
        for v in range(N):
            alpha = arb(2*v+1)/(2*N)
            weights.append((1-2*sum((2*a*pi*alpha).cos()/arb(4*a*a-1)
                                     for a in range(1,128)))/N)
            xs.append((pi*alpha).cos())
        assert all(w > 0 for w in weights)
        assert sum(weights).contains(1)
        grid = []
        for j in range(1,7):
            for x,w in zip(xs, weights):
                t = (2*j-1+x)/12
                z = -B/(acb(t)+I*h)-I*h
                lam = I/(b*(acb(t)+I*h))
                grid.append((j,t,w/6,z,lam))
        for j,t in enumerate(ts):
            z = -B/(acb(t)+I*h)-I*h
            lam = I/(b*(acb(t)+I*h))
            grid.append((0,t,arb(0),z,lam))
        return grid


    def basis_measure(n,kind):
        sums={}
        for j in range(1,7):
            phases=[P[l]*exp_pi(ts[l]*(n % 12)) for l in range(j,7)]
            aa=sum(phases)
            bb=sum(ts[l]*phases[l-j] for l in range(j,7))
            sums[j]=(aa,bb)
        result=[]
        for j,t,w,z,lam in grid:
            if j==0:
                result.append(acb(0))
                continue
            aa,bb=sums[j]
            phase=exp_pi(-t*n)
            density=-2*pi*pi*phase*(bb-t*aa) if kind==0 else 2*I*pi*phase*aa
            result.append(w*density)
        return result


    def table_measure(index):
        result=[acb(0) for _ in grid]
        for n,(c,d) in tab[index].items():
            for kind,coeff in enumerate((c,d)):
                if coeff==0:
                    continue
                basis=basis_measure(n,kind)
                result=[a+coeff*x for a,x in zip(result,basis)]
        for j in range(7):
            result[-7+j]=(1 if j==0 else 2)*C[index]*P[j]
        return result


    factor_cache={}


    def k_factors(m):
        if m not in factor_cache:
            f0=[lam*exp_pi(z*m) for _,t,w,z,lam in grid]
            f1=[v*I*pi*z for v,(_,t,w,z,lam) in zip(f0,grid)]
            factor_cache[m]=(f0,f1)
        return factor_cache[m]


    def pair(measure,m):
        f0,f1=k_factors(m)
        x0=sum(v*f for v,f in zip(measure,f0)).real+ERR
        x1=sum(v*f for v,f in zip(measure,f1)).real+ERR
        q,d=Q[m % 12],D[m % 12]
        return (-x0/q,(d*x0-x1)/q)


    def moments(measure,m,L):
        us=[acb(0) for _ in range(L+1)]
        ks=[acb(0) for _ in range(L+1)]
        for mass,(_,t,w,z,lam) in zip(measure,grid):
            u=mass*exp_pi(t*m)
            k=mass*lam*exp_pi(z*m)
            pu=I*pi*t
            pk=I*pi*z
            for ell in range(L+1):
                us[ell]+=u
                ks[ell]+=k
                u=u*pu/(ell+1)
                k=k*pk/(ell+1)
        return ([v.real+ERR for v in us],[v.real+ERR for v in ks])


    def norm1(mat):
        return max_ball([sum(abs(mat[i,j]) for i in range(mat.nrows()))
                         for j in range(mat.ncols())])


    start=time.time()
    grid=make_grid()
    measures=[table_measure(0),table_measure(1)]
    print("Built rigorous quadrature grid and both tabulated measures",flush=True)

    # Matrix columns in precisely the specified all-c, then all-d order.
    J=[1,3,4]
    E=[n for n in nodes if n not in J]
    cols=[(n,k) for k in range(2) for n in nodes]
    SJ=[]
    SJlow=[]
    for n,k in cols:
        mu=basis_measure(n,k)
        v=[pair(mu,m) for m in J]
        SJ.append([x[0] for x in v]+[x[1] for x in v])
        if n in J:
            low=[pair(mu,m) for m in E if m<=16]
            SJlow.append([x[0] for x in low]+[x[1] for x in low])
    jcols=[i for i,(n,k) in enumerate(cols) if n in J]
    ecols=[i for i,(n,k) in enumerate(cols) if n in E]
    dmat=arb_mat([[SJ[j][i] for j in jcols] for i in range(6)])
    umat=arb_mat([[SJ[j][i] for j in ecols] for i in range(6)])
    ident=arb_mat([[int(i==j) for j in range(6)] for i in range(6)])
    wp=arb_mat([[arb(x)/10000 for x in row] for row in source_data["W_plus"]])
    wm=arb_mat([[arb(x)/10000 for x in row] for row in source_data["W_minus"]])
    matrix_results=[]
    for sign,w in [(1,wp),(-1,wm)]:
        inv=(ident-sign*dmat).inv()
        invnorm=norm1(inv);cross=norm1(inv*umat)
        defect=norm1(ident-w*(ident-sign*dmat))
        assert_upper(invnorm,32,"inverse norm")
        assert_upper(cross,3.7,"cross norm")
        assert_upper(defect,.001,"W inverse defect")
        defect_bracket={1:('.00025422624910652544','.00025422624910652546'),
                        -1:('.00042288165102553355','.00042288165102553357')}[sign]
        assert_printed_bracket('W defect for sign '+str(sign),defect,*defect_bracket)
        wnorm=norm1(w)
        assert_upper(wnorm,'30.84' if sign==1 else '1.83',"W column norm")
        grouped_cross=[]
        group_bounds=('3.54','.44','.25') if sign==1 else ('.73','.32','.17')
        for (lo,hi),bound in zip(((7,9),(12,16),(19,100)),group_bounds):
            indices=[j for j,column in enumerate(ecols) if lo<=cols[column][0]<=hi]
            block=arb_mat([[umat[i,j] for j in indices] for i in range(6)])
            value=norm1(w*block)
            assert_upper(value,bound,('W grouped cross',sign,lo,hi))
            grouped_cross.append({'node_range':[lo,hi],'norm':enclose(value),'upper_bound':bound})
        matrix_results.append({'sign':sign,'inverse_norm':enclose(invnorm),'cross_norm':enclose(cross),'W_defect':enclose(defect),'W_norm':enclose(wnorm),'W_grouped_cross':grouped_cross})
    low_norm=max_ball([sum(abs(x) for x in v) for v in SJlow])
    assert_upper(low_norm,.088,"low exterior to J")
    assert_printed_bracket('low exterior norm',low_norm,
                           '.08688748182289641591','.08688748182289641592')
    print("Certified matrix and exterior-block bounds",flush=True)

    residuals=[]
    for i in range(2):
        for m in nodes:
            cc,dd=pair(measures[1-i],m)
            c,d=tab[i][m]
            r0=abs(c-cc);r1=abs(d+int(i==0 and m==1)-dd)
            assert_upper(r0,"3e-10","c residual")
            assert_upper(r1,"3e-10","d residual")
            residuals.append({'function':i+1,'node':m,'c':enclose(r0),'d':enclose(r1)})
    print("Certified tabulated residual bounds",flush=True)

    centers=[0]+[n for n in nodes if n<=40]
    all_moments={}
    for m in centers:
        all_moments[m]=[moments(measures[i],m,30) for i in range(2)]
    print("Computed interval Taylor coefficients at every sign-test center",flush=True)

    sign_results=[]
    bernstein_example=None
    sign_minima=[]
    full_nodes=[0]+nodes
    for m in centers:
        q=full_nodes.index(m)
        ys=[arb(full_nodes[q+1]-m)/2]
        if q>0:
            ys.append(arb(full_nodes[q-1]-m)/2)
        for y in ys:
            for i in range(2):
                if i==0 and (m==0 or (m==1 and y<0)):
                    continue
                nu=0 if m==0 else (1 if i==0 and m==1 else 2)
                sig=-1 if i==0 else 1
                direct=all_moments[m][i][0]
                transformed=all_moments[m][1-i][1]
                coeffs=[sig*y**r*(direct[r+nu]+transformed[r+nu]) for r in range(29)]
                bern=[sum(arb(comb(k,r))/comb(28,r)*coeffs[r] for r in range(k+1)) for k in range(29)]
                bound=.74 if m==0 else (.18 if m==1 else (.02 if m in (3,4) else .009))
                for k,value in enumerate(bern):
                    assert_lower(value,bound,('Bernstein',i+1,m,str(y),k))
                if i==1 and m==16 and y==-arb(1)/2:
                    record=assert_printed_bracket('Bernstein (2,16,-1/2,28)',bern[28],
                                                  '.00951875955680','.00951875955684')
                    bernstein_example={'function':2,'node':16,'y':'-0.5','k':28,**record}
                minimum=-max_ball([-value for value in bern])
                sign_minima.append((i+1,m,minimum))
                sign_results.append({'function':i+1,'node':m,'y':enclose(y),'minimum':enclose(minimum),'required_lower_bound':bound})
    assert bernstein_example is not None
    assert len(printed_brackets)==4
    print("Certified individual Bernstein coefficient bounds",flush=True)

    # Exact counterparts of every grouped lower bound in the source table.
    group_specs=[([0],None,'.762'),([1],'.314','.191'),([3,4],'.028','.024'),
                 ([7,9],'.114','.112'),([12,13,15,16],'.0105','.0094'),
                 ([19,21],'.123','.113'),([24,25,27,28],'.0111','.0113'),
                 ([31,33],'.121','.126'),([36,37,39,40],'.0107','.0115')]
    grouped_bernstein=[]
    for group,bound1,bound2 in group_specs:
        for i,bound in enumerate((bound1,bound2),1):
            if bound is None:
                continue
            values=[value for function,node,value in sign_minima if function==i and node in group]
            value=-max_ball([-v for v in values])
            assert_lower(value,bound,('grouped Bernstein',i,group))
            grouped_bernstein.append({'function':i,'nodes':group,'minimum':enclose(value),'lower_bound':bound})

    result={'source_sha256':EXPECTED_SHA,'status':'pass','method':'Arb balls for the exact cosine quadrature, enlarged by 1e-22 per moment for the analytic quadrature remainder','python_flint_version':flint.__version__,'precision_bits':ctx.prec,'elapsed_seconds':time.time()-start,'matrix_bounds':matrix_results,'low_exterior_norm':enclose(low_norm),'residuals':residuals,'Bernstein_intervals':sign_results,'quadrature_moment_error_added':'1e-22'}
    # Explicit coverage assertions prevent an accidentally shortened run passing.
    assert nodes == [n for n in range(1,101) if n % 12 in A]
    assert len(cols)==102 and len(jcols)==6 and len(ecols)==96
    assert dmat.nrows()==dmat.ncols()==6
    assert umat.nrows()==6 and umat.ncols()==96
    assert len(SJlow)==6 and all(len(column)==12 for column in SJlow)
    assert len(residuals)==102
    assert {(r["function"],r["node"]) for r in residuals} == {(i,m) for i in (1,2) for m in nodes}
    assert len(centers)==22 and len(sign_results)==84
    assert sum(r["function"]==1 for r in sign_results)==41
    assert sum(r["function"]==2 for r in sign_results)==43
    assert len({(r["function"],r["node"],r["y"]) for r in sign_results})==84
    result["coverage"]={"finite_nodes":51,"matrix_signs":2,"residual_pairs":102,
                        "sign_centers":22,"half_gap_intervals":84,
                        "function_1_intervals":41,"function_2_intervals":43,
                        "Bernstein_inequalities":84*29}
    result['grouped_Bernstein_bounds']=grouped_bernstein
    result['printed_brackets']=printed_brackets
    result['Bernstein_example']=bernstein_example
    result.update(provenance(source_data, __file__))
    write_result("finite.json", result)
    print(json.dumps({'status':'pass','elapsed_seconds':result['elapsed_seconds'],'matrix_bounds':matrix_results,'residual_pairs':len(residuals),'sign_intervals':len(sign_results)},indent=2),flush=True)

    return SimpleNamespace(pi=pi,b=b,h=h,B=B,A=A,P=P,ts=ts,Q=Q,D=D,
                           tab=tab,C=C,exp_pi=exp_pi,ROOT=ROOT,SOURCE=SOURCE,
                           EXPECTED_SHA=EXPECTED_SHA,source_data=source_data,
                           result=result,dmat=dmat,umat=umat)


if __name__ == "__main__":
    run_certificate()
