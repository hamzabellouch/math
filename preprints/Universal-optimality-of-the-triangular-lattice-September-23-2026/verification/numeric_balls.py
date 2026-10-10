#!/usr/bin/env python3
"""Strict Arb verification of the triangular-energy finite inequalities.

Run: python verification/numeric_balls.py --output-dir build/verification
The public manifest binds the article and checker sources. Numerical arrays
are reconstructed from the encoded formulas, not loaded from the manifest.
The executed route encloses exact quadrature, without floor-matrix emulation.
"""
import contextlib
import json
import math
import sys
import time
import traceback

sys.dont_write_bytecode = True
from inputs import (managed_output, parse_options, recheck_inputs, run_metadata)


class Tee:
    """Mirror progress and summary output into the run log."""
    def __init__(self, *streams):
        self.streams = streams

    def write(self, value):
        for stream in self.streams:
            stream.write(value)
        return len(value)

    def flush(self):
        for stream in self.streams:
            stream.flush()


def initialize_numerics():
    # Called only after source integrity and exact dependency-version checks.
    global arb, acb, arb_mat, acb_mat, ctx
    global N, M, nodes, nf, nn, cols, p, b, h, B, ii, P, started, ENDPOINTS, BOXES
    from flint import arb, acb, arb_mat, acb_mat, ctx
    ctx.prec = 256
    N, M = 384, 168
    nodes = [n for n in range(1,M+1) if n%12 in [0,1,3,4,7,9]]
    nf = len(nodes)
    nn = 2*nf
    cols = nn+3
    p = arb.pi()
    b = arb(3).sqrt()/2
    h = arb(2)/5
    B = arb(4)/3
    ii = acb(0,1)
    P = [acb(5), acb(-1,2*b), acb(1,2*b), acb(-2), acb(-arb(1)/2,b), acb(-1,-2*b), acb(1)]
    started = time.monotonic()

    ENDPOINTS=['2.36','2.65','3.2','4','6',None]
    BOXES=[]
    for Ks,Js in zip(ENDPOINTS,ENDPOINTS[1:]):
        K=dec(Ks); J=dec(Js) if Js is not None else None
        expK=[(-K*d).exp() for d in [0,2,3,6,8]]
        expJ=[(-J*d).exp() if J is not None else arb(int(d==0)) for d in [0,2,3,6,8]]
        BOXES.append((K,J,[1/K,1/J if J is not None else arb(0)],expK,expJ))


def progress(label):
    print(json.dumps(dict(stage=label,elapsed_seconds=time.monotonic()-started)),flush=True)

def dec(x):
    """Finite decimal to a rational enclosure, without binary float input."""
    return arb(str(x))

def show(x):
    return x.str(35,radius=True)

def require(condition,label):
    if not condition: raise AssertionError(label)

def ball_min(xs):
    ans=xs[0]
    for x in xs[1:]: ans=ans.min(x)
    return ans

def ball_max(xs):
    ans=xs[0]
    for x in xs[1:]: ans=ans.max(x)
    return ans

def norm1(A):
    return ball_max([sum((abs(A[i,j]) for i in range(A.nrows())),arb(0)) for j in range(A.ncols())])

def constants(n):
    a=n%12
    if a in [0,4]: Q=p*p/3
    elif a in [1,3]: Q=2*p*p/3*(2-2*b)
    else: Q=2*p*p/3*(2+2*b)
    D={0:-7*p*2*b/18,1:p*(3+2*b)/18,3:-p*(3+2*b)/18,
       4:7*p*2*b/18,7:-p*(3-2*b)/18,9:p*(3-2*b)/18}[a]
    return Q,D

def build():
    # Degree-383 cosine quadrature, all 384 weights certified positive.
    alpha=[arb(2*v+1)/(2*N) for v in range(N)]
    weights=[(1-2*sum(((2*d*p*a).cos()/(4*d*d-1) for d in range(1,N//2)),arb(0)))/N for a in alpha]
    for o in weights: require(o>0,'quadrature weight positivity')
    require(sum(weights,arb(0)).contains(1),'quadrature weight sum contains 1')
    tau=[[(2*j-1+(p*a).cos())/12 for a in alpha] for j in range(1,7)]
    ts=[t for block in tau for t in block]+[arb(j)/6 for j in range(7)]
    nt=len(ts)
    W=acb_mat(nt,cols)
    # Node phases repeat modulo 12; cache the exact same ball expressions.
    spec={(a,l):P[l]*(ii*p*l*a/6).exp() for a in [0,1,3,4,7,9] for l in range(1,7)}
    for j in range(1,7):
        coeff={}
        for a in [0,1,3,4,7,9]:
            sd=sum((spec[a,l] for l in range(j,7)),acb(0))
            sc=sum((arb(l)/6*spec[a,l] for l in range(j,7)),acb(0))
            coeff[a]=(sd,sc)
        for v,t in enumerate(tau[j-1]):
            row=(j-1)*N+v
            scale=weights[v]/6*2*p
            for ni,n in enumerate(nodes+[0]):
                sd,sc=coeff[n%12]
                av=scale*(-ii*p*t*n).exp()
                cindex=ni if ni<nf else nn
                dindex=nf+ni if ni<nf else nn+1
                W[row,cindex]=-p*av*(sc-t*sd)
                W[row,dindex]=ii*av*sd
    for j in range(7): W[6*N+j,cols-1]=(1 if j==0 else 2)*P[j]
    progress('quadrature mass matrix complete')
    z=[-B/(t+ii*h)-ii*h for t in ts]
    lam=[ii/(b*(t+ii*h)) for t in ts]
    G=acb_mat(2*nf,nt)
    for ni,n in enumerate(nodes):
        for ti in range(nt):
            g=lam[ti]*(ii*p*z[ti]*n).exp()
            G[ni,ti]=g
            G[nf+ni,ti]=ii*p*z[ti]*g
    jets=(G*W).real
    S=arb_mat(nn,cols)
    for ni,n in enumerate(nodes):
        Q,Dn=constants(n)
        for col in range(cols):
            a,d=jets[ni,col],jets[nf+ni,col]
            S[ni,col]=-a/Q
            S[nf+ni,col]=(Dn*a-d)/Q
    D=arb_mat([[S[i,j] for j in range(nn)] for i in range(nn)])
    Se=arb_mat([[S[i,nn+j] for j in range(3)] for i in range(nn)])
    Y=arb_mat(nn,10)
    for j,n in enumerate([1,3,4,7,9]):
        ni=nodes.index(n)
        Q,Dn=constants(n)
        Y[nf+ni,j]=-1/Q
        Y[ni,j+5]=1/Q
        Y[nf+ni,j+5]=-Dn/Q
    E1,E2=arb_mat(3,10),arb_mat(3,10)
    e0=['.567','.250','-.0074','0','-.209','.0096']
    e1=['-.976','.408','.0115','1','.938','-.017']
    for i in range(3):
        E1[i,0],E1[i,5]=dec(e0[i]),dec(e1[i])
        E2[i,0],E2[i,5]=dec(e0[i+3]),dec(e1[i+3])
    progress('projected matrix S complete')
    U=D
    vp=arb_mat([[int(i==j) for j in range(nn)] for i in range(nn)])
    vm=vp
    table=[['1.74','2.74','2.1'],['2.09','6.94','2.2'],['2.27','15.32','2.13'],
           ['1.75','25.3','1.97'],['.75','31.1','1.88'],['.12','32.09','1.85'],
           ['.0031','32.12','1.85'],['.000002','32.12','1.85'],['.000000000001','32.12','1.85']]
    powers=[]
    for r in range(9):
        vp=vp+vp*U
        vm=vm+(-1 if r==0 else 1)*(vm*U)
        norms=[norm1(U),norm1(vp),norm1(vm)]
        for value,bound in zip(norms,table[r]): require(value<dec(bound),f'power table row {r}, bound {bound}')
        if r==6: require(norms[0]<dec('.004'),'equation 11 D^64')
        powers.append(dict(step=r,U=show(norms[0]),Vp=show(norms[1]),Vm=show(norms[2])))
        if r<8: U=U*U
    require(norm1(vp)+norm1(vm)<36,'equation 11 sum inverse series norms')
    g1=Y+Se*E2
    g2=Se*E1
    xp,xm=vp*(g1+g2),vm*(g1-g2)
    xf=[(xp+xm)/2,(xp-xm)/2]
    XX=[]
    for xx,extra in zip(xf,[E1,E2]):
        XX.append(arb_mat([[xx[i,j] if i<nn else extra[i-nn,j] for j in range(10)] for i in range(cols)]))
    indiv=[[sum((abs(X[i,j]) for i in range(cols)),arb(0)) for j in range(10)] for X in XX]
    for i in range(2):
        for j in range(10):
            require(indiv[i][j]<dec([['1.29','2.65'],['1.01','3.03']][i][int(j>=5)]),'individual X norm table')
    combined=[indiv[0][j]+indiv[1][j] for j in range(10)]
    for j,val in enumerate(combined):
        require(val<dec('2.20' if j<5 else '5.40'),'combined X norm table')
        require(val<dec('2.3' if j<5 else '5.6'),'equation 11 combined X norm')
    summary=dict(power_norms=powers,individual_column_norms=[[show(x) for x in row] for row in indiv],
                 combined_column_norms=[show(x) for x in combined])
    progress('all equation 11 and norm table inequalities rigorously enclosed')
    return ts,W,z,lam,XX,summary


def low(row,box):
    K,J,xs,eks,ejs=box
    answers=[]
    for x in xs:
        v=[row[j]+x*row[j+5] for j in range(5)]
        answers.append(v[0]+sum(((v[j]*eks[j]).min(v[j]*ejs[j]) for j in range(1,5)),arb(0)))
    return answers[0].min(answers[1])

def check_signs(ts,W,z,lam,XX):
    nt=len(ts)
    WX=[W*acb_mat(X) for X in XX]
    omega=arb_mat([[arb(math.comb(d,r))/math.comb(40,r) if r<=d else arb(0) for r in range(41)] for d in range(41)])
    allnodes=[0]+nodes
    groups=['m=0','m=1','m=3,4','m>=7']
    printed=[['.33','.019','.0033','.00116'],['.34','.017','.0037','.0018'],
             ['.35','.033','.0061','.0026'],['.36','.036','.0085','.0031'],['.38','.011','.0105','.0037']]
    minima={}
    count=0
    global_value=None
    global_detail=None
    for idx,m in enumerate(allnodes):
        if m>88: break
        ys=[arb(allnodes[idx+1]-m)/2]
        if idx: ys.append(arb(allnodes[idx-1]-m)/2)
        nu=0 if m==0 else 2
        gi=0 if m==0 else 1 if m==1 else 2 if m in [3,4] else 3
        for y in ys:
            F,G=acb_mat(41,nt),acb_mat(41,nt)
            for ti,t in enumerate(ts):
                fa=(ii*p*t*m).exp()
                ga=lam[ti]*(ii*p*z[ti]*m).exp()
                for a in range(41+nu):
                    if a>=nu:
                        F[a-nu,ti]=fa/y**nu
                        G[a-nu,ti]=ga/y**nu
                    fa=fa*ii*p*y*t/(a+1)
                    ga=ga*ii*p*y*z[ti]/(a+1)
            for fn,sig in enumerate([-1,1]):
                lc=sig*(F*WX[fn]+G*WX[1-fn]).real
                Ls=omega*lc
                for bi,box in enumerate(BOXES):
                    K,J=box[:2]
                    tc=arb_mat(41,1)
                    if fn==0:
                        if m==0:
                            for r in range(41): tc[r,0]=K.exp()/K*(-K*y)**r/math.factorial(r)
                        elif m==1:
                            for r in range(41): tc[r,0]=K*(-K*y)**r/math.factorial(r+2)
                        elif m==3 and J is not None: tc[0,0]=J/2*(-13*J/6).exp()
                    tc=omega*tc
                    for d in range(41):
                        val=low([Ls[d,j] for j in range(10)],box)+tc[d,0]
                        require(val>dec('.001'),f'equation12 fn{fn+1} m{m} y{y} d{d} box{bi}')
                        require(val>dec(printed[bi][gi]),f'printed sign table fn{fn+1} m{m} y{y} d{d} box{bi}')
                        count+=1
                        detail=dict(fn=fn+1,m=m,y=show(y),d=d,K=ENDPOINTS[bi],J=ENDPOINTS[bi+1])
                        key=(bi,gi)
                        if key not in minima or float(val.mid())<float(minima[key][0].mid()): minima[key]=(val,detail)
                        if global_value is None or float(val.mid())<float(global_value.mid()): global_value,global_detail=val,detail
        if idx%6==0: progress(f'sign half-gaps certified through node {m}')
    # Float conversions above select diagnostics only; every inequality was
    # independently proved with strict Arb comparisons before this selection.
    tail=[]
    s0=arb(179)/2
    sel=[(nodes.index(n),n) for n in nodes if n<=88]+[(None,0)]
    for bi,box in enumerate(BOXES):
        for fn,X in enumerate(XX):
            sig=-1 if fn==0 else 1
            cr=[]; dr=[]
            for ni,n in sel:
                ci=ni if ni is not None else nn
                di=nf+ni if ni is not None else nn+1
                cr.append([sig*X[ci,j] for j in range(10)])
                dr.append([sig*X[di,j] for j in range(10)])
            value=low([sig*X[cols-1,j] for j in range(10)],box)
            value+=low([sum((row[j] for row in dr),arb(0)) for j in range(10)],box).min(0)/s0
            for (ni,n),c,d in zip(sel,cr,dr):
                value+=low(c,box).min(0)/(s0-n)**2+low(d,box).min(0)*n/(s0*(s0-n))
            require(value>dec('.0021'),f'equation13 box{bi} fn{fn+1}')
            require(value>dec(['.0022','.0029','.0036','.0043','.0052'][bi]),f'printed tail table box{bi} fn{fn+1}')
            tail.append(dict(fn=fn+1,K=ENDPOINTS[bi],J=ENDPOINTS[bi+1],value=show(value)))
    return dict(equation12_certified_count=count,minimum=dict(value=show(global_value),**global_detail),
                table=[dict(group=groups[gi],value=show(minima[bi,gi][0]),**minima[bi,gi][1]) for bi in range(5) for gi in range(4)],tail=tail)


def run_verification(options):
    ts,W,z,lam,XX,summary=build()
    summary['signs']=check_signs(ts,W,z,lam,XX)
    # A completed run must include every required comparison, even under -O.
    require(summary['signs']['equation12_certified_count'] == 37310,
            'required Bernstein comparison count: 37310')
    require(len(summary['signs']['tail']) == 10, 'required tail comparison count: 10')
    summary['verification']='All (11)-(13) and every displayed numerical table inequality certified by strict Arb ball comparisons.'
    summary['precision_bits']=ctx.prec
    summary['arithmetic']='python-flint 0.9.0 / Arb; exact mathematical quadrature, without rational floor emulation'
    summary['input_sha256']=options.binding['input_sha256']
    summary['_provenance']=run_metadata(options, 'numeric_balls.py', ctx.prec)
    summary['completed_counts']={'bernstein': summary['signs']['equation12_certified_count'],
                                 'tail': len(summary['signs']['tail'])}
    summary['elapsed_seconds']=time.monotonic()-started
    recheck_inputs(options)
    return summary


def main(argv=None):
    options = parse_options(__doc__, argv)
    initialize_numerics()
    with managed_output(options, ('numeric_balls_results.json', 'numeric_balls_run.log'),
                        'numeric_balls_results.json') as files:
        with contextlib.redirect_stdout(Tee(sys.stdout, files['numeric_balls_run.log'])), \
                contextlib.redirect_stderr(Tee(sys.stderr, files['numeric_balls_run.log'])):
            try:
                summary = run_verification(options)
                files['numeric_balls_results.json'].write(json.dumps(summary, indent=2)+'\n')
                files['numeric_balls_results.json'].flush()
                print(json.dumps(summary, indent=2), flush=True)
            except Exception:
                traceback.print_exc()
                raise
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
