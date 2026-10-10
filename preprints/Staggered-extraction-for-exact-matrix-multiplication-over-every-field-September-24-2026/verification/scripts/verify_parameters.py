#!/usr/bin/env python3
"""Verify the packaged exact rational parameters for the staggered laser bound.

Requires Python >=3.10 and mpmath==1.3.0, with assertions enabled (no -O).
From verification/, first create a fresh directory outside verification/, then run:
  mkdir ../verification-recheck
  python3 -B scripts/verify_parameters.py --mode interval --dps 80 --rational-log --output ../verification-recheck/recheck-interval-series.json
  python3 -B scripts/verify_parameters.py --mode interval --dps 80 --output ../verification-recheck/recheck-interval.json

The first verifier command encloses true logarithms using rational arithmetic
and an explicit rational series-tail bound. The second is an independent directed
native-log check of the same contractions. No optimizer, network, source audit,
or floating-point exp approximation is needed. Always select a fresh --output
outside verification/: keep packaged inputs and certificates unchanged. Omitting
--output replaces the supplied data/certificate-interval[-series].json.
"""
import argparse
from collections import Counter, defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import permutations
from math import factorial
from pathlib import Path
import hashlib
import json
import sys
import mpmath

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)
BASE = Path(__file__).resolve().parents[1]
SHA = '538deff25fb30b68b01f7ff43b2a62ce0719afba25891ff38fda7027a31c2b65'
R = (0, 1, 2, 2, 3, 4)
D = (1, 10, 25, 2, 10, 1)
KAPPA = (5, 4, 2, 3, 1, 0)

def shapes(size):
    return [(i, j, size-i-j) for i in range(size+1) for j in range(size+1-i)]

def below(s):
    return [u for u in shapes(sum(s)//2) if all(u[i] <= s[i] for i in range(3))]

def complement(s, u):
    return tuple(s[i]-u[i] for i in range(3))

@lru_cache(None)
def exact_F(n):
    y = Fraction(n, 640000)
    return sum((y**j / factorial(j) for j in range(17)), Fraction(0))**64

class Cursor:
    def __init__(self, values):
        self.values, self.pos = values, 0
    def get(self):
        value = self.values[self.pos]
        self.pos += 1
        return value
    def done(self):
        assert self.pos == len(self.values), (self.pos, len(self.values))

def exact_structure_checks(arrays):
    """Prove discrete identities before any interval conversion.

    Normalization is exact by its definition as division by the positive sum.
    The interval containment checks in main() are only consistency diagnostics.
    """
    pair_codes=((0,0),(0,1),(1,1),(0,2),(1,2),(2,2))
    for i,code in enumerate(pair_codes):
        assert sum(code)==R[i]
        assert (1 if code[0]==code[1] else 2)*5**code.count(1)==D[i]
        assert pair_codes[KAPPA[i]]==tuple(sorted(2-x for x in code))
        assert KAPPA[KAPPA[i]]==i and D[KAPPA[i]]==D[i]
    gp=[g for g in shapes(16) if min(g)>0 and tuple(sorted(g))==g]
    tp=[t for t in shapes(8) if min(t)>0]
    tz=[t for t in shapes(8) if min(t)==0]
    for parents,data in [(gp,arrays[1]),(tp,arrays[2])]:
        cursor=Cursor(data)
        for s in parents:
            half=sum(s)//2
            weights=[]
            for k in s:
                coord={j:cursor.get() for j in range(max(0,k-half),k//2)}
                coord[k//2]=0
                weights.append(coord)
            signatures={u:tuple(weights[i][min(u[i],s[i]-u[i])] for i in range(3)) for u in below(s)}
            for u,signature in signatures.items():
                assert signature==signatures[complement(s,u)]
        cursor.done()
    cursor=Cursor(arrays[3]);ds={}
    for t in tp:
        for u in below(t):
            if max(u)==2:
                ds[t,u]=Fraction(cursor.get(),10**6)
                assert 0<=ds[t,u]<=Fraction(110106,10**6)
    cursor.done()
    assert ds[(1,3,4),(0,2,2)]==Fraction(92966,10**6)
    assert ds[(1,3,4),(1,1,2)]==Fraction(1204,10**6)
    def law(t,u,w):
        return {2:1-ds[t,u],3:ds[t,u]} if u[w]==2 else {R.index(u[w]):Fraction(1)}
    checks=0
    for t in tp:
        for u in below(t):
            for zero_axis in range(3):
                if u[zero_axis]==0:
                    a,b=[i for i in range(3) if i!=zero_axis]
                    assert {KAPPA[i]:v for i,v in law(t,u,a).items()}==law(t,u,b)
                    checks+=1
    cursor=Cursor(arrays[4])
    for t in tz:
        support=[(i,j) for i in range(6) for j in range(i,6) if R[i]+R[j]==max(t)]
        assigned={ij:(cursor.get() if k<len(support)-1 else 0) for k,ij in enumerate(support)}
        ordered={(i,j):n for (a,b),n in assigned.items() for (i,j) in {(a,b),(b,a)}}
        assert all(ordered[i,j]==ordered[j,i] for i,j in ordered)
        assert len(ordered)==sum(R[i]+R[j]==max(t) for i in range(6) for j in range(6))
        for i,j in ordered:
            for w in range(3):
                stat=(0,0) if t[w]==0 else ((i,j) if w==t.index(max(t)) else (KAPPA[i],KAPPA[j]))
                assert R[stat[0]]+R[stat[1]]==t[w]
    cursor.done()
    tail=Fraction(2,63*3**63)/(1-Fraction(1,9))
    epsilon=2048*tail
    assert epsilon<Fraction(6391,10**32)
    final_error=(Fraction(68,3)+9*Fraction(2371056,10**6)+8)*epsilon
    assert final_error<Fraction(3324,10**30)
    return {'complement_checks_including_two_zero_axes':checks,
            'exact_split_weight_symmetries':True,'exact_zero_leaf_complements':True,
            'exact_multiplicities_and_involution':True,
            'normalization':'Defined by exact division by positive total weight.',
            'log_error_bound_fraction':str(epsilon),
            'final_log_substitution_error_bound_fraction':str(final_error)}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--mode', choices=['interval', 'point'], default='interval')
    parser.add_argument('--dps', type=int, default=80)
    parser.add_argument('--rational-log', action='store_true',
                        help='Enclose true logs with the submitted rational series plus its tail bound.')
    parser.add_argument('--output', type=Path, help='Write certificate to this path.')
    args = parser.parse_args()
    assert args.dps >= 50, 'Use at least 50 decimal digits.'
    assert mpmath.__version__ == '1.3.0', 'The archived verifier pins mpmath 1.3.0.'
    interval = args.mode == 'interval'
    assert not args.rational_log or interval
    ctx = mpmath.iv if interval else mpmath.mp
    ctx.dps = args.dps
    if interval:
        mpmath.mp.dps = args.dps+30
    zero, one = ctx.mpf(0), ctx.mpf(1)
    observed_exponents=[]
    def log(x):
        if not args.rational_log:
            return ctx.ln(x)
        x=ctx.mpf(x)
        assert x>0
        def poly(y):
            ratio=(y-one)/(y+one)
            ratio2=ratio*ratio
            power=ratio
            total=zero
            for j in range(31):
                total+=power/(2*j+1)
                power*=ratio2
            return 2*total
        # The function L is continuous and increasing at powers of two as well
        # as between them, so enclosing its endpoint values encloses its range.
        endpoint_results=[]
        for endpoint in x._mpi_:
            sign,mantissa,exp,bits=endpoint
            assert sign==0 and mantissa>0
            e=exp+bits-1
            assert abs(e)<2048
            observed_exponents.append(e)
            endpoint_fraction=Fraction(mantissa)*Fraction(2)**exp
            y=(ctx.mpf(endpoint_fraction.numerator)/ctx.mpf(endpoint_fraction.denominator))/(ctx.mpf(2)**e)
            endpoint_results.append(e*poly(ctx.mpf(2))+poly(y))
        enclosed=ctx.mpf([endpoint_results[0].a,endpoint_results[1].b])
        maxe=max(abs(endpoint[2]+endpoint[3]-1) for endpoint in x._mpi_)
        # Uniform tail: |log(y)-P(y)| <= 2*(1/3)^63/(63*(1-1/9))
        # for 1 <= y <= 2. Account for e*P(2) as well.
        tail=(maxe+1)*ctx.mpf(2)/(ctx.mpf(3)**63*63*(one-one/9))
        return enclosed+ctx.mpf([-tail.b,tail.b])
    inp = (BASE/'data'/'parameters.json').read_bytes()
    assert hashlib.sha256(inp).hexdigest() == SHA, 'Packaged parameter data changed.'
    packaged = json.loads(inp)
    assert packaged['array_order'] == ['a','P','p','d','z']
    arrays = [packaged['arrays'][name] for name in packaged['array_order']]
    structural = exact_structure_checks(arrays)
    assert list(map(len, arrays)) == [17, 118, 54, 75, 36]
    F = {}
    for n in {0}.union(*map(set, [arrays[i] for i in [0,1,2,4]])):
        f = exact_F(n)
        assert f > 0
        assert Fraction(1,2**23)<f<2**23
        F[n] = ctx.mpf(f.numerator)/ctx.mpf(f.denominator)

    def num(x):
        if interval:
            def outward(endpoint, lower):
                sign,mantissa,exp,bits=endpoint
                value=Fraction((-1 if sign else 1)*mantissa)
                value*=Fraction(2)**exp
                places=args.dps+10
                scaled=value*10**places
                integer=(scaled.numerator//scaled.denominator) if lower else -(-scaled.numerator//scaled.denominator)
                raw=str(abs(integer)).zfill(places+1)
                return ('-' if integer<0 else '')+raw[:-places]+'.'+raw[-places:]
            return {'lo': outward(x._mpi_[0], True),
                    'hi': outward(x._mpi_[1], False)}
        return mpmath.mp.nstr(x, args.dps-5)

    def contains_zero(x):
        return x.a <= 0 <= x.b if interval else abs(x) < ctx.mpf('1e-60')

    def check_normalized(p):
        assert all(x > 0 for x in p.values())
        assert contains_zero(sum(p.values(), zero)-one)

    def normalize(p):
        total = sum(p.values(), zero)
        return {key: value/total for key, value in p.items()}

    def entropy(p):
        if isinstance(p, dict):
            p = p.values()
        vals = [x for x in p if x != 0]
        total = sum(vals, zero)
        if total == 0:
            return zero
        assert all(x > 0 for x in vals)
        return total*log(total)-sum((x*log(x) for x in vals), zero)

    def pair(p, s, q):
        ans = defaultdict(lambda: zero)
        for u, mass in p.items():
            for i, vi in q[u].items():
                for j, vj in q[complement(s,u)].items():
                    ans[(i,j)] += mass*vi*vj
        return dict(ans)

    def capacity(s, p, priority, laws):
        X,Y,Z = priority
        marginal = defaultdict(lambda: zero)
        for u, mass in p.items():
            marginal[u[X]] += mass
        result = [entropy(marginal)]
        for W in [Y,Z]:
            q = {u:laws(u,W) for u in p}
            groups = {}
            singleton_entropy = zero
            for u,mass in p.items():
                single = (u[Z] == 0) if W == Y else (u[X] == 0 or u[Y] == 0)
                if single:
                    singleton_entropy += mass*entropy(q[u])
                    continue
                group = groups.setdefault(u[W], defaultdict(lambda: zero))
                for i, val in q[u].items():
                    group[i] += mass*val
            # K is homogeneous, so entropy(mass*q)=mass*H(q).
            J = singleton_entropy+sum((entropy(group) for group in groups.values()), zero)
            result.append(entropy(pair(p,s,q))-2*J)
        return result

    gs = [g for g in shapes(16) if tuple(sorted(g)) == g]
    gp = [g for g in gs if min(g)>0]
    ts = shapes(8)
    tp = [t for t in ts if min(t)>0]
    tz = [t for t in ts if min(t)==0]
    A = {}
    for g in gs:
        multiplicity = 6
        for count in Counter(g).values():
            multiplicity //= factorial(count)
        A[g] = multiplicity * F[arrays[0][g[0]]] * F[arrays[0][g[1]]] * F[arrays[0][g[2]]]
    A = normalize(A)
    check_normalized(A)

    split_maps = {}
    cursors = {}
    for label, parents, data in [('P',gp,arrays[1]),('p',tp,arrays[2])]:
        cursor = Cursor(data)
        ans = {}
        for s in parents:
            half = sum(s)//2
            weights=[]
            for k in s:
                coord = {j:F[cursor.get()] for j in range(max(0,k-half),k//2)}
                coord[k//2] = one
                weights.append(coord)
            vals = {}
            for u in below(s):
                vals[u] = ctx.fprod([weights[i][min(u[i],s[i]-u[i])] for i in range(3)]) if not interval else weights[0][min(u[0],s[0]-u[0])]*weights[1][min(u[1],s[1]-u[1])]*weights[2][min(u[2],s[2]-u[2])]
            ans[s]=normalize(vals)
            check_normalized(ans[s])
            for u in ans[s]:
                assert contains_zero(ans[s][u]-ans[s][complement(s,u)])
        cursor.done()
        split_maps[label] = ans
        cursors[label] = cursor.pos
    P,p = split_maps['P'],split_maps['p']
    d = {}
    cursor = Cursor(arrays[3])
    for t in tp:
        for u in below(t):
            if max(u)==2:
                n = cursor.get()
                assert 0 <= n <= 1000000
                d[t,u] = ctx.mpf(n)/1000000
    cursor.done()
    cursors['d'] = cursor.pos
    z = {}
    cursor = Cursor(arrays[4])
    for t in tz:
        unordered = [(i,j) for i in range(6) for j in range(i,6) if R[i]+R[j]==max(t)]
        vals={}
        for index,(i,j) in enumerate(unordered):
            weight = F[cursor.get()] if index < len(unordered)-1 else one
            vals[i,j]=weight
            vals[j,i]=weight
        z[t]=normalize(vals)
        check_normalized(z[t])
        for i,j in z[t]:
            assert contains_zero(z[t][i,j]-z[t][j,i])
    cursor.done()
    cursors['z'] = cursor.pos

    def v(t,u,w):
        if u[w]==2:
            return {i:x for i,x in [(2,one-d[t,u]),(3,d[t,u])] if x != 0}
        return {R.index(u[w]):one}

    V={}
    normalization_count=0
    for t in ts:
        for w in range(3):
            if min(t)>0:
                q={u:v(t,u,w) for u in p[t]}
                for u,law in q.items():
                    check_normalized(law)
                    normalization_count+=1
                    assert all(R[i]==u[w] for i in law)
                V[t,w]=pair(p[t],t,q)
            elif t[w]==0:
                V[t,w]={(0,0):one}
            elif w == t.index(max(t)):
                V[t,w]=z[t]
            else:
                V[t,w]={(KAPPA[i],KAPPA[j]):mass for (i,j),mass in z[t].items()}
            check_normalized(V[t,w])
            assert all(R[i]+R[j]==t[w] for i,j in V[t,w])
    # Interval consistency checks supplement the exact structural checks above.
    # Containment of zero is not used to prove a symbolic identity.
    zero_compat=0
    for t in tz:
        nz=[i for i in range(3) if t[i]>0]
        if len(nz)==2:
            w0,w1=nz
            transformed={(KAPPA[i],KAPPA[j]):mass for (i,j),mass in V[t,w0].items()}
            assert set(transformed)==set(V[t,w1])
            assert all(contains_zero(mass-V[t,w1][ij]) for ij,mass in transformed.items())
            zero_compat+=1
    for t in tp:
        for u in below(t):
            nz=[i for i in range(3) if u[i]>0]
            if min(u)==0 and len(nz)==2:
                w0,w1=nz
                transformed={KAPPA[i]:mass for i,mass in v(t,u,w0).items()}
                other=v(t,u,w1)
                assert set(transformed)==set(other)
                assert all(contains_zero(mass-other[i]) for i,mass in transformed.items())
                zero_compat+=1

    m={t:2*sum((A[g]*P[g].get(t,zero) for g in gp),zero) for t in ts}
    mu={(t,u):2*m[t]*mass for t in tp for u,mass in p[t].items()}
    rowsA={i:[zero,zero,zero] for i in range(1,6)}
    typesB=sorted(set(tuple(sorted(t)) for t in tp))
    rowsB={t:[zero,zero,zero] for t in typesB}
    pi={}
    canonical={(1,1,6),(1,2,5),(1,3,4),(2,2,4),(3,2,3)}
    for t in tp:
        pi[t]=next(order for order in permutations(range(3)) if tuple(t[i] for i in order) in canonical)
        caps=capacity(t,p[t],pi[t],lambda u,w:v(t,u,w))
        row=rowsB[tuple(sorted(t))]
        for i in range(3):row[i]+=m[t]*caps[i]
    for g in gp:
        caps=capacity(g,P[g],(0,1,2),lambda t,w:V[t,w])
        for i in range(3):rowsA[min(g)][i]+=A[g]*caps[i]
    LA=[sum((row[i] for row in rowsA.values()),zero) for i in range(3)]
    LB=[sum((row[i] for row in rowsB.values()),zero) for i in range(3)]
    LAB=[LA[i]+LB[i] for i in range(3)]
    h=lambda dd:entropy([one-dd,dd])+dd*log(2)
    T=sum((mass for (t,u),mass in mu.items() if min(u)>0),zero)
    B=sum((mass*(2*log(2)+h(d[t,u]))/3 for (t,u),mass in mu.items() if min(u)>0),zero)
    C=B+sum(LAB,zero)/3
    LC=[C-val for val in LAB]
    lam=[(T*log(2)-LC[i])/(3*(T*log(2)-B)) for i in range(3)]
    assert T*log(2)-B>0
    assert all(x>0 for x in lam)
    assert contains_zero(sum(lam,zero)-one)
    assert all(x>0 for x in LA+LB+LC)
    LC_direct=[sum((mass*((one-lam[i])*log(2)+lam[i]*h(d[t,u]))
                   for (t,u),mass in mu.items() if min(u)>0),zero) for i in range(3)]
    assert all(contains_zero(LC_direct[i]-LC[i]) for i in range(3))
    marg=defaultdict(lambda:zero)
    for g,mass in A.items():
        for k in g:marg[k]+=mass/3
    H0=entropy(marg)
    coefficients=[1]
    for _ in range(8):
        nxt=[0]*(len(coefficients)+2)
        for i,c in enumerate(coefficients):
            for j,mult in enumerate([1,5,1]):nxt[i+j]+=c*mult
        coefficients=nxt
    S0=sum((mass*log(coefficients[max(g)]) for g,mass in A.items() if min(g)==0),zero)
    S1=sum((m[t]*(entropy(z[t])+sum((mass*log(D[i]*D[j]) for (i,j),mass in z[t].items()),zero)) for t in tz),zero)
    S2=zero
    for (t,u),mass in mu.items():
        if max(u)==4: rate=zero
        elif max(u)==3:rate=log(10)
        elif min(u)==0:rate=h(d[t,u])+2*(one-d[t,u])*log(5)
        else:rate=(2-d[t,u])*log(5)
        S2+=mass*rate
    S=S0+S1+S2
    beta=2*C-min(LA)-min(LAB)-min([LB[i]+LC[i] for i in range(3)])-min(LC)
    assert 0<beta<1
    assert all(value>0 for row in list(rowsA.values())+list(rowsB.values()) for value in row)
    lhs=H0+C+ctx.mpf(2371056)/1000000*S/3
    rhs=8*log(7)
    exponent=3*(rhs-H0-C)/S
    assert H0+C>ctx.mpf('5.6129832')
    assert S>ctx.mpf('12.5947700')
    assert lhs-rhs>0
    assert exponent < ctx.mpf('2.371054886006746')
    expectedA=[['.010739192','.016912163','.016213531'],['.081941050','.088150511','.082591626'],['.292033029','.283922596','.257330639'],['.547143900','.527202791','.487211274'],['.247999127','.248080948','.237330883']]
    expectedB=[['.002770751','.002770751','.000443544'],['.080908872','.106275766','.087117877'],['.386356324','.454421695','.323639129'],['.395346750','.395353092','.248930076'],['.611253765','.686627626','.634289551']]
    expectedScalars=['1.841147374','1.158066972','2.345955063','.031704071','.882362236','11.680704014']
    displayed=[ctx.mpf(x) for row in expectedA+expectedB for x in row]+list(map(ctx.mpf,expectedScalars))
    actual=[x for row in list(rowsA.values())+list(rowsB.values()) for x in row]+[H0,B,T,S0,S1,S2]
    errors=[x-y for x,y in zip(actual,displayed)]
    for error in errors:assert abs(error)<ctx.mpf('3e-8')

    scalarvals={'H0':H0,'Bstar':B,'T':T,'S0':S0,'S1':S1,'S2':S2,'Sstar':S,
       'Cstar':C,'H0_plus_Cstar':H0+C,'eight_log7':rhs,'lhs_at_2_371056':lhs,
       'strict_gap':lhs-rhs,'exponent_upper_bound':exponent,'T_log2':T*log(2),
       'T_log2_minus_Bstar':T*log(2)-B,'boundary_deficit_beta':beta}
    vectors={'LA':LA,'LB':LB,'LA_plus_LB':LAB,'LC':LC,'LC_direct':LC_direct,'lambda':lam,
       'balance_slacks':[T*log(2)-x for x in LC]}
    # These are rational decimal widenings printed in the paper.
    scalar_enclosures={
      'H0_plus_Cstar':('5.612983956059236756','5.612983956059236757'),
      'Sstar':('12.594770321594676362','12.594770321594676363'),
      'T_log2_minus_Bstar':('0.468025165562828972','0.468025165562828973'),
      'strict_gap':('0.000004676829725968','0.000004676829725969'),
      'exponent_upper_bound':('2.371054886006745684','2.371054886006745685'),
      'boundary_deficit_beta':('0.533798153','0.533798155')}
    for name,(lo,hi) in scalar_enclosures.items():
        assert scalarvals[name]>ctx.mpf(lo) and scalarvals[name]<ctx.mpf(hi), name
    vector_lower_bounds={
      'LC':['1.115343821954349','.962118642424118','1.396738451843254'],
      'balance_slacks':['.510748315682386','.663973495212618','.229353685793481'],
      'lambda':['.363761291246081','.472890166361139','.163348542392779']}
    for name,lower in vector_lower_bounds.items():
        for x,lo in zip(vectors[name],lower):
            assert x>ctx.mpf(lo) and x<ctx.mpf(lo)+ctx.mpf('1e-15')
    assert all(abs(error)<ctx.mpf('4.795e-10') for error in errors)
    # Adversarial propagation from all 36 printed centers independently.
    center_yield=displayed[30]+displayed[31]+sum(displayed[:30],zero)/3
    center_volume=sum(displayed[33:36],zero)
    omega=ctx.mpf(2371056)/1000000
    rounded_uncertainty=(12+omega)*ctx.mpf('4e-8')
    rounded_margin=center_yield+omega*center_volume/3-rhs-rounded_uncertainty
    assert rounded_margin>ctx.mpf('0.0000041011')
    scalarvals['rounded_table_lower_margin']=rounded_margin
    result={'parameter_sha256':SHA,'mode':args.mode,'dps':args.dps,'mpmath_version':mpmath.__version__,
      'log_mode':'rational_series_with_tail_enclosure' if args.rational_log else 'native',
      'observed_log2_exponent_range':[min(observed_exponents),max(observed_exponents)] if observed_exponents else None,
      'exact_structure_checks':structural,
      'counts':{'table_lengths':list(map(len,arrays)),'table_consumption':cursors,'sorted_g':len(gs),
      'positive_sorted_g':len(gp),'positive_ordered_t':len(tp),'zero_ordered_t':len(tz),
      'split_P_entries':sum(map(len,P.values())),'split_p_entries':sum(map(len,p.values())),
      'distinct_exact_F_values':len(F),'d_entries':len(d),'v_normalizations_checked':normalization_count,
      'complement_compatibilities_checked':zero_compat},
      'rowsA':{str(k):list(map(num,v)) for k,v in rowsA.items()},
      'rowsB':{str(k):list(map(num,v)) for k,v in rowsB.items()},
      'scalars':{k:num(v) for k,v in scalarvals.items()},
      'vectors':{k:list(map(num,v)) for k,v in vectors.items()},
      'tabulation_errors':list(map(num,errors)),
      'checks':{'all_table_entries_consumed':True,'distribution_support_and_normalization':True,
      'P_and_p_complement_symmetry':True,'z_transpose_symmetry':True,
      'zero_shape_complementation':True,'positive_balancing_fractions':True,
      'positive_stage_totals':True,'positive_partial_capacity_entries':True,
      'printed_enclosures_certified':True,'boundary_deficit_below_one':True,
      'conservative_rounded_table_margin':True,'tabulation_error_under_3e_minus8':True,
      'claimed_strict_inequalities':True},
      'unreachable_t':[t for t in ts if m[t]==0],
      'd_range':[min(arrays[3])/1000000,max(arrays[3])/1000000],
      'notes':['All F weights computed exactly as Fractions before conversion.',
      'Certified intervals use outward rounding of all operations and serialized decimal endpoints.',
      'In series mode, true logs are enclosed by the submitted rational polynomial plus its geometric tail.',
      'Assertions involving intervals require the entire interval to satisfy the bound.',
      'The mathematical extraction proof is supplied in the accompanying paper.']}
    if interval:
        widths=[]
        def collect_widths(node):
            if isinstance(node,dict):
                if set(node)=={'lo','hi'}:
                    widths.append(Fraction(node['hi'])-Fraction(node['lo']))
                else:
                    for value in node.values():collect_widths(value)
            elif isinstance(node,list):
                for value in node:collect_widths(value)
        collect_widths(result)
        cap=Fraction(3,10**29) if args.rational_log else Fraction(1,10**(args.dps-4))
        assert all(Fraction(0)<=width<cap for width in widths)
        result['interval_width_certificate']={
            'number_of_intervals':len(widths),'strict_width_cap':str(cap),
            'maximum_width_as_exact_fraction':str(max(widths))}
    output=args.output or BASE/'data'/f'certificate-{args.mode}{"-series" if args.rational_log else ""}.json'
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(output)
    print(json.dumps({'checks':result['checks'],
                      'strict_gap':result['scalars']['strict_gap'],
                      'exponent_upper_bound':result['scalars']['exponent_upper_bound']},indent=2))

if __name__=='__main__':main()
