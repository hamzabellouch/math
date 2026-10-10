#!/usr/bin/env python3
"""Arb scalar envelopes, tail bounds, Taylor errors, and quadrature error.

Call run_certificate() after constructing the finite certificate context.
Importing this module does not run a certificate.
"""
import json
from math import factorial
import flint
from flint import arb, ctx
from certificate_data import provenance, write_result


def run_certificate(c):
    a=lambda x:arb(str(x))
    printed_scalar_bounds=[]

    def printed_upper(name,value,bound):
        assert value<a(bound),(name,str(value),bound)
        printed_scalar_bounds.append({'name':name,'enclosure':str(value),'upper':bound})

    def printed_lower(name,value,bound):
        assert value>a(bound),(name,str(value),bound)
        printed_scalar_bounds.append({'name':name,'enclosure':str(value),'lower':bound})

    pi,b,h,B=c.pi,c.b,c.h,c.B
    bs=list(map(a,['2.887','2.665','2.218','1.804','1.486','1.250','1.073']))
    aa=list(map(a,['2.934','2.713','2.269','1.859','1.548','1.320','1.151']))
    gg=list(map(a,['2.933','2.440','1.567','.900','.482','.224','.0597']))
    mm=list(map(a,[56,48,35,25,19,'6.284']))
    bet=list(map(a,[0,'4.8','3.17','1.946','1.217','.792']))
    atoms=list(map(a,[5,4,4,4,2,4,2]))

    endpoint_checks=[]
    for j,t in enumerate(c.ts):
        lam=1/(b*(t*t+h*h).sqrt())
        z=(h*h+(B*B-2*B*h*h)/(t*t+h*h)).sqrt()
        im=h*(B/(t*t+h*h)-1)
        assert lam<bs[j] and z<aa[j] and im>gg[j]
        endpoint_checks.append({'j':j,'lambda_abs':str(lam),'z_abs':str(z),'Im_z':str(im)})
    for j in range(1,7):
        for t in (c.ts[j-1],c.ts[j]):
            deriv=2*h*B*t/(t*t+h*h)**2
            assert deriv>=bet[j-1]
        for n in c.A:
            phase=[c.P[l]*c.exp_pi(c.ts[l]*n) for l in range(j,7)]
            ss=sum(phase)
            assert 2*pi*abs(ss)<mm[j-1]
            for t in (c.ts[j-1],c.ts[j]):
                sc=sum((c.ts[l]-t)*phase[l-j] for l in range(j,7))
                assert 2*pi*pi*abs(sc)<mm[j-1]
    for n in c.A:
        assert c.Q[n]>a('1.75') and abs(c.D[n])<a('2.12')


    def ls(s):
        s=arb(s)
        out=[]
        for j in range(1,7):
            factor=arb(1)/6
            if s>0 and bet[j-1]>0:
                factor=factor.min(1/(pi*bet[j-1]*s))
            out.append(bs[j-1]*(-pi*gg[j]*s).exp()*factor)
        return out


    def laps(s):
        return [atoms[j]*bs[j]*(-pi*gg[j]*s).exp() for j in range(7)]


    tail_bounds=[]
    for cut,bound in [(0,'27.7'),(4,'.272'),(16,'.0145'),(100,'4.7e-10')]:
        firsts=[n for n in range(cut+1,cut+13) if n%12 in c.A]
        total=arb(0)
        for n in firsts:
            factors=ls(n)
            for j in range(1,7):
                total+=(1+abs(c.D[n%12])+pi*aa[j-1])/c.Q[n%12]*mm[j-1]*factors[j-1]/(1-(-12*pi*gg[j]).exp())
        assert total<a(bound)
        printed_upper('row envelope at cut '+str(cut),total,
                      {0:'27.618723',4:'.269094',16:'.014122',100:'4.617010e-10'}[cut])
        tail_bounds.append({'cut':cut,'bound':str(total),'claimed_upper':bound})
    atom_tail=arb(0)
    for n in range(101,113):
        if n%12 not in c.A:
            continue
        factors=laps(n)
        for j in range(7):
            atom_tail+=(1+abs(c.D[n%12])+pi*aa[j])/c.Q[n%12]*factors[j]/(1-(-12*pi*gg[j]).exp())
    assert atom_tail<a('3.2e-8')
    printed_upper('atom-column tail',atom_tail,'3.131186e-8')

    # Exact integer checks of all four displayed coefficient-norm equalities.
    scale=10**10
    zero_c=(scale,0)
    zero_d=(44*10**8,-368*10**7)
    rows=c.source_data['rows']
    exact_norms=[abs(zero_c[i])+abs(zero_d[i])+
                 sum(abs(row[1+2*i])+abs(row[2+2*i]) for row in rows)
                 for i in range(2)]
    exact_tail_norms=[sum(abs(row[1+2*i])+abs(row[2+2*i]) for row in rows if row[0]>40)
                      for i in range(2)]
    assert exact_norms[0]==22516666247
    assert exact_norms[1]==8927477314
    assert exact_tail_norms[0]==197471
    assert exact_tail_norms[1]==161623

    # Coefficient norms and the exact-solution distance asserted in the text.
    norms=[sum(abs(cc)+abs(dd) for cc,dd in tab.values()) for tab in c.tab]
    tail_norms=[sum(abs(cc)+abs(dd) for n,(cc,dd) in tab.items() if n>40) for tab in c.tab]
    assert all(x<a('2.29') for x in norms)
    assert all(x<a('.00002') for x in tail_norms)
    distance=2*(91*a('1.1e-7')+2540*(a('2.29')*a('5e-10')+a('.017')*a('3.2e-8')))
    assert distance<a('.00003')
    finite_inverse=(a(32)+(1+a('3.7'))/(1-a('.687'))*a('.11')*32).max((1+a('3.7'))/(1-a('.687')))
    assert finite_inverse<90

    # Lower bound on the finite rational part throughout the infinite tail.
    s0=a('41.5')
    r_lowers=[]
    for i in range(2):
        sig=arb(-1 if i==0 else 1)
        selected={n:(sig*cc,sig*dd) for n,(cc,dd) in c.tab[i].items() if n<=40}
        lower=sig*c.C[i]+sum(dd for cc,dd in selected.values()).min(0)/s0
        for n,(cc,dd) in selected.items():
            lower+=cc.min(0)/(s0-n)**2+dd.min(0)*n/(s0*(s0-n))
        assert lower>a('.012' if i==0 else '.016')
        printed_lower('rational tail index '+str(i+1),lower,('.01206834','.01656468')[i])
        assert lower-a('.00003')/(s0-40)>a('.011')
        r_lowers.append(str(lower))

    direct_second=sum(mm[j-1]*(pi*c.ts[j])**2/6 for j in range(1,7))
    assert direct_second<77
    printed_upper('direct second derivative envelope',direct_second,'76.043')
    tail_second=a('.00005')*77+a('2.3')*sum(mm[j-1]*ls(s0)[j-1]*(pi*aa[j-1])**2 for j in range(1,7))+a('.017')*sum(laps(s0)[j]*(pi*aa[j])**2 for j in range(7))
    assert tail_second<a('.006')
    printed_upper('tail second derivative envelope',tail_second,'.005303')

    # P midpoint quotients: log-concavity supplies the rest of each half-gap.
    midpoint_values=[]
    for left,right in zip(c.A,c.A[1:]+[12]):
        mid=arb(left+right)/2
        val=arb(1)
        for n in c.A:
            val*=(2*(pi*(mid-n)/12).sin())**2
        quotient=val/(arb(right-left)/2)**2
        assert quotient>a('.68')
        midpoint_values.append({'left':left,'right':right,'quotient':str(quotient)})

    # Approximate-to-exact quotient errors.
    origin_error=a('.00003')*sum(mm[j-1]*(arb(1)/6+ls(0)[j-1]) for j in range(1,7))
    assert origin_error<a('.004')
    printed_upper('origin quotient error',origin_error,'.003189')
    quotient_errors=[]
    for m,nu,bound in [('.5',1,'.011'),('.5',2,'.011'),('2',2,'.002')]:
        error=a('.00003')/factorial(nu)*sum(mm[j-1]*((pi*c.ts[j])**nu/6+ls(a(m))[j-1]*(pi*aa[j-1])**nu) for j in range(1,7))
        assert error<a(bound)
        printed_upper('quotient error at '+m+', order '+str(nu),error,
                      {('.5',1):'.003736',('.5',2):'.009146',('2',2):'.001796'}[(m,nu)])
        quotient_errors.append({'lower_s':m,'nu':nu,'error':str(error)})
    tv=a('2.29')*sum(mm)/6+a('.017')*sum(atoms)
    assert tv<80
    printed_upper('direct total variation',tv,'72.669')

    truncations=[]
    for m,Y,nu in [(0,'.5',0),(1,'1',1),(1,'1',2),(3,'1',2),(4,'1.5',2)]:
        Y=a(Y);q=29+nu
        ratio=pi*aa[0]*Y/(q+1)
        assert ratio<1
        value=Y**(-nu)/factorial(q)/(1-ratio)*(80*(pi*Y)**q+a('2.3')*sum(mm[j-1]*ls(m)[j-1]*(pi*aa[j-1]*Y)**q for j in range(1,7))+a('.017')*sum(laps(m)[j]*(pi*aa[j]*Y)**q for j in range(7)))
        assert value<a('.001')
        printed_upper('Taylor remainder at '+str(m)+', order '+str(nu),value,
                      {(0,0):'1.578e-10',(1,1):'2.007e-5',(1,2):'5.735e-6',
                       (3,2):'9.581e-11',(4,2):'6.133e-7'}[(m,nu)])
        truncations.append({'m':m,'Y':str(Y),'nu':nu,'error':str(value)})

    # Independent disk estimates validating the moment-error enlargement.
    rho=arb(1)/6
    cmax=arb(11)/12
    imlower=B*(h-rho)/(cmax*cmax+h*h-rho*rho)-h
    assert imlower>-a('.081')
    assert 1/(b*(h-rho))<5
    assert B/(h-rho)+h<a('6.2')
    assert cmax+rho<a('1.1')
    density_prefactor=(3*2*pi*pi*10*arb(13)/12).max(3*2*pi*10)
    assert density_prefactor<1000
    disk_direct=1000*(100*pi/6).exp()*(100*pi/6).exp()*(a('1.5')*pi*a('1.1')).exp()
    disk_transform=1000*(100*pi/6).exp()*5*(100*pi*a('.081')).exp()*(a('1.5')*pi*a('6.2')).exp()
    assert disk_direct<a('1e53') and disk_transform<a('1e53')
    printed_upper('direct disk integrand',disk_direct,'5.38e50')
    printed_upper('transformed disk integrand',disk_transform,'1.51e50')
    quadrature_discrepancy=a('1e53')*arb(2)**(-254)
    assert quadrature_discrepancy<a('1e-22')
    printed_upper('quadrature discrepancy',quadrature_discrepancy,'3.455e-24')
    assert len(printed_scalar_bounds)==22

    result={'source_sha256':c.EXPECTED_SHA,'status':'pass','method':'Arb enclosures at 192 bits; endpoint monotonicity, convexity, geometric tails, and log-concavity supplied by the analytic argument','endpoint_envelopes':endpoint_checks,'row_tail_bounds':tail_bounds,'atom_tail_bound':str(atom_tail),'table_norms':list(map(str,norms)),'table_tail_norms':list(map(str,tail_norms)),'exact_list_distance_bound':str(distance),'finite_inverse_bound':str(finite_inverse),'rational_part_lower_bounds':r_lowers,'direct_second_derivative_envelope':str(direct_second),'tail_second_derivative_bound':str(tail_second),'midpoint_quotients':midpoint_values,'origin_error':str(origin_error),'quotient_errors':quotient_errors,'direct_total_variation_bound':str(tv),'Taylor_truncation_bounds':truncations,'disk_Im_z_lower':str(imlower),'disk_density_prefactor':str(density_prefactor),'disk_direct_integrand_bound':str(disk_direct),'disk_transformed_integrand_bound':str(disk_transform),'quadrature_discrepancy_bound':str(quadrature_discrepancy)}
    result['printed_scalar_bounds']=printed_scalar_bounds
    result['exact_coefficient_norms']={'denominator':scale,'full_numerators':exact_norms,
                                       'tail_numerators':exact_tail_norms}
    result.update(provenance(c.source_data, __file__))
    result["python_flint_version"]=flint.__version__
    result["precision_bits"]=ctx.prec
    write_result("scalar.json", result)
    print(json.dumps({'status':result['status'],
                      'quadrature_discrepancy_bound':result['quadrature_discrepancy_bound'],
                      'exact_list_distance_bound':result['exact_list_distance_bound'],
                      'results_file':'verification/results/scalar.json'},indent=2),flush=True)

    return result


if __name__ == "__main__":
    from interval_certificate import run_certificate as run_finite
    run_certificate(run_finite())
