#!/usr/bin/env python3
"""Scalar certificate for the triangular-lattice universal-energy proof.

Run: python verification/arithmetic_bounds.py --output-dir build/verification
Uses 512-bit Arb balls, exact Fraction arithmetic, and integer sample e_* calls.
The scalar assertions include the printed outward margins and composite error
budgets. They do not execute the degree-2000 rational enclosure procedure or
the full floor-rounded matrix prescription. The complete exact-quadrature
matrices are checked separately by numeric_balls.py. The public manifest binds
the article and checker sources before numerical imports.
"""
from contextlib import redirect_stderr, redirect_stdout
from fractions import Fraction as Q
import json
import math
import sys
import time
import traceback

sys.dont_write_bytecode = True
from inputs import (managed_output, parse_options, recheck_inputs, run_metadata)


class Tee:
    """Copy console output to the runtime log."""
    def __init__(self, console, log):
        self.console = console
        self.log = log

    def write(self, value):
        self.console.write(value)
        self.log.write(value)
        return len(value)

    def flush(self):
        self.console.flush()
        self.log.flush()


def run_certificate():
    """Check the named scalar bounds, including their composite additions."""
    from flint import arb, acb, ctx

    ctx.prec = 512
    out = {}

    def A(x):
        if isinstance(x, Q):
            return arb(x.numerator) / x.denominator
        return arb(x)

    def save(name, value, upper=None, lower=None):
        if upper is not None:
            assert value < A(upper), (name, value, upper)
        if lower is not None:
            assert value > A(lower), (name, value, lower)
        out[name] = str(value)
        print(name, value)

    pi = arb.pi()
    b = A(3).sqrt()/2
    h, B, M = A(Q(2,5)), A(Q(4,3)), 168
    eps = Q(1,10**80)
    ps = Q('3.14159265358979323846264338327950288419716939937510582097494459230781640628620899')
    bs = Q('0.86602540378443864676372317075293618347140262690519031402790348972596650845440001')

    # Exact rational 80-digit certificates; degree 131 alternating sums.
    def atan_bounds(x):
        lo = sum((-1)**j * x**(2*j+1)/Q(2*j+1) for j in range(66))
        return lo, lo+x**133/Q(133)

    lo5, hi5 = atan_bounds(Q(1,5))
    lo239, hi239 = atan_bounds(Q(1,239))
    assert ps < 16*lo5-4*hi239
    assert 16*hi5-4*lo239 < ps+eps
    assert bs*bs < Q(3,4) < (bs+eps)*(bs+eps)
    save('pi_decimal_error', abs(pi-A(ps)), upper=eps)
    save('b_decimal_error', abs(b-A(bs)), upper=eps)

    # Exact product constants for spectral total variation.
    save('c_column_variation', pi*pi*A(Q(65,18)), upper=36)
    save('d_column_variation', pi*A(Q(32,3)), upper=36)
    save('Q_min', 2*pi*pi/3*(2-2*b), lower='1.75')
    save('D_max', 7*pi*2*b/18, upper='2.12')

    def z(t):
        return -B/acb(t,h)-acb(0,h)

    save('real_lambda_max', 1/(b*h), upper=3)
    save('real_z_max', abs(z(A(0))), upper=3)
    save('real_decay_min', pi*z(A(1)).imag, lower='.187')
    save('low_interval_decay_min', pi*z(A(Q(5,6))).imag, lower='.70')
    save('last_interval_lambda_max', 1/(b*(A(Q(5,6))**2+h*h).sqrt()), upper='1.25')
    save('last_interval_z_max', abs(z(A(Q(5,6)))), upper='1.32')
    save('last_interval_decay_slope_min', 2*pi*h*B/(1+h*h)**2, lower='2.48')
    save('S_single_row_factor', 3*(1+A('2.12')+3*pi)/A('1.75'), upper=22)
    save('S_last_row_factor', A('1.25')*(1+A('2.12')+A('1.32')*pi)/A('1.75'), upper='5.3')
    save('S_full_norm_bound', 22*36/(A('.187').exp()-1), upper=4000)

    # Complex disk bounds used in the Taylor/Cauchy quadrature estimate.
    r = A(Q(1,6))
    for j in range(1,7):
        u = A(Q(2*j-1,12))
        den = u*u+h*h-r*r
        save(f'disk{j}_tmax', u+r, upper='1.1')
        save(f'disk{j}_lambda_max', 1/(b*((u*u+h*h).sqrt()-r)), upper=5)
        center = acb(-B*u/den,B*h/den-h)
        save(f'disk{j}_zmax', abs(center)+B*r/den, upper='6.2')
        save(f'disk{j}_Im_z_min', B*(h-r)/den-h, lower='-.081')

    # Uniform density bound: all positive-frequency |P_l| sum to ten,
    # and sum t_l |P_l|=16/3. On the first disk the sharper c-column
    # bound below dominates all later disks; d-column bound is 20*pi.
    save('density_c_bound_without_growth', 2*pi*pi*(A(Q(16,3))+A(Q(1,12))*10), upper=220)
    save('density_d_bound_without_growth', 20*pi, upper=220)
    save('analytic_direct_integrand_bound', 220*(pi*M/3+A('1.65')*pi).exp(), upper='1e83')
    save('analytic_transform_integrand_bound', 1100*(pi*M/6+pi*A('.081')*M+A('9.3')*pi).exp(), upper='1e83')
    save('quadrature_Cauchy_error', 4*A('1e83')/A(2)**384, upper='1e-31')

    # Fejer rule: this exact telescoping lower bound proves positivity.
    N=384
    positive_bracket=1-sum(Q(2,4*d*d-1) for d in range(1,N//2))
    assert positive_bracket == Q(1,N-1)
    save('quadrature_weight_uniform_lower_bound', A(positive_bracket/N), lower=0)

    # Analytic e_* error bounds including all componentwise floors.
    rho=A('.416')
    floorerr=A(2)*A(eps)
    err=arb(0)
    initial=arb(0)
    for j in range(1,61):
        err=rho/j*err+floorerr*rho**(j-1)/math.factorial(j)+floorerr
        initial+=err
    initial+=rho.exp()*rho**61/math.factorial(61)
    save('e_star_initial_error_bound',initial,upper='1.263e-78')
    save('e_star_Taylor_tail_bound',rho.exp()*rho**61/math.factorial(61),upper='2e-107')
    save('e_star_broad_squaring_bound', (A('4e-78')+12*floorerr)*3**12*A(7).exp(),upper='2.472e-69')
    err=A('4e-78')
    for j in range(12):
        err=(2*(A(7)/2**(12-j)).exp()+err)*err+floorerr
    save('e_star_recursive_squaring_bound',err,upper='1e-68')

    # Integer implementation exactly follows componentwise floor rounding.
    SCALE=10**80
    def e_star(wr,wi=Q(0)):
        wr,wi=Q(wr),Q(wi)
        ur=(wr*SCALE/4096).__floor__()
        ui=(wi*SCALE/4096).__floor__()
        dr,di=SCALE,0
        xr,xi=SCALE,0
        for j in range(1,61):
            dr,di=(dr*ur-di*ui)//(SCALE*j),(dr*ui+di*ur)//(SCALE*j)
            xr,xi=xr+dr,xi+di
        for _ in range(12):
            xr,xi=(xr*xr-xi*xi)//SCALE,(2*xr*xi)//SCALE
        return acb(A(Q(xr,SCALE)),A(Q(xi,SCALE)))

    for ix,(wr,wi) in enumerate([(Q(6),Q(0)),(Q(0),ps*168),(Q(0),Q(1699)),(Q(-1548),Q(0)),(Q(-1),Q(1699))]):
        save(f'e_star_sample{ix}_error',abs(e_star(wr,wi)-acb(A(wr),A(wi)).exp()),upper='1e-68')

    # Numerical values of the analytic propagation bounds. These assertions
    # do not construct the primitive masses or execute floor-matrix products.
    primitive_row=A(15).exp()*(A('1e-60')+3*A('1e-63')+floorerr)
    save('primitive_higher_row_error_bound',primitive_row,upper='1e-52')
    primitive_moment=(230+A('1e-59'))*A('1e-52')+3*A(15).exp()*A('1e-59')
    save('primitive_moment_error_bound',primitive_moment,upper='1e-48')
    eU=A('1e-44')
    eVp=A(0)
    for j in range(9):
        eVp=5*eVp+34*eU+A('1e-77')
        save(f'power_U_error_step{j}',eU,upper='1e-36')
        save(f'power_V_error_step{j}',eVp,upper='1e-34')
        if j<8: eU=7*eU+A('1e-77')
    save('power_U_final_error_bound',eU,upper='5.765e-38')
    save('power_V_final_error_bound',eVp,upper='6.529e-36')
    save('X_column_error_bound',2*(eVp*20000+36*A('1e-43'))+336*A(eps),upper='2.612e-31')
    list_error=41*4*(230*3*A(15).exp())*A('1e-29')
    moment_error=41*4*6*A('1e-48')
    save('L_row_list_error_bound',list_error,upper='3.700e-18')
    save('L_row_primitive_error_bound',moment_error,upper='1e-44')
    save('L_row_entry_error_bound',list_error+moment_error,upper='1e-16')

    def U(r,w,c):
        return (800*(A(w)+A(c))*(-A('.70')*r).exp()/(1-(-A('.70')).exp())
           +A('5.3')*(A('2.54')*A(w)/r+2*A(c))*(-A('.187')*r).exp()/(1-(-A('.187')).exp()))
    save('U168_unit',U(168,1,0),upper='1.0670e-14')
    save('U168_reference',U(168,5,'.02'),upper='8.1575e-14')
    save('U91_reference',U(91,5,'.02'),upper='2.2711e-7')
    # The local rational proof of the two distant target tails. Positivity of
    # the exponential series gives exp(59/25)>P7>21/2, hence rho<2/21.
    p7=sum(Q(59,25)**j/Q(math.factorial(j)) for j in range(8))
    assert p7>Q(21,2)
    cjet=Q(548,413)
    rho_upper=Q(2,21)
    target168=cjet*rho_upper**168/(1-rho_upper)
    target91=cjet*rho_upper**90/(1-rho_upper)
    assert target168<Q('1e-170')
    assert target91<Q('1e-89')
    save('target_tail_above168_bound',A(target168),upper='1e-170')
    save('target_tail_from91_bound',A(target91),upper='1e-89')
    save('tail_reference_residual_bound',U(168,5,'.02')+A('1e-170'),upper='8.3e-14')
    save('high_list_norm_bound',U(91,5,'.02')+A('1e-89'),upper='2.4e-7')
    jet=(1+(1+A('2.12'))/A('2.36'))/A('1.75')*(-A('2.36')*11).exp()/(1-(-A('2.36')).exp())
    save('finite_dropped_jets',jet,upper='7.7915e-12')
    save('finite_power_residual',A('.004')**8*20000,upper='1.4e-15')
    save('finite_reference_residual_bound',A('8e-12')+A('1e-24')+A('1.4e-15'),upper='1e-11')
    beta=A('1.1e-14')
    ut=(A('8.3e-14')+beta*40*A('1e-11'))/(1-beta*(1+40*4000))
    uf=40*(A('1e-11')+4000*ut)
    save('total_exact_list_correction',uf+ut,upper='1.3681e-8')
    save('reference_list_norm', (A('2.3')+A('5.6')/A('2.36'))*sum((-A('2.36')*(n-1)).exp() for n in [1,3,4,7,9]),upper='4.7185')
    save('deleted_quotient_error',36*A('2e-8')*3*(3*pi)**2/2,upper='9.5933e-5')

    included_moments=41*4*5*A('1e-31')
    save('half_gap_included_moment_error',included_moments,upper='1e-28')
    half_gap_bounds={0:'1.8e-19',1:'1.0e-11',3:'3.0e-16',4:'2.0e-11'}
    for mm,yy,nu in [(0,A('.5'),0),(1,A(1),2),(3,A(1),2),(4,A('1.5'),2)]:
        ll=41+nu
        terms=[(-pi*z(A(Q(j,6))).imag*mm).exp()*(pi*abs(z(A(Q(j-1,6))))*yy)**ll for j in range(1,7)]
        # Appendix A bounds all six nonnegative candidates by their sum,
        # which also bounds the maximum in the analytic remainder.
        bound=yy**(-nu)*36*5/(math.factorial(ll)*(1-3*pi*yy/(ll+1)))*((pi*yy)**ll+3*sum(terms))
        save(f'H_Taylor_tail_m{mm}',bound,upper=half_gap_bounds[mm])
        save(f'half_gap_polynomial_error_m{mm}',bound+included_moments,upper='1e-8')
    save('T_Taylor_tail_m0',A(6).exp()/6*3**41/math.factorial(41)/(1-A(3)/42),upper='8e-29')
    save('T_Taylor_tail_m1',A(6)*6**41/math.factorial(43)/(1-A(6)/44),upper='1e-20')
    s=A('89.5')
    tail=(36*pi*pi*A('2.4e-7')+3*(3*pi)**2*36*5*(-A('.70')*s).exp()
          +A('1.25')*(A('1.32')*pi)**2*(A('2.54')*5/s+A('.04'))*(-A('.187')*s).exp()
          +A('2.36')*(-A('2.36')*(s-1)).exp())
    save('tail_second_derivative_bound',tail,upper='8.5485e-5')
    save('P_midpoint_smallest_ratio',12-8*A(2).sqrt(),lower='.6862')

    out['result']='All scalar assertions certified with 512-bit Arb balls or exact integer/Fraction arithmetic.'
    return out



def main(argv=None):
    options = parse_options(__doc__, argv, reject_optimized=True)
    provenance = run_metadata(options, 'arithmetic_bounds.py', 512)
    with managed_output(options, ('arithmetic_bounds.json', 'arithmetic_bounds.log'),
                        'arithmetic_bounds.json') as files:
        with redirect_stdout(Tee(sys.stdout, files['arithmetic_bounds.log'])), \
                redirect_stderr(Tee(sys.stderr, files['arithmetic_bounds.log'])):
            print(f"input_sha256 {options.binding['input_sha256']}", flush=True)
            print(f"verifier_sha256 {provenance['verifier_sha256']}", flush=True)
            started = time.perf_counter()
            try:
                result = run_certificate()
                recheck_inputs(options)
                provenance['elapsed_seconds'] = time.perf_counter() - started
                result['_provenance'] = provenance
                files['arithmetic_bounds.json'].write(json.dumps(result, indent=2)+'\n')
                files['arithmetic_bounds.json'].flush()
                print(result['result'])
                print(f"elapsed_seconds {provenance['elapsed_seconds']:.6f}")
                print('result_file arithmetic_bounds.json')
            except Exception:
                traceback.print_exc()
                raise
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
