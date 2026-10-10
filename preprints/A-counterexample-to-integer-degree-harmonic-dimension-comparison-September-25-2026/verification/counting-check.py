"""Exact rational check of the finite spectral selection; independent of the metric construction.

m=15, q=101/100, c=147/1000, epsilon=1/100,
alpha^2=99853/100000. Upper bounds on exponents have denominator 2*10^8.
All multiplicities, inequalities, and reported counts use integer arithmetic.
"""
from math import comb, isqrt
from time import monotonic

m, s, k = 15, 8, 50000
h = m - 1
alpha_num, alpha_den = 99853, 100000
q_num = 101
Q = 10**8
R = 2*Q

def dim(l):
    return comb(m+l,m) - (comb(m+l-2,m) if l>=2 else 0)

def total_dim(l):
    return comb(m+l,l) + comb(m+l-1,l-1)

# Sufficient full-degree test: B_l < alpha^2*k*(k+h).
# The largest eigenvalue is <= alpha^-2*B_l (strictly below for odd l).
lf = k
while lf*(lf+h)*alpha_den >= alpha_num*k*(k+h):
    lf -= 1
assert (lf+1)*(lf+1+h)*alpha_den >= alpha_num*k*(k+h)
assert lf*(lf+h)*alpha_den < alpha_num*k*(k+h)

# lambda_min=alpha^-2*(B_l-l^2/101).
lh = k
while alpha_den*(q_num*lh*(lh+h)-lh*lh) < q_num*alpha_num*k*(k+h):
    lh += 1
lh -= 1

selected = total_dim(lf)-dim(0)-dim(1)
full_l, partial_l = 0, 0
start=monotonic()
for l in range(lf+1, lh+1):
    B=l*(l+h)
    den=q_num*alpha_num
    base_mult=comb(l+s-1,s-1) # (b,l-b) harmonic multiplicity for b=0.
    count, upper_sum=0,0
    for b in range(l//2+1):
        mult=base_mult*(1 if 2*b==l else 2)
        num=alpha_den*(q_num*B-(2*b-l)**2)
        radicand_num=Q*Q*(h*h*den+4*num)
        sqrt_upper=isqrt(radicand_num//den)+1
        # sqrt_upper>Q*sqrt(h^2+4*lambda); hence d_upper/R>d.
        assert sqrt_upper*sqrt_upper*den > radicand_num
        d_upper=sqrt_upper-h*Q
        if upper_sum+mult*d_upper < k*R*(count+mult):
            count += mult
            upper_sum += mult*d_upper
        else:
            assert d_upper>k*R
            available=k*R*count-upper_sum
            take=max(0,min(mult,(available-1)//(d_upper-k*R)))
            count += take
            upper_sum += take*d_upper
            break
        if b<l//2:
            old=base_mult*(s+b-1)*(l-b)
            divisor=(b+1)*(s+l-b-2)
            assert old%divisor==0
            base_mult=old//divisor
    assert count==0 or upper_sum<k*R*count
    assert count<=dim(l)
    full_l += count==dim(l)
    partial_l += 0<count<dim(l)
    selected += count

denominator=total_dim(k)
print('parameters:',dict(m=m,s=s,k=k,q='101/100',c='147/1000',epsilon='1/100',alpha_squared='99853/100000'))
print('degrees checked individually:',lf+1,lh)
print('number fully/partially selected among checked degrees:',full_l,partial_l)
print('selected=',selected)
print('Euclidean comparator=',denominator)
print('strict surplus=',selected-denominator)
print('ratio=',selected/denominator)
print('exact count proves (3):',selected>denominator)
print('seconds=',monotonic()-start)
assert selected>denominator
