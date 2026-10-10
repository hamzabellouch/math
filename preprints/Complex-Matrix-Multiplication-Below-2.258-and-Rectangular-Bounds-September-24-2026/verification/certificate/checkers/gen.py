from fractions import Fraction as F
from math import isqrt
B=2**52
BF=2**44
def rnd(x): return (2*x.numerator+x.denominator)//(2*x.denominator)
rc=list(map(F,['.28309034','-.05388682','.00841589','.00450821','-.00680398']))
seed=list(map(F,['.0152567903','.0002597033','-.0014351728','-.0017937434','-.0008593989','-.0002090472','-.0000227468']))
r0=F('.357')
R=F('1.24')
a={(3*i,0):x/F('.32')**(3*i) for i,x in enumerate(seed)}
def g(i,j): return a.get((i,j),F())
NH=112
for d in range(NH-1):
 for i in range(d+1):
  j=d-i
  a[i+1,j+1]=(g(i,j)*d*(d-1)-g(i+2,j-1)*(i+2)*(i+1)-g(i-1,j+2)*(j+2)*(j+1))/(2*(i+1)*(j+1))
with open('dat','w') as f:
 print(*(rnd(x*B) for x in [F('3.1415926535897932384626433832795'),R,r0,F(300000,225925),*rc]),isqrt(3*B*B//4),file=f)
 print(*(rnd(g(i,d-i)*r0**d*B) for d in range(NH+1) for i in range(d+1)),file=f)
 nums=iter(map(int,open('qP').read().split()))
 p=[]
 for d in range(421):
  row=[F(next(nums),2**224) for j in range(d+1)]
  assert row==row[::-1]
  p.append(row)
 A=[R**d*sum(map(abs,row)) for d,row in enumerate(p)]
 print('Ptot',float(sum(A)),'M2',float(sum(d*d*x for d,x in enumerate(A))),'tail',float(sum(A[221:])))
 assert sum(A)<F('.414') and sum(d*d*x for d,x in enumerate(A))<6 and sum(A[221:])<F('6.3e-11')
 print(*(rnd(p[d][i]*(1+(2*i!=d))*R**d*B) for d in range(221) for i in range(d//2+1)),file=f)
 xs=list(map(F,open('newc22').read().split()))
 key=[(i+j,i-j) for i in range(23) for j in range(i%3,min(i,22-i)+1,3)]
 assert len(xs)==len(key)
 ma=[sum(abs(x)*R**d*d**k for x,(d,s) in zip(xs,key)) for k in range(5)]
 print('ma',*map(float,ma))
 assert all(x<v for x,v in zip(ma,[35000,750000,15000000,300000000,6000000000]))
 print(*(rnd(x*R**d*BF) for x,(d,s) in zip(xs,key)),file=f)
# H derivative checks
r,r1,r2=[sum(abs(v)*(3*k)**j for k,v in enumerate(rc)) for j in range(3)]
z1,z2=r+r1,r+2*r1+r2;n=NH
norm=sum(abs(x)*r0**(i+j) for (i,j),x in a.items())
d1=sum(abs(x)*(i+j)*r**(i+j)/r for (i,j),x in a.items())
d2=sum(abs(x)*(i+j)*(i+j-1)*r**(i+j)/r**2 for (i,j),x in a.items())
res=sum(abs(x)*r**k*((i*(i-1)+j*(j-1))/r*(k==n)+k*(k-1)*(k>=n-1)) for (i,j),x in a.items() for k in [i+j])
M=18*z1**2+9*z2+d2*z1**2+d1*z2
print('H',*map(float,[r,z1,z2,norm,d1,d2,res,M]))
assert r<r0 and z2<F('3.16') and norm<2 and res<F('7e-13') and M<68
