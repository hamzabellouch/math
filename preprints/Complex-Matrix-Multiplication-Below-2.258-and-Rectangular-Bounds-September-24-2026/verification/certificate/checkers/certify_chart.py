import sys
n,q=map(int,sys.argv[2:]); f=open(sys.argv[1]); g=open('qP')
Q=1<<q; S=1<<224; U=1<<160
rd=rn=1; D=[[]for _ in range(3)]; A=[[]for _ in range(3)]
dif236=dif420=0; results=[0]*3; rnd=0
for k in range(n+1):
 p=[int(next(f))for _ in range(k+1)]
 assert p==p[::-1]
 v=[int(next(g))for _ in p] if k<=420 else [0]*len(p)
 def up(x,y):return (x+y-1)//y
 def scale(x,m=0):return up(U*rn*x*25**m,Q*rd*31**m)
 small=up(U*rn*sum(abs(a*S-b*Q)for a,b in zip(p,v)),Q*S*rd)
 dif236+=small if k<=236 else scale(sum(map(abs,p)))
 for i in range(3):results[i]+=small*k**i
 d=[0]*3;a=[0]*3
 for i,b in enumerate(p):
  j=k-i
  c=72*b+(8 if k==0 else 2 if k==1 else -2 if (i,j)==(1,1) else -1 if k==2 else 0)*Q
  d[(i-j)%3]+=abs(c)
  a[0]+=abs(b)*i*j
  a[1]+=abs(b)*j*(j-1)
  a[2]+=abs(b)*i*(i-1)
 for i in range(3):
  D[i].append(scale(d[i])); A[i].append(scale(a[i],2))
 if k>=2:rnd+=scale((k+1)*k**2*36,2)
 rn*=31;rd*=25
tail=sum(sum(d[x]*sum(a[n-x+1:])for x in range(n+1))for d,a in zip(D,A))
print('qP236',dif236/U,'qP420 jet', [a/U for a in results])
print('LP', tail/U**2+rnd/U, 'target <=1e-20',tail+rnd*U<=U*U//10**20)
import json
from pathlib import Path
out={'n':n,'q':q,'radius_numerator':31,'radius_denominator':25,'difference_degree236_upper':str(dif236),'difference_jet_upper':list(map(str,results)),'difference_denominator':str(U),'residual_numerator_upper':str(tail+rnd*U),'residual_denominator':str(U*U),'residual_upper_decimal':str((tail+rnd*U)/(U*U)),'passes_1e20':tail+rnd*U<=U*U//10**20}
Path(sys.argv[1]+'.certificate.json').write_text(json.dumps(out,indent=2)+'\n')

