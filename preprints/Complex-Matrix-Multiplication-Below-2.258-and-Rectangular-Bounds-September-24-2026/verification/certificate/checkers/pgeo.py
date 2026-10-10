Q=1<<224
f=open('qP')
P=[[int(next(f)) for j in range(k+1)]for k in range(421)]
Rnum=31; Rden=25
N=480;K=40;T=1<<45
def trig(b):
 t=T*(b%(12*N))*3141592653589793238//(6*N*10**18)
 z=[T,t]
 for i in range(2,65): z.append(-z[-2]*t*t//(i*(i-1)*T*T))
 return sum(z[::2]),sum(z[1::2])
tr=[[[trig(m*b) for m in range(K+1)]for b in (2*i+1,4*N+2*i+1,8*N+2*i+1)]for i in range(N)]
def dot(a,b):
 return sum(u*v for u,v in zip(a,b))//T
def check(j):
 x=Rnum*(2*j+1);y=2*N*Rden
 val=[0]*(K+1);dr=val.copy();dt=val.copy()
 for k in range(K+1):
  for i,p in enumerate(P[k]):
   m=abs(k-2*i);val[m]+=T*p*x**k//(y**k*Q)
   u=T*p*x**k*y
   dr[m]+=k*u//(x*y**k*Q);dt[m]-=m*u//(x*y**k*Q)
 for tri in tr:
  E=[];ar=[];at=[];d=[]
  ps=ra=ta=0
  for row in tri:
   c,s=zip(*row);p=dot(val,c);r=(T+x*c[1]//y)//3
   a=dot(dr,c);b=dot(dt,s)
   E.append(r+2*p);ar.append(c[1]//3+2*a);at.append(-s[1]//3+2*b)
   ps+=p;ra+=a;ta+=b;d.append(r*(T-r)//T+2*p)
   assert 10000*p>=516*T
  e=E[1]-ps
  assert 10000*(min(E[0],E[2])-ps)>=550*T
  avg=sum(d)//3;assert 1000*avg>=488*T
  if 1000*e<18*T:
   assert 1000*(ra-ar[1])>=183*T
   assert 10**8*((ra-ar[1])**2+(ta-at[1])**2)>=(3208*T)**2
  if 1000*e>=-8*T:
   assert (9*avg-2*T)**2>=18*sum((a-b)**2 for a,b in zip(d,d[1:]+d[:1]))
import sys
for j in range(*[int(s) for s in sys.argv[1:]]):check(j)
