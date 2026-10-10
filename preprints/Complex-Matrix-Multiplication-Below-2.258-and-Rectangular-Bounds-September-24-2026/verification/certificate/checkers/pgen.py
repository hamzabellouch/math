Q=1<<224;N=420
def chart():
 Z=[18623,-2696,-2677,194,393,17,1,8]+[0]*N
 P=[[0]*(N+1) for i in range(N+1)];D=[r.copy() for r in P]
 for k in range(N+1):
  for i in range(1+k//2):
   j=k-i;n=Q*Z[k];w=100000
   if i:
    w=D[0][0]*i*j;n=0
    for x in range(i):
     for y in range(int(x==0),j):
      h=(1+y-x)%3;a=i-x-1+h;b=j-y+1-h
      n-=D[x][y]*P[a][b]*(b*(b-1) if h==0 else a*b if h==1 else a*(a-1))
   P[i][j]=P[j][i]=p=(n+w//2)//w
   D[i][j]=D[j][i]=72*p+Q*(8 if k==0 else 2 if k==1 else -1-i if k==2 else 0)
 return [[P[k-i][i] for i in range(k+1)]for k in range(N+1)]
def certify(P):
 T=10**32
 def totals(x,y):
  return [1+sum(map(abs,row))*T*x**k//(Q*y**k)for k,row in enumerate(P)]
 R,S=31,25
 v=totals(R,S)
 assert 1000*sum(k*S*t for k,t in enumerate(v))<592*T*R
 assert sum(k*(k-1)*S**2*t*1000 for k,t in enumerate(v))<3050*T*R**2
 u=v.copy();u[:41]=41*[0]
 assert 10**4*sum(u)<2*T
 assert sum(k*S*t*1000 for k,t in enumerate(u))<6*T*R
 assert 36*S*S*10**12*sum(k*k*t*(2*a+(j<=2)*(T//5))
      for k,t in enumerate(v)for j,a in enumerate(v)if j+k>N)<30*(R*T)**2
 w=totals(5,4)
 assert sum(t*(4*k)**6 for k,t in enumerate(w))<3890000*T*5**6
