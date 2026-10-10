"""Exact capacity checks for the bounded parameter ranges."""
import sys
import time

def intermediate():
 for M in [9,10,11,12,13,14]+list(range(15,22)):
  for r in range(1,(M//2 if M%2 else 3*M//2+2)+1):
   if r>={10:8,12:14,14:22}.get(M,999): continue
   n=M*(M+1)//2+2*r
   def bounds(d,e):
    p=[(d-1,2*M-2)] if d>1 else []
    for f in range(e,5):
     q=min(8,(2*M-8-f)//f)
     if q>0:p.append((q,2*r-2+q*(f+1)))
    return p
   for d in range(1,5):
    for e in range(1,5):
     assert any(max(U+V-1,U*V//(i*j))<n for i,U in bounds(d,e)
                     for j,V in bounds(e,d))

def pack(n,k):
 return tuple((n+i)//k for i in range(k))
def parts(n,k,m):
 if not n:
  yield ()
 elif k:
  for x in range(1,min(m,n)+1):
   for a in parts(n-x,k-1,x):yield (x,)+a
def dom(a,b):
 return all(sum(a[:i+1])>=sum(b[:i+1]) for i in range(len(b)))
def strip(a,b):
 A=a+(0,)*(4-len(a)); B=b+(0,)*(4-len(b))
 return all(A[i]>=B[i]>=A[i+1] for i in range(3))
def bal(a):
 if not a:return [()]
 if len(a)%2:return [x+y+(a[i],) for i in range(0,len(a),2)
                  for x in bal(a[:i]) for y in bal(a[i+1:])]
 return [sum((pack(x+x+1,4) for x in a[::2]),())]
def run(m,r):
 n=m*(m+1)//2+2*r; K=2*m-1; c=(r//2+1)*2
 s=1+r%2
 B=[]
 for t,x in ([(2,3),(2,0)] if s==2 else [(0,0),(0,1)]):
  if x>c:continue
  for rest in bal(list(range(4 if x==3 else 3,m-1))):
   z=rest+pack(K+r+t,4)+(pack(x+c,2) if x else (c,))
   B.append(z if x+t else z+(1,))
 def choices(u):return list(parts(u,3,u))
 ev=[tuple(2*z for z in a) for a in choices(c//2)]
 step=[a for a in choices(c+3) if any(strip(a,b) for b in ev)]
 tot=choices(c+3+s)
 bad=[a for a in tot if not any(strip(a,b) for b in step)]
 C=[a+b for a in tot if not any(dom(u,a) for u in bad)
         for b in bal(list(range(4,m-1)))]
 C=set(tuple(sorted(p,reverse=True)) for p in C)
 C=[a for a in C if not any(b!=a and dom(a,b) for b in C)]
 def bound(A,h):
  if not h:return False
  return all(min(sum(A),sum(h[:i])+max(0,i-len(h))*h[-1])<=
        sum(min(i,p) for p in A) for i in range(1,max(A))) # unknown extension
 def hit(h):
  for j,z in (([(len(h)-1,0)] if s==1 else
       [(i,z) for z in [1,3] for i in range(len(h)) if h[i]>=z])):
   a=list(h); a[j]-=z
   for it in range(K+r-z):
    k=max((i for i in range(len(a)) if i!=j and a[i]>max(0,h[i]-4)),
                       default=None,key=lambda i:a[i])
    if k==None:break
    a[k]-=1
   else:
    if any(bound(A,sorted(a,reverse=True)) for A in C):return True
  return False
 def F(h,w):
  return any(sum(w[:d])>=K and
      sum(max(0,(x-d)//2) for x in h[:min(8,(K-7-d)//d)])>=r
      for d in range(1,5))
 def stop(a,b):
  return F(a,b) or F(b,a) or any(bound(A,h) for h in (a,b) for A in B)
 def gen(left,a,b):
  if stop(a,b):return
  k=len(a)
  if k>=4 and min(sum(a[:4]),sum(b[:4]))<K:return
  def fill(u,v):
   return u+[sum(z>=i for z in v) for i in range(k+1,v[0]+1)]+[0]
  if not left:
   u=fill(a,b); v=fill(b,a)
   if min(sum(u[:4]),sum(v[:4]))>=K and not stop(u,v):
    assert hit(u) or hit(v)
   return
  for x in range(1,1+min(left,a[-1]-k if a else n)):
   for y in range((left+x-1)//x,1+min(left+1-x,b[-1]-k if b else x)):
    gen(left+1-x-y,a+[x+k],b+[y+k])
 gen(n,[],[])

def exceptional():
 for m in [10,12,14]:
  for r in range({10:8,12:14,14:22}[m],3*m//2+3):
   # optional: omit calls already following from the two-first-sums
   # rectangle bound of the preceding check
   run(m,r)

if __name__ == '__main__':
 if not __debug__:
  raise SystemExit('Capacity verification requires assertions; run Python without -O.')
 started = time.monotonic()
 if sys.argv[1:] == ['intermediate']:
  intermediate()
 elif sys.argv[1:] == ['exceptional']:
  exceptional()
 elif len(sys.argv) == 3:
  run(int(sys.argv[1]), int(sys.argv[2]))
 else:
  raise SystemExit('Use intermediate, exceptional, or M r')
 print('PASS', *sys.argv[1:], 'elapsed_seconds=%.6f' % (time.monotonic()-started))
