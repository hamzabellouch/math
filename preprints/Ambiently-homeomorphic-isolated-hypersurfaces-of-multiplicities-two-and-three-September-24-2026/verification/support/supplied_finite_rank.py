def matrix(N,K):
    fac=list(range(3*N+1))
    for p in range(2,3*N+1):
        if fac[p]==p:
            for x in range(p*p,3*N+1,p):
                fac[x]=p
    # fac[x] for x>1 is a prime divisor
    table=[]
    def column(b):
        col={}
        for r,ns in enumerate(((N-b,-b),(2*N+b,2*N-b,b-3*N,-b-N))):
            for x in ns:
                s=1 if x>0 else -1
                x=abs(x)
                while x>1:
                    p=fac[x]
                    if p>K:
                        return None
                    col[r,p]=col.get((r,p),0)+s
                    x//=p
        return col
    for b in range(1,(N+1)//2):
        if b%3:
            col=column(b)
            if col is not None:
                table.append({i:k for i,k in col.items() if k})
    def counts():
        cnt={}
        for col in table:
            for i in col:
                cnt[i]=cnt.get(i,0)+1
        return cnt
    cnt=counts()
    assert (len(table),len(cnt))==(1118,1100)
    while 1 in cnt.values():
        table=[col for col in table if all(cnt[i]>1 for i in col)]
        cnt=counts()
    return table,len(cnt)

def rank(table,prime):
    piv={}
    for col0 in table:
        col={i:v%prime for i,v in col0.items() if v%prime}
        col[-1,0]=1
        while col:
            j=max(col)
            if j not in piv:
                a=pow(col[j],prime-2,prime)
                piv[j]={i:k*a%prime for i,k in col.items()}
                break
            a=col[j]
            for i,k in piv[j].items():
                val=(col.get(i,0)-a*k)%prime
                if val:
                    col[i]=val
                else:
                    col.pop(i,None)
    return len(piv)

M,r=matrix(3**11,4450)
assert (len(M),r,rank(M,1009))==(896,867,868)
