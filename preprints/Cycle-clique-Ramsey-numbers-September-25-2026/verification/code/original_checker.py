def forests(t,b,first=()):
    if t == 0:
        yield ()
        return
    def seqs(p,left):
        if first <= p <= p[::-1]:
            for tail in forests(t-len(p)-1,left,p):
                yield (p,)+tail
        if len(p) < t-1:
            for q in range(1,left+1):
                yield from seqs(p+(q,),left-q)
    yield from seqs((),b)

def data(P):
    edges = []
    Q = set()
    n = 0
    for p in P:
        Q.add(n)
        for q in p:
            edges.append((n,n+1+q))
            n += 1+q
            Q.add(n)
        n += 1
    J = [set() for _ in range(n)]
    tips = [[] for _ in J]
    for x in Q:
        J[x] = Q-{x}
        tips[x] = [x]
    for a,b in edges:
        for x in range(a,b):
            J[x].add(x+1)
            J[x+1].add(x)
        for x in range(a+1,b):
            tips[x] = [a,b]
    return edges,J,tips

def forbidden(k,L,edges,tips,x,y):
    out = set()
    rest = [(a,b) for a,b in edges if not (a<x<b or a<y<b)]
    for mask in range(1<<len(rest)):
        E = [edge for i,edge in enumerate(rest) if mask & (1<<i)]
        vertices = {v for edge in E for v in edge}
        q0 = sum(b-a-1 for a,b in E)
        e = len(E)+1
        for z in tips[x]:
            if sum(z in edge for edge in E) >= 2:
                continue
            # E is ordered along the chains
            reach = {z}
            for a,b in E:
                if a in reach:
                    reach.add(b)
            for w in tips[y]:
                if z>=w or sum(w in edge for edge in E)>=2:
                    continue
                v = len(vertices | {z,w})
                q = q0+abs(x-z)+abs(y-w)
                if w not in reach:
                    low = L+(e>=len(edges))-q
                    high = k+1-v-q
                    out.update(range(max(1,low),high+1))
    return out

def empty(n):
    return [[set() for j in range(n)] for i in range(n)]

def initial(k,t,P):
    edges,J,tips = data(P)
    n = len(J)
    M = empty(n)
    for y in range(n):
        for x in range(y):
            m = forbidden(k,n-t,edges,tips,x,y)
            M[x][y] = set(m)
            M[y][x] = set(m)
    return J,M

def pack(k,t,M):
    n = len(M)
    req = [set(range(1,j+1)) for j in range(7)]
    W = {}
    for i,row in enumerate(M):
        W[i,-1] = 1
        b = k+1-n+sum(0 in m for m in row)
        if b<=0:
            continue
        u = 1+int(b>=t)
        W[i,0] = u
        for r in (1,2):
            T = sum(req[r]<=m for m in row)
            c = max(b,k*u+1-n+T)
            val = max(u,1+int(c>t)+int(c>max(k,2*t)))
            if val==1 and b==c==t and k+1-n+T>=t:
                val = 2
            if val>u:
                W[i,r] = val
            b,u = c,val
    req[0] = {0}
    adj = {(i,r):{(j,s) for j,s in W if i!=j and req[r+s+2]<=M[i][j]}
           for i,r in W}
    def find(V,bound):
        while V:
            x = V[0]
            if W[x]>bound:
                return True
            V = V[1:]
            Z = [p for p in V if p in adj[x]]
            b = bound-W[x]
            if sum(W[p] for p in Z)>b and find(Z,b):
                return True
        return False
    return find(sorted(W,key=lambda p:-W[p]*sum(W[x] for x in adj[p])),k)

def exact(k,J,M):
    n = len(J)
    A = empty(n)
    for i,row in enumerate(M):
        for j,m in enumerate(row):
            A[i][j].update(m)
    for i in range(n):
        states = {(1<<i,i)}
        for ell in range(1,k+1):
            states = {(used | (1<<y),y) for used,x in states for y in J[x]
                      if not (used & (1<<y))}
            for used,x in states:
                A[i][x].add(k-ell)
    return A

def bad(k,t,J,M):
    return (any(0 in M[i][j] for i in range(len(J)) for j in J[i])
            or pack(k,t,M))

def attach(J,i,j,d):
    H = [set(nb) for nb in J]
    if d==1:
        z = len(H)
        H[i].add(z)
        H[j].add(z)
        H.append({i,j})
    else:
        H[i].add(j)
        H[j].add(i)
    return H

def check(k,t,P):
    J,M = initial(k,t,P)
    if pack(k,t,M):
        return 1
    M = exact(k,J,M)
    while not bad(k,t,J,M):
        new = []
        for i in range(len(J)):
            for j in range(i):
                for d in (0,1):
                    if d in M[i][j] or (d==0 and j in J[i]):
                        continue
                    H = attach(J,i,j,d)
                    if bad(k,t,H,exact(k,H,M)):
                        new.append((i,j,d))
        if not new:
            return 0
        for i,j,d in new:
            M[i][j].add(d)
            M[j][i].add(d)
    return 2

for k in range(5,18):
    counts = [0]*3
    for t in range(max(3,k//2),min(8,k)+1):
        for P in forests(t,k-t):
            counts[check(k,t,P)] += 1
    print(k,*counts)
