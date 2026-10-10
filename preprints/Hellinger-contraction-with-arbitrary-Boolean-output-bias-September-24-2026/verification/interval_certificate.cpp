#include <algorithm>
#include <cstdint>
#include <cstdio>
using ll = int64_t;
using bign = __int128;
using std::min;
using std::max;

struct invalid {};
constexpr ll unit = 1000000000000LL, limit = 1000000 * unit;
struct I {
    ll a, b;
    I(int k=0) { a=b=unit*k; } // only small integral constants
    static I bounds(bign a, bign b) {
        if (!(a >= -limit && b <= limit && a <= b)) throw invalid{};
        I x; x.a=(ll)a; x.b=(ll)b; return x;
    }
};
bign flo(bign a, bign b) { return a<0 ? -1-((-a-1)/b) : a/b; }
bign cei(bign a, bign b) { return -flo(-a,b); }
I operator+(I x, I y) { return I::bounds(x.a+y.a,x.b+y.b); }
I operator-(I x, I y) { return I::bounds(x.a-y.b,x.b-y.a); }
I operator-(I x) { return I::bounds(-x.b,-x.a); }
I operator*(I x, I y) {
    bign p=(bign)x.a*y.a,q=(bign)x.a*y.b,r=(bign)x.b*y.a,h=(bign)x.b*y.b;
    return I::bounds(flo(min({p,q,r,h}),unit),cei(max({p,q,r,h}),unit));
}
I inv(I x) {
    if (x.a<=0) throw invalid{};
    bign s=(bign)unit*unit; return I::bounds(flo(s,x.b),cei(s,x.a));
}
I operator/(I x,I y) { return x*inv(y); }
ll isqrt(bign n) {
    ll a=0,b=1000*unit+1; // n<=limit*unit
    while(b-a>1) { ll c=(a+b)/2; if ((bign)c*c<=n) a=c; else b=c; }
    return a;
}
I root(I x) {
    if (x.a<0) throw invalid{};
    bign b=(bign)x.b*unit; ll k=isqrt(b);
    return I::bounds(isqrt((bign)x.a*unit),k+((bign)k*k<b));
}
ll mag(I x) { return max(-x.a,x.b); }
I frac(int k) { ll j=(unit/1000)*k; return I::bounds(j,j); } // k/1000

struct J {
    I x,d[3];
    J(I y=I()) : x(y) {}
    J(int y) : x(y) {}
};
J operator+(J a,J b) {
    J c(a.x+b.x); for(int i=0;i<3;i++) c.d[i]=a.d[i]+b.d[i]; return c;
}
J operator-(J a) {
    J c(-a.x); for(int i=0;i<3;i++) c.d[i]=-a.d[i]; return c;
}
J operator-(J a,J b) { return a+(-b); }
J with(I x,J a,J b,I y,I z) {
    J c(x); for(int i=0;i<3;i++) c.d[i]=a.d[i]*y+b.d[i]*z; return c;
}
J with(I x,J a,I y) { return with(x,a,J(),y,I()); }
J operator*(J a,J b) { return with(a.x*b.x,a,b,b.x,a.x); }
J inv(J a) { I q=inv(a.x); return with(q,a,-(q*q)); }
J operator/(J a,J b) { return a*inv(b); }
J root(J a) { I q=root(a.x); return with(q,a,frac(500)*inv(q)); }
template<class T> T sq(T a) { return a*a; }
I rat(I a,I b) {
    I z=a+b;
    if (z.a<=0) return I::bounds(0,unit/2);
    I h=a/z; return I::bounds(max(ll(0),h.a),min(unit/2,h.b));
}
I E(I a,I b) { return a*rat(a,b); }
J E(J a,J b) {
    I h=rat(a.x,b.x); return with(a.x*h,a,b,h*(2-h),-(h*h));
}

template<class T> struct A { T x,y,z,i,j,k,h; }; // 0,1,2,01,02,12,012
template<class T> A<T> operator+(A<T> a,A<T> b) {
    return {a.x+b.x,a.y+b.y,a.z+b.z,a.i+b.i,a.j+b.j,a.k+b.k,a.h+b.h};
}
template<class T> A<T> operator*(A<T> a,A<T> b) {
    return {a.x*b.x,a.y*b.y,a.z*b.z,
            a.x*b.i+a.i*b.y,a.x*b.j+a.j*b.z,a.y*b.k+a.k*b.z,
            a.x*b.h+a.i*b.k+a.h*b.z};
}
template<class T> A<T> operator*(I c,A<T> b) {
    T v(c); return {v*b.x,v*b.y,v*b.z,v*b.i,v*b.j,v*b.k,v*b.h};
}
template<class T> A<T> operator+(I c,A<T> b) {
    T v(c); return {v+b.x,v+b.y,v+b.z,b.i,b.j,b.k,b.h};
}
template<class T> A<T> operator-(I c,A<T> b) { return c+(I(-1)*b); }
template<class T> A<T> inv(A<T> a) {
    T x=inv(a.x),y=inv(a.y),z=inv(a.z);
    T i=-a.i*x*y,j=-a.j*x*z,k=-a.k*y*z,h=-x*(a.h*z+a.i*k);
    return {x,y,z,i,j,k,h};
}
template<class T> A<T> root(A<T> a) {
    T x=root(a.x),y=root(a.y),z=root(a.z);
    T i=a.i/(x+y),j=a.j/(x+z),k=a.k/(y+z),h=(a.h-i*k)/(x+z);
    return {x,y,z,i,j,k,h};
}
I L,U,V,alpha,lambda,mu;
template<class T> A<T> table(T a,T b,T c,T k,int mode) {
    A<T> x{a,b,c,k,k,k,T(0)},q2=1-x*x,q=root(q2),h=2*(q*x);
    A<T> y=L+h*(U+V*h),e=inv(1+h*y);
    if (mode==1)
        return 4*(L*x+q*(I(2)*sq(L)-1-(2*U)*q2+h*(2*L*U-(2*V)*q2+(2*L*V)*h)))*e;
    if (mode==2) return 4*(q2*(q+x*y))*e;
    return 4*(q*(x+q*y))*e;
}
template<class T> T term(A<T> m,T u,T w) {
    T e=E(u,w),o=inv(1+u);
    return ((1-o*e)*m.z + (w+e)*m.k + e*u*(m.h-o*m.j))/(1+w);
}
template<class T> T expr(T u,T v,T j,int mode) {
    T d=j*(2*u+(1-u)*j),w=u+(1-u)*j,t=root(1-(1-u)*d);
    auto m=table(v*u,v*w,v,v,mode),n=table(v*u,v*t,v,v,mode);
    if (mode==1) {
        T F=(1+u*u/(1+u))*m.z+u*u*u*m.j/(1+u);
        T Z=frac(125)*(term(m,u,w)+term(n,u,t));
        T H0=alpha*(4*L-v*m.z)+(1-alpha)*u*u*(4*L-v*u*m.x);
        T di=d*(1-u),wi=1-sq(w);
        return Z*H0+(4*lambda)*di*wi*v*sq(Z)-mu*v*sq(F)/sq(4*L);
    }
    I half=frac(500)*lambda;
    T F=(m.z+u*m.j)/(1+u);
    T Z=frac(125)*((F-m.k-u*m.h)/(1+w)+(u+w)/(u+t)*(F-n.k-u*n.h)/(1+t));
    T H0=(alpha-half)*u*m.x+(1-alpha-half)*m.z+half*(w*m.y+t*n.y);
    return Z*H0-mu*(u+w)*sq(v+F/(4*L));
}
I nroot(I a) { return root(I::bounds(max(a.a,ll(0)),max(a.b,ll(0)))); }
J nroot(J a) { return root(a); }
template<class T> void expr3(T l,T u,T r,T out[3]) {
    T z=1-sq(l)-sq(u),b=sq(r)*z,lp=nroot(sq(l)+b),up=nroot(sq(u)+b);
    auto n=table(l,l,lp,T(1),3),a=table(u,u,up,T(1),2);
    T P=n.z+E(l,lp)*n.j,Q=a.z+u*a.j;
    T Z=(Q+(u+up)*P)/(8*(1-sq(r))*z);
    T W2=sq(1-(u*a.x-l*l*n.x)/(4*L*z));
    I half=frac(500)*lambda;
    out[0]=Z*((alpha-half)*u*a.x+half*up*a.z+(1-alpha)*l*l*n.x+half*b*P)-mu*(u+up)*W2;
    T rest=half*(up-u)*P;
    out[1]=Z*((frac(500)*alpha)*a.x+rest)-mu*W2;
    out[2]=Z*(half*Q+rest)-mu*W2;
}

int lo,hi,mode,depth;
struct B {
    I bounds,center;
    J jet;
    B(ll a,ll b,ll i,ll H,int k) { // subdivide [a,a+b]/1000
        bign n=(a*H+b*i)*(unit/1000),v=b*(unit/1000);
        jet.x=bounds=I::bounds(flo(n,H),cei(n+v,H));
        center=I::bounds(flo(2*n+v,2*H),cei(2*n+v,2*H));
        jet.d[k]=I::bounds(flo(v,2*H),cei(v,2*H));
    }
};
I delta(ll a,ll b) {
    I u=I::bounds(a,a),j=I::bounds(b,b); return j*(2*u+(1-u)*j)/(1+u);
}
bool derivative(I c,J a) { return c.a>mag(a.d[0])+mag(a.d[1])+mag(a.d[2]); }
bool good(B u,B v,B j) {
    if(mode!=3) {
        if(delta(u.bounds.a,j.bounds.a).a>sq(frac(hi)).b||
           delta(u.bounds.b,j.bounds.b).b<sq(frac(lo)).a) return true;
        return expr(u.bounds,v.bounds,j.bounds,mode).a>0 ||
               derivative(expr(u.center,v.center,j.center,mode),expr(u.jet,v.jet,j.jet,mode));
    }
    I a[3],b[3]; J c[3]; bool p[3];
    expr3(u.bounds,v.bounds,j.bounds,a);
    for(int i=0;i<3;i++) p[i]=a[i].a>0;
    if(p[0]||(p[1]&&p[2])) return true;
    expr3(u.center,v.center,j.center,b);
    expr3(u.jet,v.jet,j.jet,c);
    for(int i=0;i<3;i++) if(derivative(b[i],c[i])) p[i]=true;
    return p[0]||(p[1]&&p[2]);
}
bool verify(int d,int a=0,int b=0,int c=0) {
    ll h=ll(1)<<d;
    B u(0,mode==3?600:1000,a,h,0),v(0,mode==3?600:800,b,h,1),
      j(mode==3?lo:0,mode==3?hi-lo:hi,c,h,2);
    try { if (good(u,v,j)) return true; } catch(invalid) {}
    if(d==depth) return false;
    for(int i=0;i<8;i++)
        if(!verify(d+1,2*a+i/4,2*b+i/2%2,2*c+i%2)) return false;
    return true;
}
int main() {
    int data[][8]={{0,36,940,-440,300,960,1000,956},
                   {35,81,940,-440,300,930,1050,953},
                   {80,152,886,-398,250,860,1150,985},
                   {151,254,842,-335,180,770,1150,1024},
                   {253,335,842,-335,180,690,1150,1058},
                   {334,412,842,-335,180,632,1160,1087},
                   {411,479,842,-335,180,583,1160,1111}};
    for(int g=0;g<7;g++) {
        auto p=data[g]; lo=p[0]; hi=p[1]; L=frac(p[2]); U=frac(p[3]);
        V=frac(p[4]); alpha=frac(p[5]); lambda=frac(p[6]); mu=frac(p[7]);
        for(mode=1;mode<=3;mode++) {
            depth = mode==3 ? (g==0?14:7) : (g==3?7:8);
            if(!verify(0)) return 1;
        }
    }
    std::puts("pass");
}
