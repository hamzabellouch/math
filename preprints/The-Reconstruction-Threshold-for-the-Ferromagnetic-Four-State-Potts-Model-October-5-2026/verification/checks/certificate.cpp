#include<bits/stdc++.h>
#include<boost/multiprecision/cpp_int.hpp>
using namespace std;
using R=long long;
using RR=boost::multiprecision::cpp_int;

RR Pow(RR a,int n){RR r=1;while(n--)r*=a;return r;}
RR gcdB(RR a,RR b){RR c;while(b!=0){c=a%b;a=b;b=c;}return a;} 
using v=array<int,4>;
using V=array<R,4>;
vector<v> l[20];int id_[20][20][20][20]; R fact[21];
int id(int d,v x){return id_[d][x[0]][x[1]][x[2]];} int S(int d){return l[d].size();}
v operator+(v a,v b){for(int i=0;i<4;i++)a[i]+=b[i];return a;}
v e(int j){v a={};a[j]=1;return a;}
void init(){
 fact[0]=1;
 for(int d=0;d<20;d++){ if(d)fact[d]=d*fact[d-1]; // l[1] idx 0..3
 for(int i=d;i>=0;i--)for(int j=d-i;j>=0;j--)for(int k=d-i-j;k>=0;k--){id_[d][i][j][k]=S(d);l[d].push_back({i,j,k,d-i-j-k});}
 }}
R coef(v a){return fact[accumulate(a.begin(),a.end(),0)]/(fact[a[0]]*fact[a[1]]*fact[a[2]]*fact[a[3]]);}
struct P{
 int d;RR den=1;vector<RR> b;
 explicit P(int n,R r=0):d(n),b(S(n)*S(n),r){}
 RR & operator()(int i,int j){return b[i*S(d)+j];}
 RR const& operator()(int i,int j)const{return b[i*S(d)+j];}
};
P ones(int d){P r(d);for(int i=0;i<S(d);i++)for(int j=0;j<S(d);j++) r(i,j)=coef(l[d][i])*coef(l[d][j]); return r;}
P operator*(const P&a,const P&b){
 int m=a.d,n=b.d,d=m+n;
 P c(d); vector<int>w(S(m)*S(n));
 for(int i=0,h=0;i<S(m);i++)for(int j=0;j<S(n);j++)w[h++]=id(d,l[m][i]+l[n][j]);
 // b smaller
 for(int j=0;j<S(n);j++)for(int k=0;k<S(n);k++){RR B=b(j,k);if(B==0)continue;for(int i=0;i<S(m);i++){
   RR*z=&c(w[i*S(n)+j],0); for(int h=0;h<S(m);h++) z[w[h*S(n)+k]]+=a(i,h)*B;
 }}
 c.den=a.den*b.den;return c;
}
P operator*(RR r,P a){for(auto&x:a.b)x*=r;return a;}
P divi(P a,R b){ a.den*=b;return a;}
P lift(P a,int d){while(a.d<d)a=a*ones(1);return a;}
P operator+(P a,P const&b){if(a.d<b.d)a=lift(a,b.d); if(b.d<a.d)return a+lift(b,a.d);RR g=gcdB(a.den,b.den), r=a.den/g,h=b.den/g;for(int i=0;i<a.b.size();i++)a.b[i]=a.b[i]*h+b.b[i]*r;a.den*=h;return a;}
P operator-(P a,P const&b){return a+(R(-1)*b);}

using shape=array<V,4>;// stores scaled vertex coordinates
shape start(){shape m={};for(int i=0;i<4;i++)for(int j=0;j<=i;j++)m[i][j]=12*(1<<24)/(i+1);return m;}
const int had[3][4]={{1,1,-1,-1},{1,-1,1,-1},{1,-1,-1,1}};
vector<R> h={0,0,1000,-100,-150,300,-20,70,-510};
vector<R> f={0,4000,-3000,700,-4000,-800,0,0,0};
vector<R> g={1000,-1610,-3100,773,4000,-3980,0,0,0};int deg[]={0,2,3,4,4,5,6,6,6};
vector<P> inv(array<P,4>&m){
 vector<P>x(3,P(1));for(int i=0;i<3;i++)for(int j=0;j<4;j++)x[i]=x[i]+R(had[i][j])*m[j];
 P u=x[0]*x[1]*x[2];
 P a=x[0]*x[0],b=x[1]*x[1],c=x[2]*x[2],t=a+b+c,s=t*t,p=a*b+a*c+b*c;
 return {ones(0),t,u,s,p,u*t,s*t,p*t,u*u};
}
P dot(vector<R>&c,vector<P>&x,P&z){
 int i=c.size()-1;while(!c[i])i--;
 // efficiently 
 P sum=P(0);int d=x[i].d;
 for(int j=0;j<=i;j++){if(c[j]){
 P r=x[j];while(r.d<d)r=r*z;sum=sum+c[j]*r;}}
 return divi(sum,1000);
}
struct dat{shape a,b; P K; vector<P>N;vector<P>D;P t;
int k;
};
int mode=0;P operator*(P a,R r){return r*a;} // move earlier
// subdivide coefficients homogeneous actual
P sub(P const&o,bool y,int i,int j){//replace vertex i by midpoint i,j. new poly o(old) old variable w_i=w_i'/2 and w_j=w_j'+w_i'/2
 int d=o.d; P r(d);
 for(int u=0;u<S(d);u++){
 v q=l[d][u]; R c=R(1)<<(d-q[i]); 
 for(int b=0;b<=l[d][u][j];b++){
 int H=id(d,q);if(!y){RR*x=&r(H,0);for(int n=0;n<S(d);n++)x[n]+=c*o(u,n);}
 else for(int n=0;n<S(d);n++) r(n,H)+=c*o(n,u);
 c=(c*q[j])/(2*(b+1));q[i]++;q[j]--;
 }}
 r.den=o.den*(1<<d); return r;
}
// initialization Taylor lower
static dat make(){
 shape a=start();
 array<P,4> A={P(1),P(1),P(1),P(1)},B=A;
 P one=ones(1);for(int l=0;l<4;l++)for(int i=0;i<4;i++)for(int j=0;j<4;j++){A[l](i,j)=a[i][l];B[l](i,j)=a[j][l];}
 for(auto m:{&A,&B})for(auto &q:*m){for(auto &x:q.b)x>>=24;q.den=12;}
  vector<P>L=inv(A),M=inv(B); // product polynomials bivar but L depends only a "real". dot
 P hL=dot(h,L,one), hM=dot(h,M,one);
 auto tensor=[](P const&w,P const&t){ // w only a, t only b. return S degree max
 int d=max(w.d,t.d);P r(d); P x=lift(w,d),y=lift(t,d);
 for(int i=0;i<S(d);i++)for(int j=0;j<S(d);j++)r(i,j)=x(i,0)*y(0,j);
 r.den=x.den*y.den;return r;};
 vector<R>&c=mode?g:f;
 P K=-1*(tensor(hL,dot(c,M,one))+tensor(dot(c,L,one),hM));
 if(!mode)K=K+L[1]+M[1]-divi(tensor(L[1],M[3])+tensor(L[3],M[1]),1000);// strict 
 P Taylor=K; dat r={a,a,24*K,{},{},24*K};int k=mode?5:1;r.k=k;
 v idx={0,1,2,3};do{
 array<P,4> U=A;
 for(int l=0;l<4;l++)for(int i=0;i<4;i++)for(int j=0;j<4;j++)U[l](i,j)=4*a[i][l]*a[j][idx[l]];
 for(auto&q:U){for(auto&x:q.b)x>>=48;q.den=144;}
  P z=U[0]+U[1]+U[2]+U[3];
 vector<P> x=inv(U);
 P N=mode?dot(h,x,z):-1*x[1];P D=z;while(D.d<k)D=D*z;
 r.N.push_back(N);r.D.push_back(z);
 P w=z-one; // 1/z^k approx
 P w2=w*w;
 R m=mode?1:6;// need h>=-.5
 P up=N+divi(m*(D*z),2),q=one -R(k)*w+R(k*(k+1)/2)*w2-R(k*(k+1)*(k+2)/6)*(w2*w)+R(k*(k+1)*(k+2)*(k+3)/24)*(w2*w2)-R(k*(k+1)*(k+2)*(k+3)*(k+4)/120)*(w2*w2*w);
 r.t=r.t+up*q-divi(m*z,2);
 }while(next_permutation(idx.begin(),idx.end()));
 return r;
}
dat sub(dat const&a,bool y,int i,int j){
 dat r={a.a,a.b,sub(a.K,y,i,j),{},{},a.t.b.empty()?a.t:sub(a.t,y,i,j),a.k};
 V&b=y?r.b[i]:r.a[i];for(int h=0;h<4;h++)b[h]=(b[h]+(y?r.b[j][h]:r.a[j][h]))/2;
 for(int n=0;n<a.N.size();n++){r.N.push_back(sub(a.N[n],y,i,j));r.D.push_back(sub(a.D[n],y,i,j));} return r;
}
int nodes=0,lp=0,lt=0,depth=0;

using Mat=vector<vector<R>>;
map<pair<int,int>,Mat> T;
Mat const&ev(int x,int y){ if(T.count({x,y}))return T[{x,y}]; 
 Mat m(S(y),vector<R>(S(x)));
 for(int i=0;i<S(y);i++)for(int j=0;j<S(x);j++){R z=1;for(int k=0;k<4;k++)z*=Pow(RR(l[y][i][k]),l[x][j][k]).convert_to<R>();m[i][j]=z;}
 return T[{x,y}]=m;}
Mat inverse(Mat Q){
 // B/960 inverse of evaluation
 int n=S(3); Mat B(n,vector<R>(n));
 for(int j=0;j<n;j++){
    map<v,R> p;p[v{0,0,0,0}]=960;
    R den=1;
    for(int h=0;h<4;h++)for(int m=0;m<l[3][j][h];m++){
       map<v,R> b;
       for(auto q:p)for(int t=0;t<4;t++)b[q.first+e(t)]+=q.second*(3*(t==h)-m);
       p=b;den*=m+1;
    }
    for(auto q:p)B[id(3,q.first)][j]=q.second/den;
 }
 return B;}
P act(P const&a,Mat const&m,int d){
 P r(d);int n=m.size(),h=S(a.d);
 vector<RR>v(h);
 for(int i=0;i<n;i++){ fill(v.begin(),v.end(),0);for(int j=0;j<h;j++){ R x=m[i][j];if(x!=0)for(int k=0;k<h;k++)v[k]+=a(j,k)*x;}
 for(int j=0;j<n;j++)r(i,j)=inner_product(v.begin(),v.end(),m[j].begin(),RR(0));}
 r.den=a.den; // evaluation factor caller
 return r;}
const int degI=3;
bool testP(dat const&r){
 int k=r.k; P F(degI);RR cost=0,Budget=RR(1)<<32;
 static Mat I=inverse(ev(degI,degI));
 for(int n=0;n<24;n++){
 P const&d=r.D[n],&b=r.N[n];
 P f=act(b,ev(k+1,degI),degI);f.den*=Pow(3,2*(k+1));
 P M=act(d,ev(1,degI),degI);M.den*=9;
 RR sc=Budget*Pow(M.den,k);
 for(int i=0;i<f.b.size();i++)f.b[i]=M.b[i]==0?RR(0):RR((sc*f.b[i])/(f.den*Pow(M.b[i],k))); // truncate towards zero
 f.den=Budget;
 f=act(f,I,degI); f.den*=960*960;
 P o=f,w=ones(degI); for(int i=0;i<k;i++)o=o*d,w=w*d;
 o=b-o;
 // c approx ceil
 RR c=0;RR fac=Budget*w.den;
 RR big=o.den;
 for(int i=0;i<o.b.size();i++)if(o.b[i]<0){assert(w.b[i]>0);
 RR a=-o.b[i]*fac,v=w.b[i]*big;if(a>c*v)c=(a+v-1)/v;
 }
 cost+=c;F=F+f;
 }
 P bound=ones(0);bound.den=Budget;bound=cost*bound;
 auto K=r.K+F-bound;
 return *min_element(K.b.begin(),K.b.end())>=0;
}
bool uniform(shape const&a){for(auto&v:a)if(v[3]==3*(1<<24))return true;return false;}
bool goodT(P const&t){return *min_element(t.b.begin(),t.b.end())>=0;}
void run(dat r,int d){
 nodes++;depth=max(depth,d);
 if(nodes%100==0)cerr<<mode<<": "<<nodes<<" "<<d<<" "<<lp<<" "<<lt<<endl;
 if(!r.t.b.empty()&&goodT(r.t)){lt++;return;}
 if(!uniform(r.a)&&!uniform(r.b)){ if(testP(r)){lp++;return;} ;}
 if(d>=24){cerr<<"fail "<<endl;for(auto a:{r.a,r.b}){for(auto q:a){for(R x:q)cerr<<x<<",";cerr<<"|";}cerr<<endl;}exit(1);}
 // edge longest
 using Z=tuple<R,bool,int,int>;Z z(-1,false,-1,-1);
 for(bool y:{false,true}) for(int i=0;i<4;i++)for(int j=0;j<i;j++){shape&a=y?r.b:r.a;R w=0;for(int u=0;u<4;u++)w+=(a[i][u]-a[j][u])*(a[i][u]-a[j][u]);if(a[i][3]==3*(1<<24)||a[j][3]==3*(1<<24))w*=16;z=max(z,Z(w,y,i,j));}
 auto [w,y,i,j]=z;run(sub(r,y,j,i),d+1);run(sub(r,y,i,j),d+1);
}
int main(int argc,char**argv){init();mode=argc>1;run(make(),0);cerr<<"done "<<nodes<<" "<<depth<<" lp="<<lp<<" lt="<<lt<<"\n";}
