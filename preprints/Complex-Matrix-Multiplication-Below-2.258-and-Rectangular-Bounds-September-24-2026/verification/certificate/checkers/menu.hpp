#pragma once
#include <cstdint>
#include <cstdlib>
#include <cstdio>
#include <cassert>
#include <algorithm>
#include <array>
#include <vector>
#include <limits>
using namespace std;
using I=int64_t;using W=__int128_t;
constexpr I B=I(1)<<52;
I cv(W x){assert(x>=numeric_limits<I>::min()&&x<=numeric_limits<I>::max());return I(x);}
I mu(I a,I b){return cv((W(a)*b)/B);}
I di(I a,I b){assert(b);return cv(W(a)*B/b);}
I lgshort(I x){assert(B<=x&&x<=2*B);I q=di(x-B,x+B),zz=mu(q,q),s=0;
 for(int j=39;j>=0;j--)s=2*B/(2*j+1)+mu(zz,s);
 return mu(q,s);
}
I ln2(){static const I r=lgshort(2*B);return r;}
I iln(I x){assert(1<=x&&x<=512*B);int h=0;
 while(x<B){x*=2;--h;}while(x>2*B){x/=2;++h;}
 return lgshort(x)+h*ln2();
}
I ien(I x){assert(x>=0&&x<=B);return x? -mu(x,iln(x)):0;}
I iexp(I x){int h=0;I l=ln2();while(x>l){++h;x-=l;}while(x<0){--h;x+=l;}assert(-180<h&&h<9);
 I r=B;for(int j=24;j>=1;j--)r=B+mu(x,r)/j;
 for(;h<0;h++)r/=2;
 for(;h>0;h--)r=cv(W(r)*2);
 return max(I(1),r);
}
using T=array<I,3>;using Pm=array<int,3>;constexpr Pm id{0,1,2};
T pm(T x,Pm p){return {x[p[0]],x[p[1]],x[p[2]]};}
I pw(I x,int l){return l==2?mu(x,x):mu(mu(x,x),x);}
I rt(I x,int l){I a=0,b=B*64;assert(0<=x&&x<=512*B);
 // avoid cv overflow for cube beyond cube(8+)
 b=(l==2?32:9)*B;
 while(b-a>1){I m=(a+b)/2;if(pw(m,l)<=x)a=m;else b=m;}return a;
}
I G(T d,int l=16){
 sort(d.begin(),d.end());I a=d[0],b=d[1],c=d[2];if(!l)return b+c;
 a=di(a,c);b=di(b,c);return mu(c,rt(G({B,mu(a,2*B+a),mu(b,2*B+b)},l-1),2));
}
#ifndef GRID
#define GRID 64
#endif
constexpr int K=GRID,S=14;
struct Op{I v=0;int ty=0;Pm a=id,b=id,c=id;int k=0;};
Op tab[S+1][K+1][K+1];
I lerp(I a,I b,I t){return a+mu(t,b-a);}
pair<int,I> loc(I n,I d){assert(0<=n&&n<=d&&d);W x=W(n)*K;int i=min(K-1,int(x/d));return {i,I((x-i*W(d))*B/d)};}
I get(T d,int h){sort(d.begin(),d.end());if(d[2]==0)return 0;
 auto [i,x]=loc(d[0],d[2]);auto [j,y]=loc(d[1],d[2]);auto&t=tab[h];
 return mu(d[2],lerp(lerp(t[i][j].v,t[i][j+1].v,y),lerp(t[i+1][j].v,t[i+1][j+1].v,y),x));
}
T complete(T a,T b){return {mu(a[0],b[0]),mu(a[0]+a[1],b[0]+b[1])-mu(a[0],b[0]),mu(a[0]+a[2],b[0]+b[2])-mu(a[0],b[0])};}
I m3(I a,I b,I c){return mu(mu(a,b),c);}
Op improve(T x,int h){
 Op out{get(x,h)};Pm pa=id,pb=id;T a=x;
 auto chk=[&](I v,Op o,int l){if(v>pw(out.v,l)){o.v=rt(v,l);if(o.v>out.v)out=o;}};
 do{
  T b=pm(x,pb);
  for(int l=0;l<3;l++){
   T w=complete(a,b);
   chk(get(w,h),{0,2,pa,pb},2);
   Pm pc=id;
   do{
    T c=pm(x,pc);
    for(int k=0;k<3;k++){
     chk(get(complete(w,c),h),{0,3,pa,pb,pc,k},3);
     rotate(w.begin(),w.begin()+1,w.end());
    }
   }while(next_permutation(pc.begin(),pc.end()));
   rotate(a.begin(),a.begin()+1,a.end());rotate(pa.begin(),pa.begin()+1,pa.end());rotate(b.begin(),b.begin()+1,b.end());rotate(pb.begin(),pb.begin()+1,pb.end());
  }
  Pm pc=id;
  do{
   T c=pm(x,pc);
   array<T,3> m;for(int i=0;i<3;i++)for(int j=0;j<3;j++)m[i][j]=(i==j)?m3(a[i],b[j],c[i]):(m3(a[i],b[i],c[j])+m3(a[i],b[j],c[i])+m3(a[j],b[i],c[i]));
   for(int k=0;k<2;k++){
    chk(get({get(m[0],h),get(m[1],h),get(m[2],h)},h),{0,4+k,pa,pb,pc,0},3);
    for(int i=0;i<3;i++)for(int j=0;j<i;j++)swap(m[i][j],m[j][i]);
   }
  }while(next_permutation(pc.begin(),pc.end()));
 }while(next_permutation(pb.begin(),pb.end()));
 return out;
}
T datum(int i,int j){return {i*B/K,j*B/K,B};}
void init(){for(int h=0;h<=S;h++)for(int i=1;i<=K;i++){
 tab[h][0][i]=tab[h][i][0]={B+i*B/K};tab[h][0][0]={B};
 for(int j=i;j<=K;j++){T d=datum(i,j);tab[h][i][j]=tab[h][j][i]=(h?improve(d,h-1):Op{G(d)});}
}}

struct Q{T q={};I u=0;
 I score(T ld)const{return u+mu(ld[0],q[0])+mu(ld[1],q[1])+mu(ld[2],q[2]);}
};
T lg(T d){return {iln(d[0]),iln(d[1]),iln(d[2])};}
Q perm(Q q,Pm p){Q out=q;for(int i=0;i<3;i++)out.q[p[i]]=q.q[i];return out;}
struct Cloud{
 vector<pair<I,Pm>> words;
 I m=0,H=0;T count{};
 void word(I w,Pm code){w=max(I(1),w);m+=w;words.push_back({w,code});}
 void calc(int L){assert(!words.empty());I s=0,prev=0;
  for(auto [w,c]:words){s+=w;I v=di(s,m),p=v-prev;prev=v;H+=ien(p);
   for(int k=0;k<L;k++)count[c[k]]+=p;
  }
  assert(prev==B);
 }
};
int cm(int i,int j){if(i+j==0)return 0;if((i==1&&j==2)||(i==2&&j==1))return -1;return i?i:j;}
void groups(Cloud m[3][3],Op o,T x,int L){
 bool parity=o.ty>3;
 for(int i=0;i<3;i++)for(int j=0;j<3;j++)for(int r=0;r<(L==2?1:3);r++){
  Pm code{o.a[i],o.b[j],o.c[r]};I w=m3(x[code[0]],x[code[1]],L==3?x[code[2]]:B);
  int t,s=0;
  if(parity){
   if(i==j){t=i;s=r;}else if(i==r){t=i;s=j;}else if(j==r){t=j;s=i;}else continue;
   if(o.ty==5)swap(t,s);
  }else{
   t=cm(i,j);if(t<0)continue;
   if(L==3)t=cm((3+t-o.k)%3,r);
   if(t<0)continue;
  }
  m[t][s].word(w,code);
 }
}
Q term[S+1][K+1][K+1];
Q Leaf(T d){
 int k=min_element(d.begin(),d.end())-d.begin(),i=(k+1)%3,j=(k+2)%3;Q out;
 assert(d[i]+d[j]);out.q[i]=di(d[i],d[i]+d[j]);out.q[j]=B-out.q[i];out.u=ien(out.q[i])+ien(out.q[j]);return out;
}
Q lookup(T d,int h){
 Q best=Leaf(d);if(h<0)return best;T ld=lg(d);
 I bv=best.score(ld);
 Pm p=id;
 do{
  T x=pm(d,p),lx=pm(ld,p);if(x[0]>x[1]||x[1]>x[2])continue;
  int ii=int((W(x[0])*K*2/x[2]+1)/2),jj=int((W(x[1])*K*2/x[2]+1)/2);
  for(int i=max(1,ii-2);i<=min(K,ii+2);i++)for(int j=max(i,jj-2);j<=min(K,jj+2);j++){
   Q q=term[h][i][j];I v=q.score(lx);if(v>bv){best=perm(q,p);bv=v;}
  }
 }while(next_permutation(p.begin(),p.end()));
 return best;
}
template<class Fn>Q assemble(T d,Op o,Fn child){
 int L=o.ty==2?2:3;bool parity=o.ty>3;
 Cloud m[3][3];groups(m,o,d,L);
 Q q[3];T y{};for(int i=0;i<3;i++){
  for(int j=0;j<(parity?3:1);j++)m[i][j].calc(L);
  if(parity){T x{m[i][0].m,m[i][1].m,m[i][2].m};q[i]=child(x);y[i]=iexp(q[i].score(lg(x)));}
  else {y[i]=m[i][0].m;q[i]={{B,0,0}};}
 }
 Q qt=child(y),out;out.u=qt.u;
 for(int i=0;i<3;i++){
  out.u+=mu(qt.q[i],q[i].u);
  for(int j=0;j<(parity?3:1);j++){
   auto &c=m[i][j];I w=mu(qt.q[i],q[i].q[j]);
   out.u+=mu(w,c.H);
   for(int l=0;l<3;l++)out.q[l]+=mu(w,c.count[l]);
  }
 }
 out.u/=L;
 I rem=B;for(auto &p:out.q){p/=L;rem-=p;}assert(0<=rem&&rem<=21);out.q[0]+=rem;
 assert(-10000<=out.u&&out.u<2*B);
 return out;
}
Q repeat(T d,int n=12){I s=*max_element(d.begin(),d.end());for(auto &x:d)x=max(I(1),di(x,s));
 if(!n)return Leaf(d);Pm p=id;swap(p[0],p[max_element(d.begin(),d.end())-d.begin()]);
 return assemble(d,{0,2,p,p},[&](T x){return repeat(x,n-1);});
}
void initq(){
 for(int h=0;h<=S;h++)for(int i=1;i<=K;i++)for(int j=i;j<=K;j++){
  T d=datum(i,j),ld=lg(d);Q q=repeat(d);
  if(h){
   auto chk=[&](Q r){if(r.score(ld)>q.score(ld))q=r;};
   chk(term[h-1][i][j]);Op o=tab[h][i][j];
   if(o.ty)chk(assemble(d,o,[&](T x){return lookup(x,h-1);}));
   for(int k:{1,3})if(o.ty!=tab[k][i][j].ty&&tab[k][i][j].ty)chk(assemble(d,tab[k][i][j],[&](T x){return lookup(x,h-1);}));
  }
  term[h][i][j]=q;
 }
}
vector<Q> makemenu(){
 init();initq();
 vector<Q> m{{{B,0,0},0},{{0,B,0},0},{{0,0,B},0}};
 for(int i=0;i<=K;i++)for(int j=max(i,1);j<=K;j++){
  T d=datum(i,j);Q q=i?term[S][i][j]:Leaf(d);Pm p=id;do m.push_back(perm(q,p));while(next_permutation(p.begin(),p.end()));
 }
 return m;
}
// Exact LP on coarse projected (q0,q1,u).
constexpr I LOW=I(1)<<30,SH=B/LOW;
struct Pt{I x,y,u;};
Pt pt(Q q){return {q.q[0]/SH,q.q[1]/SH,q.u/SH};}
vector<Pt> lmenu(const vector<Q>&m){vector<Pt> a;for(auto q:m)a.push_back(pt(q));return a;}
I det(Pt a,Pt b,Pt o){return (a.x-o.x)*(b.y-o.y)-(a.y-o.y)*(b.x-o.x);}
struct Tri{
 Pt a,b,c;I D,s;
 Tri(const vector<Pt>&m,Pm p):a(m[p[0]]),b(m[p[1]]),c(m[p[2]]){I d=det(a,b,c);assert(d);D=abs(d);s=d>0?1:-1;}
 T at(Pt p)const{I u=s*det(p,b,c),v=s*det(a,p,c);return {u,v,D-u-v};}
 W dot(T p)const{return W(p[0])*a.u+W(p[1])*b.u+W(p[2])*c.u;}
 W gap(Pt p)const{return W(p.u)*D-dot(at(p));}
};
I solve(T p,const vector<Pt>&m){
 Pt x=pt(Q{p});Pm b=id;
 for(int iter=0;;iter++){
  assert(iter<1000000);Tri g(m,b);T v=g.at(x);assert(*min_element(v.begin(),v.end())>=0);
  int j=-1;W best=0;
  for(int k=0;k<int(m.size());k++){W e=g.gap(m[k]);if(e>best){j=k;best=e;if(iter>=100)break;}}
  if(j==-1)return cv(g.dot(v)*SH/g.D);
  T y=g.at(m[j]);int i=-1;
  for(int k=0;k<3;k++)if(y[k]>0){W d=i<0?-1:W(v[k])*y[i]-W(v[i])*y[k];if(d<0||(d==0&&b[k]<b[i]))i=k;}
  assert(i>=0);b[i]=j;
 }
}
