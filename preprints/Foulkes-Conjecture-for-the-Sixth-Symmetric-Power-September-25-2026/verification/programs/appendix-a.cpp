
// Compile assertions enabled, e.g. g++ -std=c++17 -O3 -march=native -fopenmp v.cpp
// OpenMP optional; set a moderate OMP_NUM_THREADS (e.g. 4)
#include <memory>
#include <cstdlib>
#include <utility>
#include <iostream>
#include <vector>
#include <array>
#include <algorithm>
#include <cstdint>
#include <chrono>
#include <cstring>
#include <cassert>
#include <iomanip>
#include <numeric>
#include <map>
using namespace std;
using i64=int64_t;
using i128=__int128_t;
ostream& operator<<(ostream& o, const i128 a) {
 if (a<0) return o<<'-'<<-a;
 if (a>9) o<<a/10;
 return o<<int(a%10);
}
const int K=6, M=200*K+50, D=6;
using Index=array<int,D>; // descending parts (+ staircase shift when needed)
i64 rank_tab[D+1][M][M];
void init() {
 // rank_tab[n][w][k] # partitions of w length<=n with smallest of n <k
 rank_tab[0][0][M-1]=1;
 for(int d=1;d<=D;d++)
 for(int w=0;w<M;w++) for(int k=1,t=w;k<M;k++,t-=d)
 rank_tab[d][w][k]=rank_tab[d][w][k-1]+(t<0?0:rank_tab[d-1][t][M-1]);
}
template<bool shifted=false>
int rankp(const Index& l, int w) {
 int idx=0, prev=0;
 for(int j=D-1;j>=1;j--) {
  int p=l[j]-(shifted?(D-1-j):0);
  auto t=rank_tab[j+1][w];
  idx+=t[p]-t[prev];
  w-=p; prev=p;
 }
 return idx;
}
Index shift(Index l) {
 for(int i=0;i<D;i++)l[i]+=D-1-i;
 return l;
}
int straight(Index& l) { // descending with sign
 int inv=false;
 for(int i=1;i<D;i++) {
  int x=l[i], j=i;
  while(j>0&&x>l[j-1]){l[j]=l[j-1]; inv=!inv; j--;}
  if (j>0&&x==l[j-1])return 0;
  l[j]=x;
 }
 return inv?-1:1;
}
i128 get(const vector<i128>& tab, int b, Index l) {
 int s=straight(l); if(!s || l.back()<0)return 0;
 int ix=rankp<true>(l,b*K);
 if (s<0)return -tab[ix];
 return tab[ix];
}

template<class F>
void comp_impl(int w, Index& l, int j, F f) {
 if(j==D-1){l[j]=w;f(l);return;}
 for(int x=0;x<=w;x++){
  l[j]=x;
  comp_impl(w-x,l,j+1,f);
 }
}
template<class F>
void comps(int w, F f) {Index l;comp_impl(w,l,0,f);}
template<class F>
void part_impl(int w, Index& l, int j, F f) {
 if(j==0){l[j]=w;f(l);return;}
 for(int x=(j==D-1?0:l[j+1]);x*(j+1)<=w;x++){
  l[j]=x;
  part_impl(w-x,l,j-1,f);
 }
}
template<class F>
void parts(int w, F f) {Index l;part_impl(w,l,D-1,f);}
vector<vector<i128>> gen(int B) {
 vector<vector<Index>> sub(B+1);
 for(int i=1;i<=B;i++) {
  comps(K,[&](Index l){for(int& x:l)x*=i;sub[i].push_back(l);});
 }
 vector<vector<i128>> tabs(B+1);
 tabs[0]={1};
 #pragma omp parallel
 for(int b=1;b<=B;b++){

  int N=rank_tab[D][b*K][M-1];
  #pragma omp single
  tabs[b].resize(N);

  vector<Index> ps;ps.reserve(N);
  parts(K*b,[&](Index l){ps.push_back(shift(l));});
  #pragma omp for schedule(dynamic,10)
  for(int j=0;j<N;j++){
   const Index& l=ps[j];i128 t=0;
   for(int i=1;i<=b;i++) for(auto& delta:sub[i]){
    Index prev; bool ok=true;
    for(int j=0;j<D;j++)if((prev[j]=l[j]-delta[j])<0){ok=false;break;}
    if(ok && __builtin_add_overflow(t,get(tabs[b-i],b-i,prev),&t))abort();
   }
   if(t<0||t%b){std::cerr<<"bad\n";abort();}
   tabs[b][j]=t/b;
  }

 }
 return tabs;
}


// shorter-length table using the same target recurrence
template<int n>
struct Make {
 vector<vector<i128>> tab{vector<i128>{1}};
 vector<Index> ps;
 vector<vector<Index>> subs;
 int rankn(Index l, int w) const {
  int idx=0, prev=0;
  for(int j=n-1;j>=1;j--) {
   int p=l[j]-(n-1-j);
   auto t=rank_tab[j+1][w];idx+=t[p]-t[prev];
   w-=p;prev=p;
  }
  return idx;
 }
 Make(int B):subs(B+1) {
  comps(6,[&](Index d){
   for(int i=n;i<6;i++)if(d[i])return;
   for(int j=1;j<=B;j++){Index l=d;for(int i=0;i<n;i++)l[i]*=j;subs[j].push_back(l);}
  });
 }
 i128 at(Index l,int b) const {
  // l shifted by (n-1,..0)
  int inv=false;
  for(int i=1;i<n;i++){
   int x=l[i], j=i;
   while(j>0&&x>l[j-1]){l[j]=l[j-1];inv=!inv;j--;}
   if(j&&x==l[j-1])return 0;
   l[j]=x;
  }
  auto t=tab[b][rankn(l,b*6)];
  return inv?-t:t;
 }
 static void sub_shift(Index& l){ for(int i=0;i<n;i++)l[i]+=n-1-i; }
 void next(int b) {
  int N=rank_tab[n][6*b][M-1];
  ps.clear();ps.reserve(N);
  Index zero{};part_impl(6*b,zero,n-1,[&](Index l){sub_shift(l);ps.push_back(l);});
  tab.emplace_back(ps.size());if(ps.size()!=N)abort();
  auto& q=tab.back();
  #pragma omp parallel for schedule(dynamic,200)
  for(int k=0;k<N;k++){
   Index p=ps[k];i128 c=0;bool over=false;
   for(int i=1;i<=b;i++)for(auto& l:subs[i]){
    Index t{};
    for(int j=0;j<n;j++){t[j]=p[j]-l[j];if(t[j]<0) goto nope;}
    over|=__builtin_add_overflow(at(t,b-i),c,&c);
    nope:;
   }
   if(over){cerr<<"overflow at b="<<b;abort();}
   if(c<0||c%b){cerr<<"bad q";abort();}
   q[k]=c/b;
  }
 }
};

template<int n>
struct TailRank {
 int T,w;
 vector<int> off;
 vector<Index> ts;
 static int ntails(int W){
  int n0=6-n,q=1;
  for(int i=0;i<n0;i++)q*=W+1;
  return q;
 }
 int tindex(const Index& l) const{
  int i=0;
  for(int j=n;j<6;j++)i=i*(T+1)+l[j];
  return i;
 }
 int index(const Index& l) const{
  int k=tindex(l);
  int f=l[n],z=w;
  for(int j=n;j<6;j++)z-=l[j];
  z-=f*n;
  int idx=off[k], prev=0;
  for(int j=n-1;j>=1;j--){
   int p=l[j]-f;
   auto t=rank_tab[j+1][z];idx+=t[p]-t[prev];
   z-=p;prev=p;
  }
  return idx;
 }
 const int size() const {return off.back();}
 TailRank(int w0,int t0):w(w0),T(t0) {
  off.resize(ntails(T)+1,-1);int idx=0;Index p{};
  auto rec=[&](auto rec,int j,int z)->void{
   if(j>=n){
    int f=j==5?0:p[j+1];
    for(int k=f;k*(j+1-n)<=T-z && k*(j+1)<=w-z;k++){p[j]=k;rec(rec,j-1,z+k);}
   } else {
    int k=tindex(p);off[k]=idx;ts.push_back(p);
    idx+=rank_tab[n][w-z-n*p[n]][M-1];
   }
  };
  rec(rec,5,0);
  off.back()=idx;
 }
 vector<Index> parts(){
   vector<Index> out;out.reserve(size());
   for(Index p:ts){
    int z=w;for(int j=n;j<6;j++)z-=p[j];
    part_impl(z,p,n-1,[&](Index l){out.push_back(l);});
   }
   if(out.size()!=size()){cerr<<"size bug\n";abort();}
   return out;
 }
};

template<int n>
struct QTail {
 int T;vector<TailRank<n>> ranks;
 vector<vector<i128>> tab;
 QTail(int maxb,int T):T(T) {
  ranks.reserve(maxb+1);
  for(int b=0;b<=maxb;b++)ranks.emplace_back(b*6,T);
 }
 int B() const {return ranks.size()-1;}
 i128 get(Index l, int b) const{ // nonnegative shifted vector, not necessarily strict/sorted
  int s=straight(l);if(!s)return 0;
  for(int i=0;i<6;i++)l[i]-=5-i;
  return s*tab[b][ranks[b].index(l)];
 }

 void next(int b){
  auto& rank=ranks[b];auto ps=rank.parts();
  tab.emplace_back(ps.size());auto& q=tab.back();

  #pragma omp parallel for schedule(dynamic,100)
  for(int k=0;k<ps.size();k++){
   Index p=shift(ps[k]);i128 c=0;bool over=false;
   for(int i=1;i<=b;i++){
    auto rec=[&](auto rec,Index& t,int j,int z)->void{
      if(z==0){over|=__builtin_add_overflow(get(t,b-i),c,&c);}
      else if(j==0){
       t[0]-=z;
       if(t[0]>=0)over|=__builtin_add_overflow(get(t,b-i),c,&c);
       t[0]+=z;
      } else {
       int q=t[j],v=max(q-z,0);
       for(;t[j]>=v;t[j]-=i)rec(rec,t,j-1,z+t[j]-q);
       t[j]=q;
      }
    };
    rec(rec,p,5,6*i);
   }
   if(over){cerr<<"overflow "<<b<<endl;abort();}
   if(c<0||c%b){cerr<<"bad qtail";abort();}
   q[k]=c/b;
  }
 }
 i128 coeff(Index l, int b){
  int t=0;for(int j=n;j<6;j++)t+=l[j];
  if(t>T || b>B())return 0;
  return tab[b][ranks[b].index(l)];
 }
};

template<class F>
void strip(Index l, int n, int i, int b, F f) {
 // iterate contribution to p_i[h_b]*something(length<=n-i), λ=l length<=n, prior weight (n-i)b.
 int last[6],idx[6],width[6], m=0;
 Index p=l,mu{};
 for(int j=0;j<n;j++)p[j]+=n-1-j;
 for(int j=0;j<i;j++)last[j]=-1;
 int rem=b, sum=0;
 for(int j=n-1;j>=0;j--){
  int r=p[j]%i,k=last[r];
  if(k==-1){
   mu[j]=r;rem-=(p[j]-r)/i;
  }else{
   idx[m]=j;width[m]=(p[j]-p[k])/i-1;
   sum+=width[m];++m;
  }
  last[r]=j;
 }
 if(m!=n-i || rem<0 || sum<rem)return; // m mismatch => some residues not present

 auto call=[&](){
  Index s=mu;
  int sign=1;
  for(int j=1;j<n;j++){
   int x=s[j],k=j;
   while(k&&x>s[k-1]){s[k]=s[k-1];k--;sign=-sign;}
   s[k]=x;
  }
  for(int j=0;j<n;j++)s[j]-=n-1-j;
  f(s,sign);
 };
 auto rec=[&](auto rec,int k,int w,int max)->void{
  if(k==m){call();return;}
  int j=idx[k];max-=width[k];
  for(int x=std::max(0,w-max);x<=w&&x<=width[k];x++){
   mu[j]=p[j]-i*x;
   rec(rec,k+1,w-x,max);
  }
 };
 rec(rec,0,rem,sum);
}

struct Source {
 int b;vector<vector<i128>> data{vector<i128>{1}};
 Source(int b):b(b){}
 i128 next(Index l,int j) const{
   i128 c=0;
   for(int i=1;i<=j;i++) strip(l,j,i,b,[&](Index mu,int s){
    c+=s*data[j-i][rankp(mu,(j-i)*b)];
   });
   if(c<0||c%j){cerr<<"bad source";abort();}
   return c/j;
 }
 void grow(int j){
  auto w=j*b,N=int(rank_tab[j][w][M-1]);
  vector<Index> ps;ps.reserve(N);Index p{};
  part_impl(w,p,j-1,[&](Index l){ps.push_back(l);});
  data.emplace_back(ps.size());auto& q=data.back();
  #pragma omp parallel for schedule(dynamic,50)
  for(int k=0;k<N;k++)q[k]=next(ps[k],j);
 }
};


i128 binom(int n,int k){
 i128 c=1; k=min(k,n-k);
 for(int i=1;i<=k;i++) c=c*(n-i+1)/i;
 return c;
}
constexpr i128 INF=i128(1)<<100;
i128 kbound(i128 p,int b,int k) {
 if(p==0)return 0;
 p=min(p,INF);
 int z=0;
 while(binom(b+z,z)<p) ++z;
 if(z>18)z=18; // avoid overflow choose(167,18)~1e23; INF checks
 auto c=binom(k+z,z), h=binom(k+z-1,z);
 if (p-1-z>INF/h)return INF;
 return min(INF,c+(p-1-z)*h);
}
int deg(const Index& r) {
 int w=0;
 for(int j=0;j<D;j++)w+=(j+1)*r[j];
 return w;
}
Index add(const Index& a, const Index& b) {
 auto c=a;
 for(int j=0;j<D;j++)c[j]+=b[j];
 return c;
}
Index mul(Index a,int k){
 for(auto& x:a)x*=k;
 return a;
}
int tail(const Index& d,int n=2) {
 int t=0;
 for(int j=n;j<D;j++) t+=(j+1-n)*d[j];
 return t;
}
Index part(Index d){
 for(int j=D-2;j>=0;j--)d[j]+=d[j+1];
 return d;
}
vector<vector<i128>> data_;
int const cap=25,maxb=149;
i128 coeff(const Index& d){
 int w=deg(d);
 assert(w%6==0);
 if(w>cap*6)return 0;
 return data_[w/K][rankp(part(d),w)];
}
template<class F>
void residues(Index r, int j, F f){
 for(int x=0;x<6;x++){
  r[j]=x;
  if(j==0) {
   if(deg(r)%6==0) f(r);
  } else residues(r,j-1,f);
 }
}

struct cert { Index l; i128 val; };

Index diff(Index a, const Index& b){for(int i=0;i<D;i++)a[i]-=b[i];return a;}

struct Grid {
 int limit;
 vector<Index> points,prev;
 vector<i64> tot;
 Grid(int lim):limit(lim),tot(lim+2) {
  for(int w=0;w<=limit;w++){
   tot[w+1]=tot[w]+rank_tab[5][w][M-1];
  }
  points.reserve(tot.back());
  prev.reserve(tot.back());
  for(int w=0;w<=limit;w++){
   Index d{},p{};
   part_impl(w,p,4,[&](Index l){
    d[4]=l[4];
    for(int i=0;i<4;i++)d[i]=l[i]-l[i+1];
    points.push_back(d);
    for(int i=0;i<=4;i++) {
     --d[i];
     l[i]=index(d);
     ++d[i];
    }
    prev.push_back(l);
   });
   if(points.size()!=tot[w+1])abort();
  }
 }
 int index(const Index& d) const {
  for(int v:d)if(v<0)return -1;
  if(d[5])return -1;
  int w=deg(d); if(w>limit)return -1;
  return tot[w]+rankp(part(d),w);
 }
 size_t size(int max=-1) const {return max<0?points.size():tot[min(limit,max)+1];}
};
Grid *g;

struct Mono {
 int n;
 vector<i128> q;
 template<class F> void exact(int max,F f){
   n=g->size(max);q.resize(n);
   for(int i=0;i<n;i++)q[i]=f(g->points[i]);
 }
 void propagate(){
   for(int i=0;i<n;i++){
    for(int j=0;j<5;j++){
      int p=g->prev[i][j];if(p<0)continue;
      q[i]=max(q[i],q[p]);
    }
   }
 }
 void extend(int max) {n=g->size(max);q.resize(n);propagate();}
 i128 at(const Index& d) const {int i=g->index(d);return i>=0&&i<n?q[i]:0;}
};
Mono powerAll;
vector<vector<int>> masksList;
vector<int> maskCounts;
void init_masks(){
 for(int k=1;k<=6;k++){
  vector<int> p(k);
  auto rec=[&](auto rec,int pos,int left,int lo)->void{
   if(pos==k){
    if(left)return;
    i64 c=720;vector<int> t(7);
    for(int i:p)c=c/(++t[i]*i);
    vector<int> masks;
    do{
      int s=6,m=0;
      for(int i:p) {
       s-=i;
       if(s>=2)m|=1<<(s-2);
      }
      if(find(masks.begin(),masks.end(),m)==masks.end())masks.push_back(m);
    } while(next_permutation(p.begin(),p.end()));
    masksList.push_back(masks);
    maskCounts.push_back(c);
    return;
   }
   for(int i=lo;i<=left;i++){p[pos]=i;rec(rec,pos+1,left-i,i);}
  };
  rec(rec,0,6,1);
 }
 if(accumulate(maskCounts.begin(),maskCounts.end(),0)!=720){cerr<<"counts fail: ";for(auto v:maskCounts)cerr<<v<<",";cerr<<endl;abort();}
}
i128 ub_cycle(const Index& d){
 i128 q[16];
 q[0]=1;
 for(int i=0;i<4;i++){
  int s=i+2;int w[5],best=0;
  for(int j=0;j<s;j++){
   w[j]=1;
   for(int k=j;k<j+6-s;k++)w[j]+=d[k];
   if(w[j]>w[best])best=j;
  }
  i128 f=1;
  for(int j=0;j<s;j++)if(j!=best)f*=w[j];
  for(int m=0;m<1<<i;m++)q[m+(1<<i)]=q[m]*f;
 }
 i128 u=0;
 for(int j=0;j<masksList.size();j++){
  i128 t=INF;
  for(int m:masksList[j])t=min(t,q[m]);
  u+=i128(maskCounts[j])*t;
 }
 return u/720;
}
void feed_power(Index x,i128 p){
 // x[5]==0 required; other shifts via residues separately
 if(p<=1||x[5])return;
 int b=deg(x)/6;
 for(int k=1;k*b<=maxb;k++){
  auto d=mul(x,k);
  bool ok=true;
  for(int i=0;i<5;i++){
   if(d[i]%6){ok=false;break;}
   d[i]/=6;
  }
  if(!ok)continue;
  int w=g->index(d);
  powerAll.q[w]=max(powerAll.q[w],kbound(p,b,k));
 }
}
vector<Index> rs;
const int ulim=42;
Mono uniBase;
vector<cert> uOcc;
void init_common(){
 g=new Grid(maxb);
 residues(Index{},D-1,[&](Index r){rs.push_back(r);});
 if(rs.size()!=7776)abort();
 powerAll.exact(maxb,[](Index x){return i128(1);});
 uniBase.exact(ulim,[](Index x){return INF;});
 Mono specific;
 for(Index r:rs){
  int b0=deg(r)/6;
  specific.exact(cap-b0,[&](Index m){
   return coeff(add(r,mul(m,6)));
  });
  if(r[5]==0)for(int i=0;i<specific.n;i++) feed_power(add(r,mul(g->points[i],6)),specific.q[i]);
  specific.extend(ulim);
  for(int i=0;i<specific.n;i++)uniBase.q[i]=min(uniBase.q[i],specific.q[i]);
 }
 // minimal common occurrences
 for(int i=0;i<uniBase.n;i++){
  if(!uniBase.q[i])continue;
  bool minimal=true;
  for(int j=0;j<5;j++){
   int p=g->prev[i][j];
   if(p>=0&&uniBase.q[p])minimal=false;
  }
  if(minimal)uOcc.push_back(cert{g->points[i],uniBase.q[i]});
 }
 cerr<<uOcc.size()<<" minimal common occurrences with all r from deg<= "<<ulim<<endl;
 uniBase.extend(maxb);
 powerAll.propagate();
}
vector<vector<i128>> qextra[6];
int xcap[6]={0,0,0,149,55,25};
template<int n> void gen_extra(){
 Make<n> make(xcap[n]);
 for(int b=1;b<=xcap[n];b++)make.next(b);
 qextra[n]=move(make.tab);
}
void feed_extra(int n){
 for(int b=cap+1;b<=xcap[n];b++){
  Index d{},p{};int i=0;
  part_impl(b*6,p,n-1,[&](Index l){
   auto val=qextra[n][b][i++];
   if(n>3&&l[n-1]==0)return;
   d[n-1]=l[n-1];
   for(int j=0;j<n-1;j++)d[j]=l[j]-l[j+1];
   if(val>INF)val=INF;
   feed_power(d,val);
  });
 }
 powerAll.propagate();
}
i128 explicit_coeff(Index d){
 int w=deg(d),b=w/6,n=6;
 if(b<=cap)return coeff(d);
 while(n>=4&&!d[n-1])n--;
 if(n>=5 || b>xcap[n] || w!=6*b)return 0;
 return qextra[n][b][rankp(part(d),w)];
}

Index high{5,5,5,5,5,5};
// singleton common lower test
bool passed(Index m, Index dhi){
 i128 u=ub_cycle(dhi),v=uniBase.at(m);
 if(v>=u)return true;
 for(auto z:uOcc){
   auto p=diff(m,z.l);
   v=max(v,powerAll.at(p));
 }
 return v>=u;
}

unique_ptr<QTail<3>> qt;
i64 fails_by[25]{}, maxby[25]{};
vector<int> todos;
vector<int> down, prevIndex, where;
vector<Index> downprev;
void setup(){
 where.resize(g->size(),-1);
 vector<int> todo1;
 for(int i=0;i<g->size();i++){
  auto m=g->points[i];
  auto d=mul(m,6), dhi=add(d,high);
  int b=deg(m);
  if(b+17<=cap || passed(m,dhi))continue;
  where[i]=0;todo1.push_back(i);
 }
 for(int i=g->size()-1;i>=0;i--){
  if(where[i]==-1)continue;
  for(int j=0;j<5;j++){
   int p=g->prev[i][j];if(p>=0)where[p]=0;
  }
 }
 for(int i=0;i<g->size();i++){
  if(where[i]==-1)continue;
  Index p=g->prev[i];
  for(int j=0;j<5;j++)if(p[j]>=0)p[j]=where[p[j]];
  where[i]=down.size();
  downprev.push_back(p);
  down.push_back(i);
 }
 for(int p:todo1)todos.push_back(where[p]);
 cerr<<"todos "<<todos.size()<<", down "<<down.size()<<endl;
}


vector<vector<Index>> occvec;

void init_occ(){
 occvec.resize(rs.size());
 for(int i=0;i<rs.size();i++){
  auto r=rs[i];Mono spec;
  spec.exact(cap-deg(r)/6,[&](Index m){return coeff(add(r,mul(m,6)));});
  for(int z=0;z<spec.n;z++){
   if(!spec.q[z])continue;
   bool minimal=true;
   for(int j=0;j<5;j++){
    int v=g->prev[z][j];if(v>=0&&spec.q[v])minimal=false;
   }
   if(minimal)occvec[i].push_back(g->points[z]);
  }
 }
 int m=0;for(auto& c:occvec)m=max(m,int(c.size()));
 cerr<<"max occvec "<<m<<endl;
}

struct TestSpec {
 Index r;
 vector<i128> spec;
 vector<Index> occ;
 TestSpec(int i):r(rs[i]),occ(occvec[i]) {
  spec.reserve(down.size());
  for(int k=0;k<down.size();k++){
    auto& m=g->points[down[k]];
    auto d=add(r,mul(m,6));
    i128 q=max(explicit_coeff(d),qt->coeff(part(d),deg(d)/6));
    for(int j=0;j<5;j++){
      int p=downprev[k][j];if(p>=0)q=max(q,spec[p]);
    }
    spec.push_back(q);
  }
 }
 bool pass(const Index& m,const Index& d,i128 q) const {
  auto u=ub_cycle(d);
  if(q>=u)return true;
  // direct chart: non-first tail <=b suffices
  if(tail(d,1)<=deg(d)/6)return true;
  for(auto& c:occ)if(powerAll.at(diff(m,c))>=u)return true;
  return false;
 }
 void run() const{
  for(int k:todos){
   auto& m=g->points[down[k]];
   auto d=add(r,mul(m,6));
   int b=deg(d)/6;
   if(b<=cap||b>maxb)continue;
   if(pass(m,d,spec[k]))continue;

   #pragma omp critical
   {
    ++fails_by[b/6];maxby[b/6]=max(maxby[b/6],i64(tail(d)));
   }
  }
 }
};
void classify(){
 init_common();
 gen_extra<3>(); gen_extra<4>(); feed_extra(3);feed_extra(4);
 setup();init_occ();
 qt=make_unique<QTail<3>>(45,18);qt->tab={{1}};
 for(int b=1;b<=45;b++)qt->next(b);
 #pragma omp parallel for schedule(dynamic,4)
 for(int i=0;i<rs.size();i++){TestSpec t(i);t.run();}
 for(int i=cap/6;i<25;i++){
  cout<<6*i<<" flags "<<fails_by[i]<<" max "<<maxby[i]<<endl;
  if(maxby[i]>27)abort();
 }
}

i64 checked=0, mistakes=0;
void run(int b){
 Source s(b);for(int j=1;j<=5;j++)s.grow(j);
 i64 c=0,eq=0;
 vector<Index> todo;
 parts(6*b,[&](Index l){
  Index d=l;for(int j=0;j<5;j++)d[j]-=l[j+1];
  if(coeff(d)<ub_cycle(d))todo.push_back(l);
 });
 #pragma omp parallel for schedule(dynamic,25) reduction(+:c,eq)
 for(int k=0;k<todo.size();k++){
  Index l=todo[k],d=l;for(int j=0;j<5;j++)d[j]-=l[j+1];
  auto p=s.next(l,6), q=coeff(d);
  if(p>q){
   c++;
   #pragma omp critical
   if(mistakes++<10){cerr<<"Violation b="<<b<<" l=";for(int v:l)cerr<<v<<",";cerr<<" f="<<p<<" q="<<q<<endl;}
  }
  if(p==q)eq++;
 }
 checked+=todo.size();
 cout<<b<<" total(exact) "<<todo.size()<<" failed "<<c<<" equality "<<eq<<endl;
}

int main(){
 init();init_masks();data_=gen(cap);
 for(int b=6;b<=cap;b++)run(b);
 if(mistakes)return 1;
 classify();
}
