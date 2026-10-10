#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <vector>
using namespace std;
using LL=int64_t;
using Big=__int128_t;
const int H=72;
const LL N=1000000000000LL, SCALE=1000000000000000LL;
using Triple=array<int,3>;
vector<Triple> states;
int index_[H+1][H+1];
int pure,unif;
int indexof(Triple t){
 sort(t.rbegin(),t.rend());
 assert(accumulate(t.begin(),t.end(),0)==H);
 int k=index_[t[0]][t[1]];
 assert(k>=0 && states[k]==t);
 return k;
}
void init(){
 assert(H%3==0);
 for(auto& row:index_)for(int& z:row)z=-1;
 for(int i=0;i<=H;i++)for(int j=0;j<=i;j++){
  int k=H-i-j;
  if(k<0 || k>j)continue;
  index_[i][j]=states.size();
  states.push_back({i,j,k});
 }
 pure=indexof({H,0,0});unif=indexof({H/3,H/3,H/3});
}
using Law=vector<LL>;
Law atom(int k){Law m(states.size());m[k]=N;return m;}
void complete(Law& m){
 LL sum=accumulate(m.begin(),m.end(),LL(0));
 assert(sum>=0 && sum<=N);
 m[pure]+=N-sum;
}
struct Table{
 bool symmetric;
 LL den;
 vector<int> off,to;
 vector<LL> wt;
 // mode 0 grid-grid, 1 grid-edge, 2 edge-edge
 Table(int mode,LL A=0,LL AD=1):symmetric(mode!=1){
  LL g=gcd(A,AD);A/=g;AD/=g;
  den=(mode==0?6LL:mode==1?6*AD:18*AD*AD)*H*H;
  assert(den>0);
  int K=states.size();
  off.reserve((symmetric?K*(K+1)/2:K*K)+1);
  size_t reserve=(symmetric?K*(K+1)/2:K*K)*14LL;
  to.reserve(reserve);wt.reserve(reserve);
  for(int i=0;i<K;i++)for(int j=(symmetric?i:0);j<K;j++){
   assert(to.size()<100000000);
   off.push_back(int(to.size()));
   auto p=states[i],q=states[j];
   array<LL,3> lhs,rhs;
   for(int c=0;c<3;c++){
    lhs[c]=mode==2?(AD+A)*H-3*A*p[c]:p[c];
    rhs[c]=mode==0?3*q[c]:(AD+A)*H-3*A*q[c];
    assert(lhs[c]>=0 && rhs[c]>=0);
   }
   vector<pair<int,LL>> entries;
   array<int,3> perm={0,1,2};
   do{
    array<LL,3> raw;
    LL T=0;
    for(int c=0;c<3;c++){raw[c]=lhs[c]*rhs[perm[c]];T+=raw[c];}
    if(!T)continue;
    Triple n;
    array<LL,3> rem;
    int miss=H;
    for(int c=0;c<3;c++){
     assert(raw[c]<=INT64_MAX/H);
     LL v=H*raw[c];
     n[c]=int(v/T);rem[c]=v%T;miss-=n[c];
    }
    assert(miss>=0 && miss<=2);
    if(!miss)entries.push_back({indexof(n),T});
    else for(int c=0;c<3;c++){
     LL w=miss==1?rem[c]:T-rem[c];
     if(!w)continue;
     Triple corner=n;
     for(int h=0;h<3;h++)if((h==c)==(miss==1))corner[h]++;
     entries.push_back({indexof(corner),w});
    }
   }while(next_permutation(perm.begin(),perm.end()));
   sort(entries.begin(),entries.end());
   LL sum=0;
   for(unsigned k=0;k<entries.size();){
    unsigned h=k+1; LL w=entries[k].second;
    while(h<entries.size() && entries[h].first==entries[k].first)
     w+=entries[h++].second;
    to.push_back(entries[k].first);wt.push_back(w);sum+=w;k=h;
   }
   assert(sum==den);
  }
  assert(to.size()<100000000);
  off.push_back(int(to.size()));
  cerr<<"table "<<mode<<" entries "<<to.size()<<endl;
 }
 Law combine(const Law& x,const Law& y)const{
  int K=states.size(),pos=0;
  vector<Big> sums(K);
  for(int i=0;i<K;i++){
   int start=symmetric?i:0;
   if(x[i]==0 && (!symmetric || y[i]==0)){pos+=K-start;continue;}
   for(int j=start;j<K;j++,pos++){
    Big mass=Big(x[i])*y[j];
    if(symmetric && i!=j)mass+=Big(x[j])*y[i];
    if(!mass)continue;
    for(int z=off[pos];z<off[pos+1];z++)
     sums[to[z]]+=mass*wt[z];
   }
  }
  assert(pos+1==(int)off.size());
  Law m(K);
  for(int k=0;k<K;k++)m[k]=LL(sums[k]/(Big(N)*den));
  complete(m);return m;
 }
};
LL down(Big x,Big y){assert(x>=0 && y>0 && x/y<=N*Big(SCALE));auto z=x/y;assert(z<=INT64_MAX);return LL(z);}
LL up(Big x,Big y){return down(x+y-1,y);}
LL w_zero(int dnum){
 LL lo=SCALE,hi=SCALE,sum=SCALE;
 for(int n=1;n<=41;n++){
  lo=down(Big(lo)*dnum,200*n);
  hi=up(Big(hi)*dnum,200*n);
  sum+=(n%2? -hi:lo);
 }
 return down(Big(sum)*N,SCALE);
}
Law poisson(const Law& inc,int dnum,const Table& step){
 LL w=w_zero(dnum);
 Law mix(states.size());mix[unif]=w;
 Law part=atom(unif);
 for(int n=1;;n++){
  w=down(Big(w)*dnum,200*n);
  if(!w)break;
  part=step.combine(part,inc);
  for(unsigned k=0;k<mix.size();k++)mix[k]+=down(Big(w)*part[k],N);
 }
 complete(mix);
 // no squares
 return mix;
}
const LL AD=1000000;
LL a_upper(int dmin){
 int lo=0,hi=500000;
 while(hi-lo>1){
  int m=(lo+hi)/2;
  if(Big(m)*m*dmin>=Big(AD)*AD*200)hi=m;else lo=m;
 }
 return hi;
}
LL mu_num(const Law& m){
 LL sum=0;
 for(unsigned k=0;k<m.size();k++){
  auto [a,b,c]=states[k];
  sum+=m[k]*(H*H-3*(a*b+b*c+c*a));
 }
 return sum;
}
int run(int id){
 bool regular=id<0;
 int dmin=regular?800:800+3*id,dmax=dmin+3;
 LL A=a_upper(dmin);
 Table step(regular?2:1,A,AD);
 Law m=atom(pure);
 auto test=[&](int it){
  LL sum=mu_num(m);
  if(it%10==0)cerr<<id<<" "<<it<<" "<<count_if(m.begin(),m.end(),[](LL v){return v>0;})<<" "<<double(sum)/(N*H*H)<<endl;
  return 20*Big(sum)<Big(N)*H*H;
 };
 if(regular){
  Table prod(0);
  for(int it=1;it<=400;it++){
   Law half=step.combine(m,m);
   m=prod.combine(half,half);
   if(test(it))return it;
  }
 }else{
  for(int it=1;it<=400;it++){
   m=poisson(m,dmax,step);
   if(test(it))return it;
  }
 }
 assert(false);return 0;
}
int main(int argc,char**argv){
 assert(argc==2);
 init();
 int id=atoi(argv[1]);
 assert(id>=-1 && id<27);
 cout<<id<<" "<<run(id)<<endl;
}
