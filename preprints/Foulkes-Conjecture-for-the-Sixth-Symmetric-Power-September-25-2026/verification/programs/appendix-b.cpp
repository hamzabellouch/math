#include <boost/multiprecision/cpp_int.hpp>
#include <stdexcept>
#include <functional>
#include <cstdint>
#include <iostream>
#include <algorithm>
#include <array>
#include <vector>
#include <cassert>
using namespace std;
using Int=__int128_t;
using Big=boost::multiprecision::cpp_int;
using A=array<int,4>;
const int T=27,O=168,L=330,NB=447+O+1;
using P=array<Int,L>; // q exponents -168..161
vector<A> parts;
int index_[28][28][28][28];
int idx(A p,int sign=0){
 sort(p.begin(),p.end(),greater<int>());
 if(p.back()<0)return -1;
 return index_[p[0]][p[1]][p[2]][p[3]];
}
int wt(A p){return p[0]+p[1]+p[2]+p[3];}
A sub(A p,A a,int k=1){for(int i=0;i<4;i++)p[i]-=k*a[i];return p;}

template<class F> void arrays(int t,bool ordered,F f){
 A p{};
 auto rec=[&](auto rec,int i,int left,int bound)->void{
  if(i==4){if(!left)f(p);return;}
  for(int x=0;x<=left&&x<=bound;x++){
    p[i]=x;rec(rec,i+1,left-x,ordered?x:t);
  }
 };
 rec(rec,0,t,t);
}
vector<P> num[7];
void add(P& to,const P& from,int mul,int shift){
 for(int i=max(0,-shift);i<min(L,L-shift);i++)to[i+shift]+=mul*from[i];
}
void target(){
 for(int j=0;j<=6;j++){
  vector<P> H(parts.size());H[0][O]=1;
  for(int k=1;k<parts.size();k++){
   auto p=parts[k];int t=wt(p);
   for(int h=1;h<=6&&h<=t;h++)arrays(h,false,[&](A a){
    for(int i=1;i*h<=t;i++){
     int z=idx(sub(p,a,i)); if(z<0)break;
     for(int u=0;u<=6-h;u++)add(H[k],H[z],h,i*(u-j));
    }
   });
   for(auto& v:H[k]){assert(v%t==0);v/=t;}
  }
  for(int mask=0;mask<64;mask++)if(__builtin_popcount((unsigned)mask)==j){
    int e=0;for(int i=0;i<6;i++)if(mask>>i&1)e+=i+1;
    for(int k=0;k<parts.size();k++)add(num[j][k],H[k],j%2?-720:720,e);
  }
 }
}
void source(const vector<int>& lens,int cnt){
 int D[22]={1};
 for(int i=1;i<=6;i++)for(int n=21;n>=i;n--)D[n]-=D[n-i];
 for(int i:lens)for(int n=i;n<=21;n++)D[n]+=D[n-i];
 for(int mask=0;mask<1<<lens.size();mask++){
  int ways[2][T+1]{};ways[0][0]=ways[1][0]=1;
  int j=0,c=cnt;
  for(int k=0;k<(int)lens.size();k++){
   int i=lens[k],z=mask>>k&1;
   if(z)j+=i,c=-c;
   for(int n=i;n<=T;n++)ways[z][n]+=ways[z][n-i];
  }
  for(int k=0;k<(int)parts.size();k++){
   array<Int,T+1> pol{};pol[0]=1;int deg=0;
   for(int m:parts[k]){
    array<Int,T+1> t{};
    for(int n=0;n<=deg;n++)for(int i=0;i<=m;i++)
     t[n+i]+=pol[n]*ways[1][i]*ways[0][m-i];
    pol=t;deg+=m;
   }
   for(int i=0;i<=deg;i++)for(int e=0;e<=15;e++)
    num[j][k][O+j+e-i]-=c*pol[i]*D[e];
  }
 }
}
void gen_source(vector<int>& lens,int rem,int low,int cnt){
 if(!rem){source(lens,cnt);return;}
 for(int h=low;h<=rem;h++){
  int m=count(lens.begin(),lens.end(),h)+1;
  lens.push_back(h);gen_source(lens,rem-h,h,cnt/(h*m));lens.pop_back();
 }
}
const int pascal[5][5]={{1},{1,1},{1,2,1},{1,3,3,1},{1,4,6,4,1}};
void cross(){
 for(int k=(int)parts.size()-1;k>=0;k--){
  A p=parts[k];
  for(int mask=1;mask<81;mask++){
    int t=mask,n1=0,n2=0;A h{};
    for(int& v:h){v=t%3;t/=3;n1+=v==1;n2+=v==2;}
    int i=idx(sub(p,h));if(i<0)continue;
    for(int j=0;j<=6;j++)for(int s=0;s<=n1;s++)add(num[j][k],num[j][i],(n1%2?-1:1)*pascal[n1][s],-n2-s);
  }
  for(int j=0;j<=6;j++)for(int s=L-1;s>0;s--)num[j][k][s]-=num[j][k][s-1];
 }
}
using Row=array<Big,NB>;
Row schur_row(const vector<P>& n,A eta){
 A delta{3,2,1,0}, p;for(int i=0;i<4;i++)p[i]=eta[i]+delta[i];
 P r{};
 do{
  int i=idx(sub(p,delta));if(i<0)continue;
  int c=1;
  for(int v=0;v<4;v++)for(int w=0;w<v;w++)if(delta[w]<delta[v])c=-c;
  add(r,n[i],c,0);
 }while(prev_permutation(delta.begin(),delta.end()));
 Row t{};for(int i=0;i<L;i++)t[i]=r[i];
 for(int h=1;h<=6;h++)for(int i=h;i<NB;i++)t[i]+=t[i-h];
 return t;
}
int total[25]{},eq_[25]{};
void run_thin(){
 parts.clear(); // run once
 for(int t=0;t<=T;t++)arrays(t,true,[&](A p){index_[p[0]][p[1]][p[2]][p[3]]=parts.size();parts.push_back(p);});
 for(auto& v:num)v.resize(parts.size());
 target();vector<int> lens;gen_source(lens,6,1,720);cross();
 for(auto p:parts){
  array<Row,7> rows;for(int j=0;j<=6;j++)rows[j]=schur_row(num[j],p);
  for(int b=26;b<=149;b++)for(int B=p[0];2*B<=6*b-wt(p);B++){
   Big c=0;
   for(int j=0;j<=6;j++){int i=O+B-j*b;if(i>=0)c+=rows[j][i];}
   if(c<0||c%720!=0)throw std::runtime_error("thin");
   eq_[b/6]+= c==0; total[b/6]++;
  }
 }
 for(int b=4;b<25;b++)cout<<6*b<<" "<<total[b]<<" "<<eq_[b]<<endl;
}
int main(){run_thin();}
