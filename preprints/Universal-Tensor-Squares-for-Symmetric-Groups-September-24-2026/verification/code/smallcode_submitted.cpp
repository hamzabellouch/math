#include <algorithm>
#include <vector>
#include <cmath>
#include <cstdint>
#include <cstdlib>
using namespace std;
using U=uint64_t;
using D=unsigned __int128;
using V=vector<int>;
D one(int i){return D(1)<<i;}
vector<D> masks[65];
V idxs[65],dimv[65];
int n,p,invv[65],fac[65];

void diagrams(int s,int left,int cap,int pos,D B){
 if(!left){masks[s].push_back(B);return;}
 for(int j=min(left,cap);j>0;--j)
    diagrams(s,left-j,j,pos-1,B^one(pos)^one(pos+j));
}
U mixit(U z){
 z=(z^(z>>30))*0xbf58476d1ce4e5b9ULL;
 z=(z^(z>>27))*0x94d049bb133111ebULL;
 return z^(z>>31);
}
int slot(int s,D b){
 int mask=int(idxs[s].size()-1),i=(mixit(U(b))+7*mixit(U(b>>64)))&mask;
 while(idxs[s][i]!=-1&&masks[s][idxs[s][i]]!=b)i=(i+1)&mask;
 return i;
}
int lowest(D b){
 if(U(b))return __builtin_ctzll(U(b));
 return 64+__builtin_ctzll(U(b>>64));
}
int cnt(D b){return __builtin_popcountll(U(b))+__builtin_popcountll(U(b>>64));}
int addm(int a,int b){int c=a+b;return c>=p?c-p:c;}
int mul(int a,int b){return (int)((long long)a*b%p);}
int inverse(int a){
 int z=1;
 for(int e=p-2;e;e/=2,a=mul(a,a))if(e%2)z=mul(z,a);
 return z;
}
// forward from s to s+k, or its transpose
V op(int s,int k,bool up,const V& v){
 V z(masks[up?s+k:s].size(),0);
 for(int i=0;i<(int)masks[s].size();i++){
   if(up&&!v[i])continue;
   D b=masks[s][i];
   for(D a=b&((~b)>>k);a;a&=a-1){
     int x=lowest(a);
     D m=one(x),t=one(x+k);
     int j=idxs[s+k][slot(s+k,b^m^t)];
     int value=v[up?i:j];
     if(cnt((t-m-m)&b)%2)value=value?p-value:0;
     int& w=z[up?j:i];w=addm(w,value);
   }
 }
 return z;
}
V calc(int s,int k,int e,const V &v){
 // e already picked of size k; subsequent weights relative to them
 if(s==0)return V{mul(v[0],v[0])};
 if(k>s)return calc(s,s,0,v);
 if(k==1){
   V a(dimv[s]);int c=0;
   for(int i=0;i<(int)a.size();i++)c=addm(c,mul(a[i],v[i]));
   c=mul(mul(c,c),fac[s]);
   for(int &x:a)x=mul(x,c);
   return a;
 }
 V a=calc(s,k-1,0,v),b=op(s-k,k,false,v);
 bool nz=false;for(int x:b)if(x){nz=true;break;}
 if(nz){
   b=op(s-k,k,true,calc(s-k,k,e+1,b));
   int c=mul(invv[k],invv[e+1]);
   for(int i=0;i<(int)a.size();i++)a[i]=addm(a[i],mul(c,b[i]));
 }
 return a;
}
bool sym(D b){
 for(int i=0;i<64;i++)if(((b>>i)^(b>>(127-i)))%2==0)return false;
 return true;
}
double score(D b){ // affects order only
 double s=0;
 for(int k=1;k<=n;k++)s+=log(double(k))*cnt(b&((~b)<<k));
 return s;
}
int main(int argc,char**argv){
 n=atoi(argv[1]);
 if(n==2||n==4||n==9)return 0;
 if(n<1||n>64)abort();
 for(int s=0;s<=n;s++){
   diagrams(s,s,s,63,one(64)-1);
   int m=1;while(m<2*(int)masks[s].size())m*=2;
   idxs[s].assign(m,-1);
   for(int i=0;i<(int)masks[s].size();i++)
      idxs[s][slot(s,masks[s][i])]=i;
 }
 V list;for(int i=0;i<(int)masks[n].size();i++)
   if(sym(masks[n][i]))list.push_back(i);
 sort(list.begin(),list.end(),[](int i,int j){
   double x=score(masks[n][i]),y=score(masks[n][j]);return x==y?i<j:x<y;});
 for(int i:list){
   V ok(masks[n].size());
   for(int mod:{1000000007,1000000009}){
     p=mod; fac[0]=1; dimv[0]=V{1};
     for(int j=1;j<=n;j++){
       invv[j]=inverse(j);fac[j]=mul(fac[j-1],invv[j]);
       dimv[j]=op(j-1,1,true,dimv[j-1]);
     }
     V v(ok.size());v[i]=1; v=calc(n,n,0,v);
     bool done=true;
     for(int j=0;j<(int)v.size();j++){
       ok[j]|=(v[j]!=0);if(!ok[j])done=false;
     }
     if(done)return 0;
   }
 }
 abort();
}
