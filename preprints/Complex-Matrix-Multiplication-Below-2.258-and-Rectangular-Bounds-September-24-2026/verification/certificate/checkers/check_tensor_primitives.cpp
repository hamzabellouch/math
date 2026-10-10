#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <map>
#include <vector>
using namespace std;
int main() {
  long long complete_words=0, parity_words=0, group_pairs=0;
  for(int L=2;L<=8;++L) {
    int total=1; for(int t=0;t<L;++t) total*=3;
    array<long long,3> actual={0,0,0};
    long long a=1,b=1,c=1;
    for(int t=0;t<L;++t){ long long e0=t+1,e1=2*t+3,e2=3*t+2;a*=e0;b*=e0+e1;c*=e0+e2;}
    for(int code=0;code<total;++code){
      int k=code; array<int,3> n={0,0,0}; long long weight=1;
      for(int t=0;t<L;++t){int i=k%3;k/=3;++n[i];weight*=i==0?t+1:i==1?2*t+3:3*t+2;}
      array<int,3> f={n[0]==L,n[1]>0,n[2]>0};
      int s=f[0]+f[1]+f[2];assert(s>=1);
      bool intended=n[1]==0||n[2]==0;assert((s==1)==intended);
      if(intended){int i=f[0]?0:f[1]?1:2;actual[i]+=weight;}
      ++complete_words;
    }
    assert(actual[0]==a&&actual[1]==b-a&&actual[2]==c-a);
  }
  int M[3][3]={};
  for(int code=0;code<27;++code){int k=code;array<int,3> n={0,0,0};for(int t=0;t<3;++t){++n[k%3];k/=3;}
    int s=(n[0]%2)+(n[1]%2)+(n[2]%2);assert(s==1||s==3);
    assert((s==1)!=(n[0]==1&&n[1]==1&&n[2]==1));
    if(s==1){int maj=-1,odd=-1;for(int i=0;i<3;++i){if(n[i]>=2)maj=i;if(n[i]%2)odd=i;}assert(maj>=0&&odd>=0);++M[maj][odd];}
    ++parity_words;
  }
  for(int i=0;i<3;++i)for(int j=0;j<3;++j)assert(M[i][j]==(i==j?1:3));
  vector<array<int,3>> K1={{{2,0,0}},{{0,2,0}},{{0,0,2}},{{0,1,1}},{{1,0,1}},{{1,1,0}}};
  for(auto d:K1){if(d==array<int,3>{1,0,1})continue;array<int,3> f={d[2]>0,d[0]>0,d[1]==2};assert(f[0]+f[1]+f[2]==1);}
  // Independently enumerate finite norm-shell/tangent-slice GROUP instances.
  for(int q=2;q<=4;++q){
    vector<array<int,3>> grid;for(int x=0;x<q;++x)for(int y=0;y<q;++y)for(int z=0;z<q;++z)grid.push_back({x,y,z});
    for(auto t:grid){int radius=0;for(int i=0;i<3;++i)radius+=t[i]*t[i];map<int,vector<array<int,3>>> slices;
      for(auto u:grid){int dot=0;for(int i=0;i<3;++i)dot+=t[i]*u[i];slices[dot].push_back(u);}
      for(auto const &entry:slices)for(auto u:entry.second)for(auto v:entry.second){
        array<int,3> z;bool inside=true;int znorm=0;
        for(int i=0;i<3;++i){z[i]=(t[i]+u[i]-v[i]+4*q)%(4*q);inside=inside&&z[i]<q;znorm+=z[i]*z[i];}
        if(inside&&znorm==radius)assert(u==v&&z==t);
        ++group_pairs;
      }
    }
  }
  cout<<"PASS: COMPLETE "<<complete_words<<" words; PARITY "<<parity_words<<" words; K1 edge 5 atoms; GROUP "<<group_pairs<<" tangent pairs.\n";
}
