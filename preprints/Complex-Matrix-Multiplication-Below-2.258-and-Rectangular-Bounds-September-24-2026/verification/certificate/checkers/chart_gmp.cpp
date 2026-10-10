#include <gmpxx.h>
#include <cassert>
#include <chrono>
#include <fstream>
#include <iostream>
#include <vector>
// A literal reimplementation of pgen.chart with Python floor division.
int main(int argc,char**argv){
 assert(argc==4); int N=std::stoi(argv[1]), bits=std::stoi(argv[2]);
 int L=N+1; size_t nn=(size_t)L*L;
 std::vector<mpz_class> P(nn),D(nn),M(nn),XX(nn),YY(nn);
 mpz_class Q=mpz_class(1)<<bits,n,w,p,h;
 const int Z[]={18623,-2696,-2677,194,393,17,1,8};
 auto id=[L](int i,int j)->size_t{return (size_t)i*L+j;};
 auto started=std::chrono::steady_clock::now();
 for(int k=0;k<=N;k++){
  for(int i=0;i<=k/2;i++){
   int j=k-i;
   if(i==0){n=Q*(k<8?Z[k]:0);w=100000;}
   else {
    n=0; w=D[0]*i*j;
    for(int x=0;x<i;x++)for(int y=(x==0);y<j;y++){
     int hh=(1+y-x)%3;if(hh<0)hh+=3;
     int a=i-x-1+hh,b=j-y+1-hh;
     const auto &v=hh==0?YY[id(a,b)]:hh==1?M[id(a,b)]:XX[id(a,b)];
     mpz_submul(n.get_mpz_t(),D[id(x,y)].get_mpz_t(),v.get_mpz_t());
    }
   }
   mpz_fdiv_q_2exp(h.get_mpz_t(),w.get_mpz_t(),1);n+=h;
   mpz_fdiv_q(p.get_mpz_t(),n.get_mpz_t(),w.get_mpz_t());
   P[id(i,j)]=P[id(j,i)]=p;
   D[id(i,j)]=D[id(j,i)]=72*p+Q*(k==0?8:k==1?2:k==2?-1-i:0);
   M[id(i,j)]=M[id(j,i)]=p*i*j;
   XX[id(i,j)]=YY[id(j,i)]=p*i*(i-1);
   YY[id(i,j)]=XX[id(j,i)]=p*j*(j-1);
  }
  if(k%50==0)std::cerr<<"degree "<<k<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count()<<std::endl;
 }
 std::ofstream out(argv[3]);
 for(int k=0;k<=N;k++)for(int i=0;i<=k;i++)out<<P[id(k-i,i)]<<'\n';
}
