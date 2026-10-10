#pragma once
#include <boost/multiprecision/cpp_int.hpp>
#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <functional>
#include <iostream>
#include <map>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>
#include <omp.h>
using boost::multiprecision::cpp_int;
constexpr int BP=144, NN=3, M=38;
inline const cpp_int Q=cpp_int(1)<<BP;
inline cpp_int floor_div(const cpp_int& a,const cpp_int& b){
 if(b==0) throw std::runtime_error("integer division by zero");
 cpp_int q=a/b,r=a%b; if(r!=0 && ((a<0)!=(b<0))) --q; return q;
}
inline cpp_int ceil_div(const cpp_int& a,const cpp_int& b){return -floor_div(-a,b);}
inline cpp_int floor_q(const cpp_int& a){ if(a>=0)return cpp_int(a>>BP);return -cpp_int(((-a)+Q-1)>>BP); }
inline cpp_int ceil_q(const cpp_int& a){return -floor_q(-a);}
inline cpp_int minint(const cpp_int&a,const cpp_int&b){return a<b?a:b;}
inline cpp_int maxint(const cpp_int&a,const cpp_int&b){return a>b?a:b;}
inline cpp_int absint(const cpp_int&a){return a<0?-a:a;}
inline cpp_int ipow(cpp_int a,int k){cpp_int v=1;while(k){if(k&1)v*=a;k>>=1;if(k)a*=a;}return v;}
struct IV {
 cpp_int u,v;
 IV():u(0),v(0){}
 IV(int n):u(cpp_int(n)*Q),v(u){}
 IV(long long n):u(cpp_int(n)*Q),v(u){}
 IV(const cpp_int& n):u(n*Q),v(u){}
 IV(cpp_int lo,cpp_int hi):u(std::move(lo)),v(std::move(hi)){if(u>v)throw std::runtime_error("reversed interval");}
 bool iszero()const{return u==0&&v==0;}
 IV operator-()const{return IV(-v,-u);}
 IV inv()const{
  if(u<=0&&v>=0)throw std::runtime_error("interval div0");
  if(v<0)return -((-*this).inv());
  return IV(floor_div(Q*Q,v),ceil_div(Q*Q,u));
 }
 IV abs()const{if(u>=0)return *this;if(v<=0)return -*this;return IV(0,maxint(-u,v));}
 IV sqrt()const{if(u<=0)throw std::runtime_error("nonpositive sqrt");return IV(boost::multiprecision::sqrt(cpp_int(u*Q)),boost::multiprecision::sqrt(cpp_int(v*Q))+1);}
 IV log()const;
 IV mid()const{return IV(floor_div(u+v,2),ceil_div(u+v,2));}
 IV hull(const IV&b)const{return IV(minint(u,b.u),maxint(v,b.v));}
 IV pow(int k)const;
};
inline IV operator+(const IV&a,const IV&b){return IV(a.u+b.u,a.v+b.v);}
inline IV operator-(const IV&a,const IV&b){return a+-b;}
inline IV operator*(const IV&a,const IV&b){
 if(a.iszero()||b.iszero())return IV();
 cpp_int lo,hi;
 if(a.u>=0){if(b.u>=0){lo=a.u*b.u;hi=a.v*b.v;}else if(b.v<=0){lo=a.v*b.u;hi=a.u*b.v;}else{lo=a.v*b.u;hi=a.v*b.v;}}
 else if(a.v<=0){if(b.u>=0){lo=a.u*b.v;hi=a.v*b.u;}else if(b.v<=0){lo=a.v*b.v;hi=a.u*b.u;}else{lo=a.u*b.v;hi=a.u*b.u;}}
 else {if(b.u>=0){lo=a.u*b.v;hi=a.v*b.v;}else if(b.v<=0){lo=a.v*b.u;hi=a.u*b.u;}else{lo=minint(a.u*b.v,a.v*b.u);hi=maxint(a.u*b.u,a.v*b.v);}}
 return IV(floor_q(lo),ceil_q(hi));
}
inline IV operator/(const IV&a,const IV&b){return a*b.inv();}
inline IV& operator+=(IV&a,const IV&b){a=a+b;return a;}
inline IV& operator-=(IV&a,const IV&b){a=a-b;return a;}
inline IV& operator*=(IV&a,const IV&b){a=a*b;return a;}
inline IV& operator/=(IV&a,const IV&b){a=a/b;return a;}
inline IV rat(const cpp_int&n,const cpp_int&d=1){if(d<=0)throw std::runtime_error("rat denominator must be positive");return IV(floor_div(n*Q,d),ceil_div(n*Q,d));}
inline IV rat(int n,int d=1){return rat(cpp_int(n),cpp_int(d));}
inline IV rat(long long n,long long d=1){return rat(cpp_int(n),cpp_int(d));}
inline IV rat(const std::string&s){
 auto ep=s.find_first_of("eE");int exponent=0;std::string mant=s.substr(0,ep);
 if(ep!=std::string::npos)exponent=std::stoi(s.substr(ep+1));
 bool neg=false;if(!mant.empty()&&(mant[0]=='-'||mant[0]=='+')){neg=mant[0]=='-';mant.erase(0,1);}
 auto dp=mant.find('.');int decimals=dp==std::string::npos?0:int(mant.size()-dp-1);
 if(dp!=std::string::npos)mant.erase(dp,1);if(mant.empty())throw std::runtime_error("empty rational");
 cpp_int n=0;for(char c:mant){if(c<'0'||c>'9')throw std::runtime_error("bad rational digit");n=n*10+(c-'0');}
 if(neg)n=-n;int shift=exponent-decimals;return shift>=0?rat(n*ipow(10,shift)):rat(n,ipow(10,-shift));
}
inline IV rat(const char*s){return rat(std::string(s));}
inline IV zero=IV(0),one=IV(1),ln2;
inline IV IV::pow(int k)const{if(k<0)return pow(-k).inv();IV z=one,x=*this;while(k){if(k&1)z=z*x;k>>=1;if(k)x=x*x;}return z;}
inline IV pow(const IV&a,int k){return a.pow(k);}
inline IV abs(const IV&a){return a.abs();}
inline IV sqrt(const IV&a){return a.sqrt();}
inline IV hull(const IV&a,const IV&b){return a.hull(b);}
inline IV IV::log()const{
 if(u<=0)throw std::runtime_error("log needs positive interval");IV x=*this;int n=0;
 while(x.u<Q/4){x=x*2;--n;}while(x.v>Q){x=x/2;++n;}
 // The 200-term atanh remainder +[-1,1]/Q is proved only on this domain.
 if(x.u<Q/4||x.v>Q)throw std::runtime_error("log interval too wide for certified reduction");
 IV z=(x-one)/(x+one),out=zero,z2=z*z,vv=z;
 for(int i=0;i<200;++i){out+=vv/(2*i+1);vv=vv*z2;}
 return 2*out+IV(-1,1)+n*ln2;
}
struct J {
 std::array<IV,4>A;
 J():A{zero,zero,zero,zero}{}
 explicit J(int x):A{IV(x),zero,zero,zero}{}
 explicit J(const IV&x):A{x,zero,zero,zero}{}
 explicit J(const char*x):J(rat(x)){}
 J(std::initializer_list<IV>x):J(){if(x.size()>4)throw std::runtime_error("jet size");std::copy(x.begin(),x.end(),A.begin());}
 J(const std::vector<IV>&x):J(){if(x.size()>4)throw std::runtime_error("jet size");std::copy(x.begin(),x.end(),A.begin());}
 J operator-()const{J z;for(int i=0;i<4;++i)z.A[i]=-A[i];return z;}
 J inv()const;
 J pow(int k)const;
 J log()const;
 J sqrt()const;
 J der()const{return J{A[1],2*A[2],3*A[3],zero};}
};
inline J operator+(const J&a,const J&b){J z;for(int i=0;i<4;++i)z.A[i]=a.A[i]+b.A[i];return z;}
inline J operator+(const J&a,const IV&b){J z=a;z.A[0]+=b;return z;}
inline J operator+(const IV&a,const J&b){return b+a;}
inline J operator+(const J&a,int b){return a+IV(b);}
inline J operator+(int a,const J&b){return b+IV(a);}
inline J operator-(const J&a,const J&b){return a+-b;}
inline J operator-(const J&a,const IV&b){return a+-b;}
inline J operator-(const IV&a,const J&b){return a+-b;}
inline J operator-(const J&a,int b){return a+-IV(b);}
inline J operator-(int a,const J&b){return IV(a)+-b;}
inline J operator*(const J&a,const J&b){J z;for(int k=0;k<4;++k)for(int j=0;j<=k;++j)z.A[k]+=a.A[j]*b.A[k-j];return z;}
inline J operator*(const J&a,const IV&b){J z;for(int i=0;i<4;++i)z.A[i]=a.A[i]*b;return z;}
inline J operator*(const IV&a,const J&b){return b*a;}
inline J operator*(const J&a,int b){return a*IV(b);}
inline J operator*(int a,const J&b){return b*IV(a);}
inline J operator/(const J&a,const J&b){return a*b.inv();}
inline J operator/(const J&a,const IV&b){return a*b.inv();}
inline J operator/(const IV&a,const J&b){return a*b.inv();}
inline J operator/(const J&a,int b){return a/IV(b);}
inline J operator/(int a,const J&b){return IV(a)/b;}
inline J&operator+=(J&a,const J&b){a=a+b;return a;}
inline J&operator-=(J&a,const J&b){a=a-b;return a;}
inline J J::inv()const{J z;IV h=A[0].inv();z.A[0]=h;for(int i=1;i<4;++i){IV ss=zero;for(int j=1;j<=i;++j)ss+=A[j]*z.A[i-j];z.A[i]=-ss*h;}return z;}
inline J J::pow(int k)const{
 if(k<0)return pow(-k).inv();
 // Most jets are affine in the Taylor variable. The binomial identity gives
 // exactly the same derivatives with fewer interval operations.
 if(A[2].iszero()&&A[3].iszero()){
  J z;for(int j=0;j<4&&j<=k;++j){cpp_int c=1;for(int i=0;i<j;++i)c=c*(k-i)/(i+1);z.A[j]=A[0].pow(k-j)*A[1].pow(j)*rat(c);}return z;
 }
 J v(1),x=*this;while(k){if(k&1)v=v*x;k>>=1;if(k)x=x*x;}return v;
}
inline J pow(const J&a,int k){return a.pow(k);}
inline J J::log()const{auto iz=inv().A;J y(A[0].log());for(int n=1;n<4;++n){IV s;for(int k=1;k<=n;++k)s+=k*A[k]*iz[n-k];y.A[n]=s/n;}return y;}
inline J J::sqrt()const{J y(A[0].sqrt());for(int j=1;j<4;++j){IV ss;for(int t=1;t<j;++t)ss+=y.A[t]*y.A[j-t];y.A[j]=(A[j]-ss)/(2*y.A[0]);}return y;}
inline J solve(const IV&val,const std::function<J(const J&)>&der){J z(val);for(int i=0;i<3;++i)z.A[i+1]=der(z).A[i]/(i+1);return z;}
inline IV pi,p,R,a,v,cut,small,uR;
inline std::vector<IV>co,breaks,alp,beta,VR_list,edge_dummy,Tp0,Tp1,Tp2;
inline std::vector<int>ks;
inline std::vector<std::vector<IV>>edgevals;
inline cpp_int comb(int n,int k){if(k<0||k>n)return 0;k=std::min(k,n-k);cpp_int c=1;for(int j=1;j<=k;++j)c=c*(n-j+1)/j;return c;}
inline std::vector<IV> cs(int count=38){
 std::vector<IV> result(count,zero);
 // Group exact numerators by norm before interval conversion. All required
 // lattice points and square truncations are retained. Central symmetry
 // gives the factor two for the half square (n>0 or n=0,k>0).
 for(int mode=0;mode<2;++mode){
  const int B=mode==0?256:48;
  std::map<int,std::vector<cpp_int>> sums;
  for(int n=0;n<=B;++n)for(int k=(n==0?1:-B);k<=B;++k){
   int norm=n*n+n*k+k*k;cpp_int ar=2*n+k,bi=k;
   cpp_int ar2=ar*ar,bi2=bi*bi;
   cpp_int re6=ar2*ar2*ar2-45*ar2*ar2*bi2+135*ar2*bi2*bi2-27*bi2*bi2*bi2;
   cpp_int im6=6*ar*ar2*ar2*bi-60*ar*ar2*bi*bi2+54*ar*bi*bi2*bi2;
   auto [it,inserted]=sums.try_emplace(norm,std::vector<cpp_int>(mode==0?1:count));auto& sums_m=it->second;
   if(mode==0){sums_m[0]+=2*re6;continue;}
   cpp_int re=re6,im=im6;
   for(int m=1;m<=count;++m){if(m>=2)sums_m[m-1]+=2*re;if(m<count){cpp_int nr=re*re6-3*im*im6;im=re*im6+im*re6;re=std::move(nr);}}
  }
  for(auto& item:sums){cpp_int base=64*ipow(cpp_int(item.first),6),den=base;for(int m=1;m<=(mode==0?1:count);++m){if(mode==0||m>=2)result[m-1]+=rat(item.second[m-1],den);den*=base;}}
 }
 for(int m=1;m<=count;++m){int B=m==1?256:48,h=6*m;IV extra=8*pow(rat(4,3),3*m)*pow(rat(B),2-h)/(h-2);result[m-1]=(result[m-1]+IV(-extra.v,extra.v))*pow(a,-h)/h;}
 return result;
}
inline J cpol(const J&t,const std::vector<IV>&coeff){
 IV mid=t.A[0].mid();J h=t-mid;std::vector<IV> cc(coeff.size(),zero);
 for(size_t j=0;j<coeff.size();++j)for(size_t ll=j;ll<coeff.size();++ll)cc[j]+=rat(comb(ll,j))*coeff[ll]*pow(mid,ll-j);
 J z(0);for(auto it=cc.rbegin();it!=cc.rend();++it)z=z*h+*it;return z;
}
inline J sm(const J&t,int seg){if(seg<0)return J(0);if(seg>0)return J(1);return cpol(t,{zero,zero,zero,rat(10),rat(-15),rat(6)});}
inline std::pair<J,J>PQt(const J&t){J h=t/v;return {v*cpol(h,{zero,one,zero,rat(-6),rat(8),rat(-3)}),v*v/2*cpol(h,{zero,zero,one,rat(-3),rat(3),-one})};}
inline IV hor(const IV&x,const std::vector<IV>&coeff){IV z;for(auto it=coeff.rbegin();it!=coeff.rend();++it)z=z*x+*it;return z;}
inline J hor(const J&x,const std::vector<IV>&coeff){J z;for(auto it=coeff.rbegin();it!=coeff.rend();++it)z=z*x+*it;return z;}
inline std::pair<J,std::vector<J>> basis(const J&t,int seg){
 J g=-t.log()+pi/2*t*t,b0;J Pr,Qr;
 if(seg<3)b0=g;else if(seg<5){auto pq=PQt(t-R);Pr=pq.first;Qr=pq.second;b0=-R.log()+pi/2*R*R+(-1/R+pi*R)*Pr+(1/(R*R)+pi)*Qr;}else b0=J(-R.log()+pi/2*R*R);
 std::vector<J>bm(M),mm(M);
 if(seg<1){}else if(seg==1){J h=t-p;for(int i=0;i<M;++i)bm[i]=Tp0[i]+Tp1[i]*h+Tp2[i]*h*h;}
 else if(seg==2){J z=t*t-p*p;for(int i=0;i<M;++i)bm[i]=hor(z,edgevals[i]);}
 else if(seg<5){for(int i=0;i<M;++i)bm[i]=VR_list[i]+Pr*alp[i]+Qr*beta[i];}
 else{for(int i=0;i<M;++i)bm[i]=J(VR_list[i]);}
 J cu=sm((t-small)/cut,seg==1?0:(seg<1?-1:1));
 J gc=sm((t-R)/rat("0.10"),(seg>=3&&seg<=6)?0:(seg<3?-1:1));
 J cer=sm((t-R-rat("0.001"))/rat("0.075"),(seg==4||seg==5)?0:(seg<4?-1:1));
 for(int i=0;i<M;++i){bm[i]=cu*bm[i];mm[i]=co[i+1]*((i+1)%2?-1:1)*pow(t,ks[i+1])*(1-gc);}
 J smm(0),sbm(0);for(int i=0;i<M;++i){smm+=mm[i];sbm+=bm[i];}
 std::vector<J>D(M+1);
 if(seg<4){if(seg>=3)D[0]=b0-g;for(int i=0;i<M;++i)D[i+1]=bm[i]-mm[i];return {g+smm,D};}
 if(seg>=6)return {b0+sbm,D};
 D[0]=b0-g;J sd=D[0];for(int i=0;i<M;++i){D[i+1]=bm[i]-mm[i];sd+=D[i+1];}
 for(J&d:D)d=(1-cer)*d;return {g+smm+cer*sd,D};
}
struct JS {J s1,s2;std::map<int,J>ps;};
struct SState {IV s1,s2;std::map<int,IV>ps;};
inline std::vector<int>ek;
inline std::vector<IV>bv,s2coeff;
inline std::map<int,std::vector<IV>>pscoeff;
inline void init_ss_coefficients(){
 ek={2};ek.insert(ek.end(),ks.begin()+1,ks.end());bv={pi};
 for(int i=1;i<=M;++i)bv.push_back((i%2?-1:1)*co[i]*ks[i]);
 // Collect finite polynomial coefficients exactly algebraically; every
 // coefficient operation remains outward-rounded at 144 bits.
 s2coeff.assign(12*M+1,zero);
 for(size_t i=0;i<ek.size();++i){s2coeff[ek[i]]+=-2*bv[i]/ek[i];for(size_t j=0;j<ek.size();++j)s2coeff[ek[i]+ek[j]]+=bv[i]*bv[j]/(ek[i]+ek[j]);}
 pscoeff.clear();for(int k:ks){auto&cc=pscoeff[k];cc.resize(ek.size());for(size_t i=0;i<ek.size();++i)cc[i]=bv[i]/(ek[i]+k);}
}
inline JS ss0(const J&t,bool need_ps=true){
 JS s;std::vector<J>powers(12*M+1);powers[0]=J(1);powers[1]=t;for(size_t e=2;e<powers.size();++e)powers[e]=powers[e-1]*t;
 s.s1=t*t/2*(rat(1,2)-t.log())+pi/8*powers[4];
 for(int i=1;i<=M;++i)s.s1+=((i%2?-1:1)*co[i]/(ks[i]+2))*powers[ks[i]+2];
 s.s2=J(0);for(size_t e=0;e<s2coeff.size();++e)if(!s2coeff[e].iszero())s.s2+=s2coeff[e]*powers[e];
 if(need_ps)for(auto&item:pscoeff){J vv(0);for(size_t i=0;i<ek.size();++i)vv+=item.second[i]*powers[ek[i]];s.ps[item.first]=vv;}
 return s;
}
inline std::vector<IV> fh(const J&t,int seg,const SState*S=nullptr){
 // For the unmodified core, the harmonic modes cancel algebraically between
 // ss0 and D=-mm. This exact identity is independent of every c_m. The energy
 // is zero because t*(-c_m*t^k)' - k*(-c_m*t^k)=0.
 if(seg==0 && S==nullptr){J f=(pi*t*t-rat(1,2))*t.log()-rat(3,8)*pi*pi*pow(t,4);return {f.A[0],f.A[1],2*f.A[2],zero,zero,zero};}
 auto bd=basis(t,seg);J B=bd.first;auto&D=bd.second;J B1=B.der()+1/t;JS ss;
 if(S==nullptr)ss=ss0(t,true);
 else{ss.s1=solve(S->s1,[&](const J&){return t*B;});ss.s2=solve(S->s2,[&](const J&){return -2*B1+pow(B1,2)*t;});for(auto&kv:S->ps){int ke=kv.first;ss.ps[ke]=solve(kv.second,[&](const J&F){return B1-ke*F/t;});}}
 J dsum(0),lin(0),quad(0),e(0);std::vector<J>Qj;
 for(size_t i=0;i<D.size();++i){dsum+=D[i]/(ks[i]+2);lin+=-2*D[i]+2*ks[i]*D[i]*ss.ps.at(ks[i]);Qj.push_back(t*D[i].der()-ks[i]*D[i]);}
 // The bilinear forms are symmetric; include each off-diagonal pair twice.
 for(size_t i=0;i<D.size();++i)for(size_t j=i;j<D.size();++j){int mult=i==j?1:2;quad+=mult*ks[i]*ks[j]*D[i]*D[j]/(ks[i]+ks[j]);e+=mult*Qj[i]*Qj[j]/(ks[i]+ks[j]);}
 J f=-2*pi*(ss.s1+t*t*dsum)-rat(1,2)*(t.log()+ss.s2+lin+quad);e=rat(1,2)*e;
 return {f.A[0],f.A[1],2*f.A[2],e.A[0],e.A[1],2*e.A[2]};
}
inline std::array<J,3>dels(const J&t,int seg){J b=basis(t,seg).first,bp=b.der()+1/t;return {t*b,-2*bp+pow(bp,2)*t,bp};}
inline std::vector<IV>ts;
inline std::vector<int>orig;
inline std::vector<std::vector<IV>>pts,cels;
inline std::vector<cpp_int>UIL,VIL;
inline IV hx,l,bcons,eps,lambda_,mu,K;
inline int nsamp(const IV&aa,const IV&bb,const IV&h){cpp_int j=ceil_div(((bb-aa)/h).v,Q);return std::max(1,j.convert_to<int>());}
inline IV integ(const IV&H,const J&y,const J&yc){IV err=pow(H,3)*abs(yc.A[2])/12;return H*y.A[0]+IV(-err.v,err.v);}
inline void table(int Nnod){
 ts.clear();orig.clear();
 for(int i=0;i<6;++i){IV lo=breaks[i],up=breaks[i+1];int n=std::max(1,cpp_int(((up-lo)*(i==0?8000:Nnod)).v/Q).convert_to<int>()+1);for(int j=0;j<n;++j){ts.push_back(lo+(up-lo)*j/n);orig.push_back(i);}}
 ts.push_back(breaks.back());orig.push_back(6);pts.resize(ts.size());cels.resize(ts.size()-1);
 for(size_t i=1;i<ts.size();++i){
  if(!(ts[i-1].v<ts[i].u))throw std::runtime_error("table node intervals must be strictly separated");
 }
 std::vector<SState>pointS(ts.size()),cellS(ts.size()-1);JS initial=ss0(J(small));SState S;S.s1=initial.s1.A[0];S.s2=initial.s2.A[0];for(auto&kv:initial.ps)S.ps[kv.first]=kv.second.A[0];
 for(size_t i=1;i<ts.size();++i){IV x=ts[i],old=ts[i-1],H=x-old;int sgprev=orig[i-1];if(sgprev>=1){IV mid=(old+x)/2;J tc{IV(old.u,x.v),one},tm{mid,one};auto zm=dels(tm,sgprev),zc=dels(tc,sgprev);SState ns,bs;
   ns.s1=S.s1+integ(H,zm[0],zc[0]);ns.s2=S.s2+integ(H,zm[1],zc[1]);
   for(auto&kv:S.ps){int ke=kv.first;ns.ps[ke]=pow(old/x,ke)*kv.second+integ(H,pow(tm/x,ke)*zm[2],pow(tc/x,ke)*zc[2]);}
   cpp_int bb=maxint(absint(zc[2].A[0].u),absint(zc[2].A[0].v));IV err=H*IV(-bb,bb);bs.s1=S.s1+IV(0,H.v)*zc[0].A[0];bs.s2=S.s2+IV(0,H.v)*zc[1].A[0];
   for(auto&kv:S.ps)bs.ps[kv.first]=pow(old/tc.A[0],kv.first)*kv.second+err;
   cellS[i-1]=std::move(bs);S=std::move(ns);
  }pointS[i]=S;
  if(i%1000==0)std::cerr<<"table propagation "<<i<<"/"<<ts.size()<<"\n";
 }
 // Propagation above is serial. Once its complete interval states are saved,
 // independent point and cell evaluations may be distributed across CPUs.
 #pragma omp parallel for schedule(dynamic,4)
 for(long i=0;i<long(ts.size());++i){J tt{ts[i],one};pts[i]=fh(tt,orig[i],orig[i]==0?nullptr:&pointS[i]);if(i>0){J tc{IV(ts[i-1].u,ts[i].v),one};cels[i-1]=fh(tc,orig[i-1],orig[i-1]<1?nullptr:&cellS[i-1]);}}
}
inline void core_test(){
 IV h=rat(".00022"),bc,dsum,d2;
 for(int seg=0;seg<6;++seg){IV aa=breaks[seg],bb=breaks[seg+1];int n=nsamp(aa,bb,h);std::vector<std::array<IV,3>>result(n);
  #pragma omp parallel for schedule(dynamic,4)
  for(int j=0;j<n;++j){IV lo=aa+(bb-aa)*j/n,hi=aa+(bb-aa)*(j+1)/n;J tt{IV(lo.u,hi.v),one};auto bd=basis(tt,seg);J bi=bd.first.der()+1/tt;IV norm=abs(bi.A[0])+abs(bi.A[1])+abs(bi.A[2]),dsm,sm2;for(size_t i=0;i<ks.size();++i){IV v1;for(auto&x:bd.second[i].A)v1+=abs(x);dsm+=pow(IV(ks[i]+1),3)*v1;sm2+=pow(IV(ks[i]+1),2)*v1;}result[j]={norm,dsm,sm2};}
  for(auto&r:result){if(r[0].v>bc.v)bc=r[0];if(r[1].v>dsum.v)dsum=r[1];if(r[2].v>d2.v)d2=r[2];}
  if(!(bc.v<6000*Q&&dsum.v<2000000*Q))throw std::runtime_error("core_test bound failed");
 }
}
inline IV clamp_i(const IV&x){cpp_int lo=maxint(0,x.u),hi=minint(Q,x.v);if(lo>hi)throw std::runtime_error("empty clamp");return IV(lo,hi);}
inline std::vector<IV>tail(const IV&T){return {pts.back()[0]+eps-pi*bcons*(T*T-l*l),-2*pi*bcons*T,-2*pi*bcons,zero,zero,zero};}
inline std::vector<IV>lookup(const IV&T,bool full=false){
 if(T.v<hx.u)throw std::runtime_error("lookup below domain");std::vector<IV>out;
 auto add=[&](const std::vector<IV>&next){if(out.empty())out=next;else for(size_t j=0;j<out.size();++j)out[j]=out[j].hull(next[j]);};
 if(T.v>=l.u){auto z=tail(T);add(full?z:std::vector<IV>{z[0],z[3]});}
 int im=std::max(0,int(std::lower_bound(VIL.begin(),VIL.end(),T.u)-VIL.begin())-1),ix=std::min(int(cels.size()),int(std::upper_bound(UIL.begin(),UIL.end(),T.v)-UIL.begin()));
 for(int i=im;i<ix;++i){if(full){std::vector<IV>z=cels[i];for(auto&vv:z)vv+=eps;add(z);continue;}IV H=ts[i+1]-ts[i],aa=(T-ts[i])/H;cpp_int xu=maxint(0,aa.u),xv=minint(Q,aa.v);if(xu>xv)continue;IV X(xu,xv),fv=pts[i][0]+X*(pts[i+1][0]-pts[i][0]),ev=pts[i][3]+X*(pts[i+1][3]-pts[i][3]),er=H*H/8,err=abs(cels[i][2])*er;fv+=IV(-err.v,err.v);err=abs(cels[i][5])*er;ev+=IV(-err.v,err.v);add({fv+eps,ev+eps});}
 if(out.empty())throw std::runtime_error("empty lookup");return out;
}
inline void init_constants(){
 IV vv=one/3,acc;for(int i=0;i<200;++i){acc+=vv/(2*i+1);vv=vv/9;}ln2=2*acc+IV(-1,1);
 pi=zero;for(auto item:std::vector<std::pair<int,int>>{{5,16},{239,-4}}){int q=item.first,s=item.second;IV term=one/q,ac;for(int j=0;j<150;++j){ac+=(j%2?-1:1)*term/(2*j+1);term=term/(q*q);}ac+=IV(-2,2);pi+=s*ac;}
 p=(2/rat(3).sqrt()).sqrt()/2;R=2*p/rat(3).sqrt();a=2*p;
}
inline void init_after_co(){
 if(!(abs(co[1]).v<rat(1).u))throw std::runtime_error("co1 bound failed");ks={6};for(int m=1;m<=M;++m)ks.push_back(6*m);
 v=rat(".075");cut=rat(".06");small=p-cut;breaks={rat(".28209"),small,p,R,R+rat(".001"),R+v,R+rat(".076")};
 uR=R*R-p*p;alp.clear();beta.clear();VR_list.clear();edgevals.clear();Tp0.clear();Tp1.clear();Tp2.clear();
 for(int i=1;i<=M;++i){IV c=co[i];int k=ks[i];std::vector<IV>vals,qc,sc,edge;for(int j=0;j<=k/2;++j){IV z=rat((j%2?-1:1)*comb(k,2*j))*pow(p,k-2*j);vals.push_back(z);edge.push_back(c*z);if(j>=1)qc.push_back(j*z);if(j>=2)sc.push_back(j*(j-1)*z);}IV xx=hor(uR,vals),qq=hor(uR,qc),ss=hor(uR,sc);VR_list.push_back(c*xx);alp.push_back(c*2*R*qq);beta.push_back(c*(4*R*R*ss+2*qq));edgevals.push_back(std::move(edge));IV t0=c*pow(p,k);Tp0.push_back(t0);Tp1.push_back(t0*(-k*(k-1))/p);Tp2.push_back(t0*k*(k-1)*(rat((k-2)*(k-3),6)-rat(1,2))/(p*p));}
 init_ss_coefficients();
}
inline void init_core(){
 init_constants();std::cerr<<"computing lattice coefficients\n";co={zero};auto cc=cs(M);co.insert(co.end(),cc.begin(),cc.end());init_after_co();std::cerr<<"building table\n";table(24000);
 UIL.clear();VIL.clear();for(auto&x:ts){UIL.push_back(x.u);VIL.push_back(x.v);}hx=ts.front();l=ts.back();bcons=-R.log()+pi/2*R*R;for(auto&x:VR_list)bcons+=x;IV eerr=rat(".00000000001");eps=IV(-eerr.v,eerr.v);bcons+=eps;
 std::cerr<<"core_test\n";core_test();
}
