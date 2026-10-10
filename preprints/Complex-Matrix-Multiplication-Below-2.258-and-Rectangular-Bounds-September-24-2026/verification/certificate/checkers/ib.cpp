#include "menu.hpp"
#include <fstream>
#include <map>
constexpr int NH=112,NP=220,NX=22,NC=2160;
constexpr I BF=I(1)<<44;
I PI,R,r0,gamma0,rc[5],tri;
I ha[NH+1][NH+1];
struct PC{int d,s;I x;};
vector<PC> pcs,xcs;
void data(){
 ifstream f("dat");assert(f>>PI>>R>>r0>>gamma0);for(auto&x:rc)assert(f>>x);assert(f>>tri);
 for(int d=0;d<=NH;d++)for(int i=0;i<=d;i++)assert(f>>ha[i][d-i]);
 for(int d=0;d<=NP;d++)for(int i=0;i<=d/2;i++){I x;assert(f>>x);if(x)pcs.push_back({d,d-2*i,x});}
 for(int i=0;i<=NX;i++)for(int j=i%3;j<=min(i,NX-i);j+=3){I x;assert(f>>x);if(x)xcs.push_back({i+j,i-j,x});}
}
I co(I k,I N){k=abs(k)%(6*N);k=min(k,6*N-k);I t=cv(W(k)*PI/(3*N));t=mu(t,t);I s=B;
 for(int i=24;i>=1;i--)s=B-mu(t,s)/((2*i)*(2*i-1));return s;
}
I hv(I r,int l){assert(0<=r&&r<r0);r=di(r,r0);
 I cs[NH+1];for(int s=0;s<=NH;s++)cs[s]=co(I(s)*l,NC);
 I u=0,rp=B;
 for(int d=0;d<=NH;d++,rp=mu(rp,r))for(int i=0;i<=d;i++)u+=mu(mu(ha[i][d-i],rp),cs[abs(2*i-d)]);
 return u;
}
I f0(T p){I f=0;for(I x:p)f+=mu(gamma0-B,ien(x))+mu(2*B-gamma0,ien(B-x));return f;}
vector<Pt> bm;
void hcheck(){I best=B;
 for(int l=0;l<=NC;l++){
  I r=0;for(int k=0;k<5;k++)r+=mu(rc[k],co(3*k*l,NC));
  T p;for(int k=0;k<2;k++)p[k]=(B+2*mu(r,co(l+2*NC*k,NC)))/3;p[2]=B-p[0]-p[1];assert(*min_element(p.begin(),p.end())>B*95/1000);
  I gap=solve(p,bm)-f0(p)-hv(r,l);best=min(best,gap);assert(W(gap)*1000000>-5*W(B));
 }
 printf("h %lld\n",(long long)best);
}
#ifdef HON
int main(){data();bm=lmenu(makemenu());hcheck();}
#endif
#ifndef HON
#ifndef BGRID
#define BGRID 65536
#endif
#ifndef SUB
#define SUB 8192
#endif
constexpr int NB=BGRID,NS=SUB,MG=500;
constexpr I NT=I(NB)*NS;
struct Fields{T p{},e{};};
struct Angular{
 I k;
 I D[3][NP+1]={},E[NP+1]={},c[3][NP+1];
 Angular(I k):k(k){
  for(int h=0;h<3;h++){
   auto &a=c[h];a[0]=B;a[1]=clamp(co(k+2*NT*h,NT),-B,B);
   for(int s=2;s<=NP;s++)a[s]=2*mu(a[1],a[s-1])-a[s-2];
  }
  for(auto x:pcs)for(int h=0;h<3;h++)D[h][x.d]+=mu(x.x,c[h][x.s]);
  for(int d=0;d<=NP;d++)E[d]=D[1][d]-D[0][d]-D[2][d];E[0]+=B/3;E[1]+=mu(R,c[1][1])/3;
 }
 static I val(const I *d,I r){I x=d[NP];for(int i=NP-1;i>=0;i--)x=mu(x,r)+d[i];return x;}
 I ec()const{return val(E,B);}
 I rr()const{I a=0,b=B;if(ec()>=0)return b;
  for(int s=0;s<38;s++){I m=(a+b)/2;if(val(E,m)>=0)a=m;else b=m;}return (a+b)/2;
 }
 Fields fields(I r)const{Fields f;for(int h=0;h<3;h++)f.p[h]=val(D[h],r);
  for(int h=0;h<3;h++)f.e[h]=(B+mu(mu(r,R),c[h][1]))/3+f.p[h]-f.p[(h+1)%3]-f.p[(h+2)%3];
  return f;
 }
};
W mf(W a,I b){return a*b/BF;}
W wab(W a){return a<0?-a:a;}
struct Jet{W d[4][4]={};
 Jet(I k,I sr){
  I cs[NX+1][4],rp[NX+1],r=sr/(B/BF);
  for(int i=0;i<=NX;i++){rp[i]=i?I(mf(rp[i-1],r)):BF;for(int b=0;b<4;b++)cs[i][b]=co(i*k+b*(3*NT/2),NT)/(B/BF);}
  for(auto x:xcs){W fall=x.x;for(int a=0;a<=min(3,x.d);fall*=x.d-a,a++){
   W m=mf(fall,rp[x.d-a]);for(int b=0;b<=3-a;b++,m*=x.s)d[a][b]+=mf(m,cs[x.s][b]);
  }}
 }
 void edge(){for(int k=1;k<=3;k++){
  W n=(k==1?29:k==2?790:19990)*W(BF),v=10;
  for(int a=0;a<=k;a++){assert(wab(d[a][k-a])*v<n);n*=31;v*=25;}
 }}
 void cap(){assert(wab(d[0][1])<999*W(BF)&&wab(d[0][2])<4999*W(BF));}
};
map<pair<int,int>,I> cache;
I grid(int i,int j){auto key=make_pair(i,j);auto it=cache.find(key);if(it!=cache.end())return it->second;
 T p{I(i)*B/MG,I(j)*B/MG,B-(I(i)*B/MG+I(j)*B/MG)};assert(*min_element(p.begin(),p.end())>3*B/100);
 return cache[key]=solve(p,bm)-2*(B/1000000+1);
}
struct Z{I x,y;};
Z zm(Z a,Z b){return {mu(a.x,b.x)-mu(a.y,b.y),mu(a.x,b.y)+mu(a.y,b.x)};}
Z zd(Z a,I r){return {di(a.x,r),di(a.y,r)};}
bool inside(Z z){I q=mu(z.x,z.x)+mu(z.y,z.y);if(q<B/100)return true;
 I r=rt(q,2);Z t=zd(z,r);t=zm(zm(t,t),t);Z v{B,0};I rad=0;
 for(int k=0;k<5;k++,v=zm(v,t))rad+=mu(rc[k],v.x);
 return r<rad-(B/100000000+1);
}
I hz(Z z){z=zd(z,r0);Z v[NH+1];v[0]={B,0};for(int k=1;k<=NH;k++)v[k]=zm(v[k-1],z);
 I u=0;for(int i=0;i<=NH;i++)for(int j=0;j+i<=NH;j++)u+=mu(ha[i][j],mu(v[i].x,v[j].x)+mu(v[i].y,v[j].y));
 return u;
}
I wu(T p){I f=f0(p),x=p[0]*MG,y=p[1]*MG;int i=x/B,j=y/B;I a=x%B,b=y%B;
 I u=lerp(lerp(grid(i,j),grid(i,j+1),b),lerp(grid(i+1,j),grid(i+1,j+1),b),a);
 I out=max(u,f)-(B/50000000+1);
 Z z{(3*p[0]-B)/2,mu(tri,p[2]-p[1])};
 if(inside(z))out=max(out,f+hz(z)-24*(B/1000000+1));
 assert(out>=0);return min(out,29*(B/20));
}
I bestE=B,bestC=B;
I edge(const Angular&a){I r=a.rr();Fields f=a.fields(r);T p=f.p,e=f.e;T q{p[2]+e[0],p[0]+e[2],0};q[2]=B-q[0]-q[1];
 assert(*min_element(q.begin(),q.end())>308*B/10000);
 assert(min({p[0],p[2]})>36*B/1000&&min({e[0],e[2]})>48*B/1000);
 I u=wu(q)+ien(p[2])+ien(p[0])+ien(e[0])+ien(e[2])-ien(q[0])-ien(q[1]);
 Jet j(a.k,r);j.edge();I gap=cv(W(u)*1129/1500-j.d[0][0]*(B/BF));bestE=min(bestE,gap);return gap;
}
I cap(const Angular&a){Fields f=a.fields(B);I u=0;for(int h=0;h<3;h++){
 I l=f.e[(h+1)%3]+f.e[(h+2)%3],p=f.p[h];assert(min({l,p,B-l-p})>35*B/1000);
 u+=(ien(l)+ien(p)+ien(B-l-p))/3;
 }
 Jet j(a.k,B);j.cap();I gap=cv(u-j.d[0][0]*(B/BF));bestC=min(bestC,gap);return gap;
}
I band(I n){return 9*PI/(10*n)+B/200000000+2;}
struct Node{I k,r,e,ge=B,gc=B;
 Node(int i):k(I(i)*NS){Angular a(k);r=a.rr();e=a.ec();I h=21*band(NB)/10;if(e<h)ge=edge(a);if(e>-h)gc=cap(a);}
};
int namb=0;
void paircheck(Node x,Node y){I h=band(NB);
 if(x.e>h){assert(W(min(x.gc,y.gc))*1000000>8*B);return;}
 if(x.e<-h){assert(W(abs(x.r-y.r))*(31*3*20)*NB < W(61*25)*PI);assert(W(min(x.ge,y.ge))*1000000>12*B);return;}
 ++namb;h=band(NT);
 for(int i=0;i<NS;i++){Angular a(x.k+i);I e=a.ec();if(e<=h)assert(W(edge(a))*1000000>12*B);if(e>=-h)assert(W(cap(a))*1000000>8*B);}
}
int main(int argc,char **argv){data();bm=lmenu(makemenu());int lo=argc>1?atoi(argv[1]):0,hi=argc>2?atoi(argv[2]):NB;assert(0<=lo&&lo<=hi&&hi<=NB);
 Node a(lo);for(int i=lo+1;i<=hi;i++){Node b(i);paircheck(a,b);a=b;}
 printf("b %d %d amb %d terms %zu edge %lld cap %lld\n",lo,hi,namb,pcs.size(),(long long)bestE,(long long)bestC);
}
#endif
