#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <map>
#include <vector>
using namespace std;
using LL=int64_t;
using Big=__int128_t;
const LL S=1LL<<40;
LL safe(Big x){ assert(x > -(Big(1)<<62) && x < (Big(1)<<62)); return LL(x); }
LL mf(LL a,LL b){
 Big x=Big(a)*b;
 if(x>=0)return safe(x>>40);
 return safe(-((-x+S-1)>>40));
}
LL floor_div(Big x,Big y){
 assert(y>0);
 if(x>=0) return safe(x/y);
 return safe(-((-x+y-1)/y));
}
struct I{
 LL l=0,h=0;
};
I units(LL l,LL h){assert(l<=h);return {l,h};}
I unit(LL x){return {x,x};}
I integer(int x){return unit(x*S);}
I rat(LL x,LL y){return {floor_div(Big(x)*S,y),-floor_div(-Big(x)*S,y)};}
I operator+(I a,I b){return units(safe(Big(a.l)+b.l),safe(Big(a.h)+b.h));}
I operator-(I a){return {-a.h,-a.l};}
I operator-(I a,I b){return a+ -b;}
I operator*(I a,I b){
 if(a.l>=0){
  if(b.l>=0)return {mf(a.l,b.l),-mf(-a.h,b.h)};
  if(b.h<=0)return {mf(a.h,b.l),-mf(-a.l,b.h)};
  return {mf(a.h,b.l),-mf(-a.h,b.h)};
 }
 if(a.h<=0)return -((-a)*b);
 if(b.l>=0)return {mf(a.l,b.h),-mf(-a.h,b.h)};
 if(b.h<=0)return -(a*(-b));
 return {min(mf(a.l,b.h),mf(a.h,b.l)),max(-mf(-a.l,b.l),-mf(-a.h,b.h))};
}
I sq(I a){
 if(a.l<0 && a.h>0)return {0,max(-mf(-a.l,a.l),-mf(-a.h,a.h))};
 return a*a;
}
I inv(I a){
 if(a.h<0)return -inv(-a);
 assert(a.l>0);
 return {safe(Big(S)*S/a.h),safe((Big(S)*S+a.l-1)/a.l)};
}
I operator/(I a,I b){return a*inv(b);}
I clip(I a,LL lo,LL hi){return units(max(a.l,lo),min(a.h,hi));}
LL mag(I a){return max(-a.l,a.h);}
I atanh2(I z){ // |z|<= .334
 assert(mag(z)<=S/3+4);
 I z2=sq(z);
 const int N=14;
 I sum=rat(1,2*N+1);
 for(int n=N-1;n>=0;n--)sum=rat(1,2*n+1)+z2*sum;
 return integer(2)*z*sum+units(-2,2); // tail < 2/S
}
I ln(LL x){
 assert(x>0);
 I m=unit(x);
 int k=0;
 while(m.l<S){m=m*integer(2);k--;}
 while(m.l>=2*S){m=m*rat(1,2);k++;}
 static const I log2=atanh2(rat(1,3));
 return integer(k)*log2+atanh2((m-integer(1))/(m+integer(1)));
}
pair<I,I> L_endpoint(LL x){
 I z=unit(x),val,der;
 if(abs(x)<=S/4){
  const int N=22;
  val=rat(1,N+1);der=rat(N,N+1);
  for(int i=N-1;i>=0;i--){
   val=rat(1,i+1)+z*val;
   if(i>0)der=rat(i,i+1)+z*der;
  }
  val=val+units(-1,1);der=der+units(-1,1);
 }else{
  val= -ln(S-x)/z;
  der=(inv(integer(1)-z)-val)/z;
 }
 return {val,der};
}
LL cb_floor(LL x){
 assert(x>=0 && x<8*S);
 LL lo=0,hi=2*S;
 while(hi-lo>1){
  LL m=(hi+lo)/2;
  if(Big(m)*m*m<=Big(x)*S*S)lo=m;else hi=m;
 }
 return lo;
}

const int dim=3;
struct J{
 I v;
 array<I,dim> g{}; // gradients
};
J cn(I v){return {v,{}};}
J cn(int x){return cn(integer(x));}
J rj(LL x,LL y){return cn(rat(x,y));}
J var(I v,int i){J a=cn(v);a.g[i]=integer(1);return a;}
J operator+(J a,J b){
 a.v=a.v+b.v;for(int i=0;i<dim;i++)a.g[i]=a.g[i]+b.g[i];return a;
}
J operator-(J a){
 a.v= -a.v;for(I& x:a.g)x= -x;return a;
}
J operator-(J a,J b){return a+ -b;}
J operator*(J a,J b){
 J c=cn(a.v*b.v);
 for(int i=0;i<dim;i++)c.g[i]=a.v*b.g[i]+a.g[i]*b.v;
 return c;
}
J sq(J a){
 J c=cn(sq(a.v));
 for(int i=0;i<dim;i++)c.g[i]=integer(2)*a.v*a.g[i];
 return c;
}
J inv(J a){
 J c=cn(inv(a.v));I deriv= -sq(c.v);
 for(int i=0;i<dim;i++)c.g[i]=deriv*a.g[i];
 return c;
}
J operator/(J a,J b){return a*inv(b);}
J cube_root(J a){
 J c=cn(units(cb_floor(a.v.l),cb_floor(a.v.h)+1));
 I deriv=inv(integer(3)*sq(c.v));
 for(int i=0;i<dim;i++)c.g[i]=deriv*a.g[i];
 return c;
}
J L(J a){
 auto p=L_endpoint(a.v.l);
 auto q=L_endpoint(a.v.h);
 J c=cn(units(p.first.l,q.first.h));
 I deriv=units(p.second.l,q.second.h);
 for(int i=0;i<dim;i++)c.g[i]=deriv*a.g[i];
 return c;
}

// compute v,g of q^18 and q^6(log q)^j, j=0..3
using QT=array<pair<I,I>,5>;
QT qt_direct(I q){
 array<I,19> pw;pw[0]=integer(1);
 for(int i=1;i<=18;i++)pw[i]=pw[i-1]*q;
 QT out;
 out[0]={pw[18],integer(18)*pw[17]};
 I logs=integer(1),ll=integer(0);
 if(q.l>0)ll=units(ln(q.l).l,min(LL(0),ln(q.h).h));
 I prev5{};
 for(int j=0;j<=3;j++){
  I i5,i6;
  if(j==0 || q.l>0){i5=pw[5]*logs;i6=pw[6]*logs;}
  else{ i5=units(-pw[2].h,pw[2].h);i6=units(-pw[3].h,pw[3].h); }
  // q^(h/2)|log q|^j <=1 for h>=5, j<=3
  auto trim=[&](I x,LL bound){
   return clip(x,j%2? -bound:0,j%2? 0:bound);
  };
  i5=trim(i5,pw[2].h);i6=trim(i6,pw[3].h);
  out[j+1]={i6,integer(6)*i5+integer(j)*prev5};
  prev5=i5;
  if(j<3)logs=logs*ll;
 }
 return out;
}
array<J,5> qt(I q,int i){
 static map<pair<LL,LL>,QT> cache;
 auto key=make_pair(q.l,q.h);
 auto it=cache.find(key);
 if(it==cache.end())it=cache.emplace(key,qt_direct(q)).first;
 array<J,5> out;
 for(int j=0;j<5;j++){
  auto p=it->second[j];out[j]=cn(p.first);out[j].g[i]=p.second;
 }
 return out;
}
struct Params{
 J c0,c1,s1,del,ch,cu;
};
array<J,4> coeff(array<I,3> box,const Params& par){
 auto q=qt(box[0],0),r=qt(box[1],1);
 J a=var(box[2],2);
 J iz=inv(cn(1)+q[0]+r[0]);
 array<J,3> v={cn(3)*iz-cn(1),cn(3)*iz*q[0]-cn(1),cn(3)*iz*r[0]-cn(1)};
 for(J& u:v)u.v=clip(u.v,-S,2*S);
 J T=cn(1)-cn(3)*iz*q[1]*r[1];
 J W=cn(216)*iz*(q[3]*r[1]+q[1]*r[3]-q[2]*r[2]);
 J Y=cn(648)*iz*(cn(2)*(q[4]*r[1]+q[1]*r[4])-cn(3)*(q[3]*r[2]+q[2]*r[3]));
 J prod=cn(1),x=cn(0),y=v[0]*v[1]*v[2]*rj(1,2);
 array<J,3> log_over;
 for(int i=0;i<3;i++){
  J z=a*v[i];
  prod=prod*(cn(1)-z);
  x=x+sq(v[i])*rj(1,6);
  log_over[i]= -v[i]*L(z);
 }
 J root=cube_root(prod);
 J Te=(cn(3)*x+cn(2)*a*y)/(cn(1)+root+sq(root));
 J avg=(log_over[0]+log_over[1]+log_over[2])*rj(1,3);
 for(J& h:log_over)h=h-avg;
 J We=root*(sq(log_over[0])+sq(log_over[1])+sq(log_over[2]))*rj(1,3);
 J Ye=a*root*log_over[0]*log_over[1]*log_over[2];
 auto [c0,c1,s1,del,ch,cu]=par;
 J s0=c0+rj(1,3);
 return {
  T-Te+c0*(W-We)+s0*(Y-Ye),
  c1*(W-We)+s1*(Y-Ye)+c0*We+s0*Ye+(rj(1,2)-del)*Te,
  c1*We+s1*Ye+ch*Te+del,
  cu*del+rj(1,2)*ch*Te
 };
}
vector<array<J,3>> rows(){
 vector<array<J,3>> rows;
 vector<int> nodes={30,50,75,100,150,200,300,400,500,650,800,900,1000};
 for(unsigned i=1;i<nodes.size();i++){
  J a=rj(nodes[i-1],1000),b=rj(nodes[i],1000);
  rows.push_back({a,sq(a),a*sq(a)});
  rows.push_back({(cn(2)*a+b)*rj(1,3),a*(a+cn(2)*b)*rj(1,3),sq(a)*b});
  rows.push_back({(a+cn(2)*b)*rj(1,3),b*(b+cn(2)*a)*rj(1,3),a*sq(b)});
 }
 rows.push_back({cn(1),cn(1),cn(1)});
 return rows;
}
LL visits;
void visit(array<I,3> box,const Params& par,int depth=0){
 visits++;
 if(box[1].l>box[0].h)return; // use symmetry; boundary still covered
 auto cs=coeff(box,par);
 array<J,4> mid_cs{};
 bool have_mid=false;
 array<I,3> mid,rad;
 for(int i=0;i<3;i++){
  auto [l,h]=box[i];
  mid[i]=unit((h+l)/2);
  rad[i]=unit(h-mid[i].l);
 }
 static const auto rs=rows();
 array<LL,dim> issues{};
 bool failed=false;
 for(auto row:rs){
  auto dot=[&](array<J,4>& vv){return vv[0]+row[0]*vv[1]+row[1]*vv[2]+row[2]*vv[3];};
  J bound=dot(cs);
  if(bound.v.l>0)continue;
  if(!have_mid){have_mid=true;mid_cs=coeff(mid,par);}
  J value=dot(mid_cs);
  LL total=0;array<LL,dim> term;
  for(int i=0;i<dim;i++){
   term[i]=(unit(mag(bound.g[i]))*rad[i]).h;
   total=safe(Big(total)+term[i]);
  }
  if(value.v.l>total)continue;
  failed=true;
  for(int i=0;i<dim;i++)issues[i]=max(issues[i],term[i]);
 }
 int split=max_element(issues.begin(),issues.end())-issues.begin();
 if(!failed)return;
 assert(issues[split]>0);
 if(depth>80 || rad[split].l<=1){
  for(auto b:box)cerr<<double(b.l)/S<<" "<<double(b.h)/S<<"; ";
  cerr<<" depth "<<depth<<endl;
  assert(false);
 }
 auto next=box;next[split].h=mid[split].l;
 visit(next,par,depth+1);
 next=box;next[split].l=mid[split].l;
 visit(next,par,depth+1);
}
void run(int id){
 array<Params,3> params={{
  {rj(-268,1000),rj(-60,1000),rj(-55,1000),rj(130,1000),rj(1,16),rj(15,32)},
  {rj(-269,1000),rj(67,1000),rj(47,1000),rj(55,1000),rj(1,16),rj(15,32)},
  {rj(-271,1000),rj(58,1000),rj(49,1000),rj(50,1000),rj(1,12),rj(1,2)}
 }};
 // initial boxes to avoid overly loose derivative overflow
 vector<int> endpoints={0,190,448,477};
 visits=0;
 for(int i=0;i<24;i++){
  for(int j=0;j<=i;j++)for(int k=0;k<16;k++){
   int alo=endpoints[id],ahi=endpoints[id+1];
   array<I,3> box={
    units(rat(i,24).l,rat(i+1,24).h),
    units(rat(j,24).l,rat(j+1,24).h),
    units(rat(16*alo+(ahi-alo)*k,16000).l,rat(16*alo+(ahi-alo)*(k+1),16000).h)
   };
   visit(box,params[id]);
  }
  cerr<<id<<","<<i<<": "<<visits<<endl;
 }
}
int main(int argc,char**argv){
 assert(argc==2);run(atoi(argv[1]));
}
