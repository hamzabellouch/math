#include<initializer_list>
#include<cstdlib>
#include<cstdio>
#include<cassert>
using Z=__int128;
const int J=14,M=J+1;
struct Jet{Z a[M][M];
 Z low(int s=1){Z t=2*s*a[0][0];for(auto &row:a)for(auto v:row)t-=v<0?-v:v; // incorrect negative center!
 return t+(a[0][0]<0?-a[0][0]:a[0][0])-s*a[0][0];}
};
using Box=Jet[5];
int bin[M][M];
Z T=Z(1)<<69;
long nt[32];
void dfs(Box &q,int n){
 nt[n]++;
 if(q[1].low(-1)>T/100000000+1)return;
 Z err=0;
 for(int f=2;f<5;f++)for(int s:{1,-1}){
 Z x=-q[f].low(s);if(x>0)err+=2*x/10000000000LL+4; // ×2×1e-10 ×2? Need total ×4 for B
 }
 err*=2;
 bool ok=q[0].low()>-T+T/10000000+err;
 if(ok)return;if(n>=28){for(int f=0;f<5;f++)printf("%.12g ",double(q[f].a[0][0])/double(T));puts("");exit(1);}
 for(int sign:{1,-1}){ Box h={};
 for(int f=0;f<5;f++)for(int i=0;i<M;i++)for(int j=0;j<M;j++)
 for(int k=0;k<=j;k++){Z u=q[f].a[i][j];
 if(sign<0 && ((k^j)&1))u=-u;
 h[f].a[k][i]+=u*bin[j][k]>>j;
 }
 dfs(h,n+1);
 }
}
Z read(){
 char s[80];assert(scanf("%79s",s)==1);Z u=0;
 for(char*p=s+(*s=='-');*p;p++)u=u*10+(*p-'0');
 return *s=='-'?-u:u;
}
Z g[5][320][M];int ktop[5];Box b;
int main(){
 for(int i=0;i<M;i++){bin[i][0]=bin[i][i]=1;for(int j=1;j<i;j++)bin[i][j]=bin[i-1][j-1]+bin[i-1][j];}
 assert(read()==T&&read()==128&&read()==J&&read()==5);
 for(int f=0;f<5;f++){
 ktop[f]=int(read()); for(int k=0;k<ktop[f];k++)for(auto &x:g[f][k])x=read();
 }
 for(int u=0;u<128;u++){
 for(int f=0;f<5;f++){b[f]={};
 for(int k=ktop[f]-1;k>=0;k--)for(int j=0;j<M;j++){
 auto a=b[f].a[j];
 for(int i=M-1;i>=1;i--) a[i]=(a[i]*(2*u+1)+a[i-1])>>8;
 a[0]=(a[0]*(2*u+1)>>8)+g[f][k][j];
 }}
 dfs(b,0);
 }
 printf("%ld",nt[0]);for(int i=1;i<32;i++)if(nt[i])printf(" %ld",nt[i]);puts("");
}
