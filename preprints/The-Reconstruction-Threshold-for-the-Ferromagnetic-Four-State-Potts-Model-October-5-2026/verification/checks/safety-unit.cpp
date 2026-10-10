#define main certificate_main
#include "certificate.cpp"
#undef main

static RR eval_numerator(P const& p, array<RR,4> const& x,
                         array<RR,4> const& y) {
    vector<RR> px(S(p.d)), py(S(p.d));
    for (int i=0; i<S(p.d); ++i) {
        px[i]=1; py[i]=1;
        for (int j=0; j<4; ++j) {
            px[i]*=Pow(x[j],l[p.d][i][j]);
            py[i]*=Pow(y[j],l[p.d][i][j]);
        }
    }
    RR result=0;
    for (int i=0; i<S(p.d); ++i)
        for (int j=0; j<S(p.d); ++j)
            result+=p(i,j)*px[i]*py[j];
    return result;
}

int main() {
    init();
    RR factorial=1;
    R max_multinomial=0;
    for (int d=0; d<20; ++d) {
        if(d) factorial*=d;
        assert(factorial==fact[d]);
        for (auto a:l[d]) {
            RR expected=factorial;
            for (int j=0; j<4; ++j) expected/=fact[a[j]];
            assert(expected==coef(a));
            if(d<=11) max_multinomial=max(max_multinomial,coef(a));
        }
    }
    assert(max_multinomial==92400);
    for (int d=0; d<=11; ++d) {
        P w=ones(d);
        for(int i=0;i<S(d);++i) for(int j=0;j<S(d);++j)
            assert(w(i,j)==RR(coef(l[d][i]))*coef(l[d][j]));
        for(auto index:l[d]) for(int i=0;i<4;++i) for(int j=0;j<4;++j) if(i!=j) {
            R c=R(1)<<(d-index[i]);
            for(int t=0;t<=index[j];++t) {
                RR expected=(RR(1)<<(d-index[i]-t))*fact[index[j]]
                    /fact[t]/fact[index[j]-t];
                assert(c==expected);
                if(t<index[j]) assert((c*(index[j]-t))%(2*(t+1))==0);
                c=c*(index[j]-t)/(2*(t+1));
            }
        }
    }
    for (int d:{0,1,3,6,11}) {
        P p(d); p.den=17;
        for(int i=0;i<S(d);++i) for(int j=0;j<S(d);++j)
            p(i,j)=((i*13+j*19)%31)-15;
        for(bool y:{false,true}) {
            array<RR,4> a={2,4,6,8},b={10,12,14,16},c=a,e=b;
            auto& target=y?e:c;
            target[0]/=2; target[2]+=target[0];
            P substituted=sub(p,y,0,2);
            assert(eval_numerator(substituted,a,b)*p.den
                   ==eval_numerator(p,c,e)*substituted.den);
        }
    }
    Mat evaluation=ev(3,3), interpolation=inverse(evaluation);
    R max_inverse=0;
    for(int i=0;i<S(3);++i) for(int j=0;j<S(3);++j) {
        RR z=0;
        for(int k=0;k<S(3);++k) z+=RR(evaluation[i][k])*interpolation[k][j];
        assert(z==(i==j?RR(27*960):RR(0)));
        max_inverse=max(max_inverse,abs(interpolation[i][j]));
    }
    for(int d:{1,2,3,6}) {
        Mat values=ev(d,3);
        for(int i=0;i<S(3);++i) for(int j=0;j<S(d);++j) {
            RR expected=1;
            for(int k=0;k<4;++k) expected*=Pow(RR(l[3][i][k]),l[d][j][k]);
            assert(expected==values[i][j]);
            assert(expected<=Pow(3,d));
        }
    }
    P p(3); p.den=19;
    for(int i=0;i<S(3);++i) for(int j=0;j<S(3);++j) p(i,j)=i*21+j-100;
    P values=act(p,evaluation,3); values.den*=27*27;
    P recovered=act(values,interpolation,3); recovered.den*=960*960;
    for(int i=0;i<p.b.size();++i) assert(p.b[i]*recovered.den==recovered.b[i]*p.den);
    shape a=start();
    for(int i=0;i<4;++i) for(int j=0;j<4;++j) for(int v=0;v<4;++v) {
        R short_product=4*a[i][v]*a[j][v];
        assert(short_product==RR(4)*a[i][v]*a[j][v]);
        assert(short_product%(R(1)<<48)==0);
    }
    RR edge_bound=64*Pow(RR(12)*(RR(1)<<24),2);
    assert(edge_bound<numeric_limits<R>::max());
    cout << "All focused exactness and safety assertions passed.\n"
         << "Max multinomial through degree 11: " << max_multinomial << "\n"
         << "Max absolute interpolation coefficient: " << max_inverse << "\n"
         << "Weighted edge-distance safe bound: " << edge_bound << "\n";
}
