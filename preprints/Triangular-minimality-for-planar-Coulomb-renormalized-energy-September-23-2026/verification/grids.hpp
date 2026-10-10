#pragma once

#include "core.hpp"
#include <array>
#include <chrono>
#include <iostream>
#include <string>
#include <vector>

// Exact fixed-point interval certificate for the scalar inequalities.
// Addition of interval endpoints is exact, so parallel d-row evaluation and
// sequential row reduction preserve the endpoint results.
inline void coarse_list(const std::vector<IV>& values) {
    std::cout << '[';
    for (std::size_t i = 0; i < values.size(); ++i) {
        if (i) std::cout << ", ";
        std::cout << '(' << floor_div(values[i].u * 10000000, Q)
                  << ", " << ceil_div(values[i].v * 10000000, Q) << ')';
    }
    std::cout << ']' << std::endl;
}

struct CertificateTimer {
    std::string label;
    std::chrono::steady_clock::time_point start;
    explicit CertificateTimer(std::string name)
        : label(std::move(name)), start(std::chrono::steady_clock::now()) {
        std::cerr << "BEGIN " << label << std::endl;
    }
    ~CertificateTimer() {
        const double elapsed = std::chrono::duration<double>(
            std::chrono::steady_clock::now() - start).count();
        std::cerr << "TIMING " << label << ' ' << elapsed << " seconds" << std::endl;
    }
};

inline IV G(const IV& d, const IV& s) {
    const IV t2 = d*d+s*s;
    const IV t = t2.sqrt();
    const auto fe = lookup(t, false);
    IV f = fe[0];
    const IV e = fe[1];
    const IV A = d/t2;
    const IV B = -s*s/(d*t2);
    f = f-lambda_*t2/2-mu;
    return A*f+B*e;
}

inline std::array<IV,5> G(const IV& d, const IV& s, bool full) {
    (void)full; // This overload always returns derivatives.
    const IV t2 = d*d+s*s;
    const IV t = t2.sqrt();
    const auto values = lookup(t, true);
    IV f=values[0], fr=values[1], frr=values[2];
    const IV e=values[3], er=values[4], err=values[5];
    const IV A=d/t2, B=-s*s/(d*t2);
    f=f-lambda_*t2/2-mu;
    fr=fr-lambda_*t;
    frr=frr-lambda_;
    const IV rdt=d/t, rst=s/t;
    const IV rtdd=(one-rdt*rdt)/t, rtss=(one-rst*rst)/t;
    const IV Ad=(one-2*d*d/t2)/t2, Bd=Ad+one/(d*d);
    const IV As=-2*A*s/t2, Bs=As;
    const IV t2_cubed=pow(t2,3);
    const IV Add=2*d*(d*d-3*s*s)/t2_cubed, Bdd=Add-2/pow(d,3);
    const IV Ass=-2*d/pow(t2,2)+8*d*s*s/t2_cubed, Bss=Ass;
    return {{
        A*f+B*e,
        Ad*f+A*fr*rdt+Bd*e+B*er*rdt,
        As*f+A*fr*rst+Bs*e+B*er*rst,
        Add*f+2*Ad*fr*rdt+A*(frr*rdt*rdt+fr*rtdd)
            +Bdd*e+2*Bd*er*rdt+B*(err*rdt*rdt+er*rtdd),
        Ass*f+2*As*fr*rst+A*(frr*rst*rst+fr*rtss)
            +Bss*e+2*Bs*er*rst+B*(err*rst*rst+er*rtss)
    }};
}

inline void calcLam() {
    const IV s0=rat(".01");
    constexpr int N=45000;
    const IV H=(R/2-s0)/N;
    const auto idx_it=std::find(orig.begin(),orig.end(),2);
    const auto idx2_it=std::find(orig.begin(),orig.end(),3);
    assert(idx_it!=orig.end() && idx2_it!=orig.end());
    const auto idx=idx_it-orig.begin(), idx2=idx2_it-orig.begin();
    assert(ts[idx].u==p.u && ts[idx].v==p.v);
    assert(ts[idx2].u==R.u);
    IV fp=pts[idx][0]+eps, fpr=pts[idx][1]+eps, ep=pts[idx][3]+eps;
    IV fr=pts[idx2][0]+eps, er=pts[idx2][3]+eps;
    (void)ep; // Retain the inflated endpoint enclosure.
    IV B=(p/(R/2))*(fr-fp)-(R/2)/p*er;
    IV cf=s0/2-pow(s0,3)/(24*p*p);
    const IV erl=pow(s0,5)/(80*pow(p,4));
    cf=cf+IV(0,erl.v);
    const int im=std::max(0,int(std::lower_bound(VIL.begin(),VIL.end(),p.u)-VIL.begin())-1);
    const cpp_int radial_upper=(p*p+s0*s0).sqrt().v;
    const int ix=std::min(int(cels.size()),int(std::upper_bound(UIL.begin(),UIL.end(),radial_upper)-UIL.begin()));
    IV sp=zero;
    bool have_sp=false;
    for (int i=im; i<ix; ++i) {
        const IV item=cels[i][2]+eps;
        sp=have_sp ? sp.hull(item) : item;
        have_sp=true;
    }
    assert(have_sp);
    const IV quo=IV(p.u,p.v)/pow((p*p+s0*s0).sqrt()+p,2);
    const IV root=one/(4*p);
    const IV coeff=IV(quo.u,root.v)*(rat(1,6)*pow(s0,3));
    B=B+fpr*cf+sp*coeff;
    IV Facc=zero,Eacc=zero;
    for (int i=0; i<N; ++i) {
        const IV sh=s0+H*(i+rat(1,2));
        const auto values=lookup((p*p+sh*sh).sqrt(),false);
        Facc=Facc+H*(p*(values[0]-fp)/(sh*sh));
    }
    const IV H2=(R/2)/N;
    for (int i=0; i<N; ++i) {
        const IV sh=H2*(i+rat(1,2));
        const IV e=lookup((p*p+sh*sh).sqrt(),false)[1];
        Eacc=Eacc+H2*e/p;
    }
    const int begin=std::max(0,int(std::lower_bound(VIL.begin(),VIL.end(),p.u)-VIL.begin())-1);
    const int end=std::min(int(cels.size()),int(std::upper_bound(UIL.begin(),UIL.end(),R.v)-UIL.begin()));
    assert(begin<end);
    std::array<cpp_int,6> bnd;
    for (int k=0; k<6; ++k) {
        bnd[k]=0;
        for (int i=begin; i<end; ++i) {
            const cpp_int val=ceil_div((cels[i][k]+eps).abs().v,Q);
            if (val>bnd[k]) bnd[k]=val;
        }
    }
    const IV C=rat(std::max(cpp_int(1),bnd[1]));
    const IV Cp=rat(std::max(cpp_int(1),bnd[2]));
    const IV Ce0=rat(std::max(cpp_int(1),bnd[4]));
    const IV Ce1=rat(std::max(cpp_int(1),bnd[5]));
    const IV vpp=Cp/p+8*C/(s0*s0);
    const IV vepp=Ce1/p+Ce0/(p*p);
    const IV evipp=((R/2-s0)*H*H/24*vpp).abs();
    const IV eppp=((R/2)*H2*H2/24*vepp).abs();
    Facc=Facc+IV(-evipp.v,evipp.v);
    Eacc=Eacc+IV(-eppp.v,eppp.v);
    B=B+Facc+Eacc;
    lambda_=B/(p*(R/2));
    mu=fr-rat(1,3)*er-lambda_*R*R/2;
}

inline void calcK() {
    const int m=nsamp(zero,R/2,rat(".0001"));
    const IV h=(R/2)/m;
    const int mh=nsamp(zero,R/2,rat(".0002"));
    const IV H=(R/2)/mh;
    IV ss=zero;
    for (int i=0; i<mh; ++i) {
        const IV low=i*H,up=(i+1)*H;
        const IV d=G(p,IV(low.u,up.v),true)[4];
        ss=ss.hull(d);
    }
    IV kc=zero;
    for (int i=0; i<m; ++i) {
        const IV value=G(p,(i+rat(1,2))*h);
        kc=kc+h*value;
    }
    const IV er=pow(h,2)*(R/2)*ss.abs()/24;
    K=2*(kc+IV(-er.v,er.v));
}

inline std::vector<IV> grid_seq(const IV& a0,const IV& b0,const IV& h) {
    const int m=nsamp(a0,b0,h);
    std::vector<IV> result;
    result.reserve(m+1);
    for (int i=0;i<m;++i) result.push_back(a0+(b0-a0)*i/m);
    result.push_back(b0);
    return result;
}

inline void append_grid_seq(std::vector<IV>& dest,const IV& a0,const IV& b0,
                            const IV& h,bool include_last) {
    auto part=grid_seq(a0,b0,h);
    if (!include_last) part.pop_back();
    dest.insert(dest.end(),part.begin(),part.end());
}

inline void inside_hess(const std::string& dxmax="0.00003",const std::string& sxmax="0.00003") {
    const IV dl=rat(".52528"),du=rat(".54930"),sl=rat(".29420"),su=rat(".32621");
    const auto dseq=grid_seq(dl,du,rat(dxmax));
    std::vector<IV> xseq;
    append_grid_seq(xseq,zero,sl,rat(sxmax),false);
    append_grid_seq(xseq,sl,su,rat(sxmax),true);
    const int nd=int(dseq.size())-1,ns=int(xseq.size())-1;
    std::cerr << "MESH inside_hess " << nd << " x " << ns << std::endl;
    struct HessRow {
        IV dgl,glx,glxx,det;
        bool initialized=false;
        std::uint64_t failures=0;
    };
    std::vector<HessRow> rows(nd);
    #pragma omp parallel for schedule(dynamic,1)
    for (int j=0;j<nd;++j) {
        const IV d(dseq[j].u,dseq[j+1].v);
        IV dd=zero;
        auto& row=rows[j];
        for (int i=0;i<ns;++i) {
            const IV& lsx=xseq[i];
            const IV& usx=xseq[i+1];
            const IV sx(lsx.u,usx.v),h=usx-lsx;
            const auto values=G(d,sx,true);
            const IV& xdi=values[1];
            const IV& xxi=values[2];
            const IV& sd2=values[3];
            const IV ddcc=dd+IV(0,h.v)*sd2;
            dd=dd+h*sd2;
            if (usx.u>=sl.u) {
                const IV det=ddcc*xxi-xdi*xdi;
                if (!row.initialized) {
                    row.dgl=ddcc; row.glx=xdi; row.glxx=xxi; row.det=det;
                    row.initialized=true;
                } else {
                    row.dgl=row.dgl.hull(ddcc);
                    row.glx=row.glx.hull(xdi);
                    row.glxx=row.glxx.hull(xxi);
                    row.det=row.det.hull(det);
                }
                if (ddcc.u<=0 || xxi.u<=0 || det.u<=0) ++row.failures;
            }
        }
        assert(row.failures==0);
    }
    IV dgl=zero,glx=zero,glxx=zero,min_det=zero;
    bool initialized=false;
    for (const auto& row:rows) {
        assert(row.initialized && row.failures==0);
        if (!initialized) {
            dgl=row.dgl; glx=row.glx; glxx=row.glxx; min_det=row.det;
            initialized=true;
        } else {
            dgl=dgl.hull(row.dgl);
            glx=glx.hull(row.glx);
            glxx=glxx.hull(row.glxx);
            min_det=min_det.hull(row.det);
        }
    }
    assert(initialized);
    std::cout << "hess hulls" << std::endl;
    coarse_list({dgl,glx,glxx,min_det});
}

inline std::vector<IV> bdsup() {
    const IV H=rat("0.0008");
    const IV dlo=rat(".28209"),dup=rat(".697"),shi=rat(".65");
    const int nd=nsamp(dlo,dup,H),ns=nsamp(zero,shi,H);
    const IV hd=(dup-dlo)/nd,hs=shi/ns;
    std::cerr << "MESH bdsup " << nd << " x " << ns << std::endl;
    std::vector<std::array<IV,5>> rows(nd);
    #pragma omp parallel for schedule(dynamic,1)
    for (int j=0;j<nd;++j) {
        auto& row=rows[j];
        for (auto& value:row) value=zero;
        const IV lo=dlo+hd*j;
        const IV d(lo.u,(lo+hd).v);
        for (int i=0;i<ns;++i) {
            const IV slo=hs*i;
            const IV s(slo.u,(slo+hs).v);
            const auto ranges=G(d,s,true);
            for (int k=0;k<5;++k) row[k]=row[k].hull(ranges[k]);
        }
    }
    std::vector<IV> b(5,zero);
    for (const auto& row:rows)
        for (int k=0;k<5;++k) b[k]=b[k].hull(row[k]);
    return b;
}

inline void global_grid(const std::string& stepd,const std::string& stepx,
                        const std::vector<IV>& supplied_bounds) {
    assert(supplied_bounds.size()==5);
    std::vector<IV> b;
    for (const auto& value:supplied_bounds) b.push_back(value.abs());
    const IV chi=b[4],Gdd=b[3],Gs=b[2],Gd=b[1];
    const IV Bmin=rat(".28209"),Tmax=rat(".697"),Smax=rat(".65");
    const IV dl=rat(".52528"),du=rat(".54930"),sl=rat(".29420"),su=rat(".32621");
    std::vector<IV> dseq,sseq;
    append_grid_seq(dseq,Bmin,dl,rat(stepd),false);
    append_grid_seq(dseq,dl,du,rat(stepd),false);
    append_grid_seq(dseq,du,Tmax,rat(stepd),true);
    append_grid_seq(sseq,zero,sl,rat(stepx),false);
    append_grid_seq(sseq,sl,su,rat(stepx),false);
    append_grid_seq(sseq,su,Smax,rat(stepx),true);
    const int nd=int(dseq.size()),ns=int(sseq.size())-1;
    std::cerr << "MESH global_grid " << nd << " x " << ns << std::endl;
    cpp_int hmax=0,dmax=0;
    for (int i=0;i<ns;++i) {
        const cpp_int width=sseq[i+1].v-sseq[i].u;
        if (width>hmax) hmax=width;
    }
    for (int i=0;i<nd-1;++i) {
        const cpp_int width=dseq[i+1].v-dseq[i].u;
        if (width>dmax) dmax=width;
    }
    const IV H(0,hmax),Dh(0,dmax);
    const IV er0=2*Smax*pow(H,2)*chi/24;
    const IV eri=2*(pow(Dh,2)*Smax*Gdd+pow(H,2)*Gs)/8;
    const IV factor=er0+IV(0,eri.v);
    const IV er_drop=Smax*(H/4*Gs+Dh/2*Gd);
    struct GlobalRow { IV gmin,drop; };
    std::vector<GlobalRow> rows(nd);
    #pragma omp parallel for schedule(dynamic,1)
    for (int j=0;j<nd;++j) {
        const IV& d=dseq[j];
        const bool needall=d.u<=dl.v || d.v>=du.u;
        IV g=zero,drop=zero,gmin=10*one;
        if ((-K).u<gmin.u) gmin=-K;
        for (int i=0;i<ns;++i) {
            const IV& lo=sseq[i];
            const IV& hi=sseq[i+1];
            const IV h=hi-lo;
            const IV gv=h*G(d,(lo+hi)/2);
            g=g+gv;
            const IV minus_gv_h=-gv/h;
            const IV clipped(std::max(cpp_int(0),minus_gv_h.u),
                             std::max(cpp_int(0),minus_gv_h.v));
            drop=drop+h*clipped;
            if (!(needall || hi.v<=sl.v || hi.u>=su.u)) continue;
            const IV value=2*g-K;
            if (value.u<gmin.u) gmin=value;
        }
        rows[j]={gmin,drop};
    }
    IV gmin=10*one,drneg=-10*one;
    for (const auto& row:rows) {
        if (row.gmin.u<gmin.u) gmin=row.gmin;
        if (row.drop.v>drneg.v) drneg=row.drop;
    }
    std::cout << "gmin,drneg,factor,er_drop,gmin-factor,drneg+er_drop+K" << std::endl;
    coarse_list({gmin,drneg,factor,er_drop,gmin-factor,drneg+er_drop+K});
    assert((gmin-factor).u>0 && (drneg+er_drop+K).v<0);
}

inline void run_certificate() {
    #ifdef NDEBUG
    #error "The certificate requires active assertions; do not compile with NDEBUG."
    #endif
    CertificateTimer total_timer("full certificate");
    { CertificateTimer timer("init_core including core_test"); init_core(); }
    { CertificateTimer timer("calcLam"); calcLam(); }
    { CertificateTimer timer("calcK"); calcK(); }
    assert(lambda_.u>rat("-6.731").v && lambda_.v<rat("-6.729").u && K.v<0);
    assert((pts.back()[0]+eps-lambda_*l*l/2-mu).u>0 && (-pi*bcons-lambda_/2).u>0);
    std::cout << "lambda,mu,K,bcon,f0(l),slope,f(l)" << std::endl;
    coarse_list({lambda_,mu,K,bcons,pts.back()[0]+eps,
                 -pi*bcons-lambda_/2,pts.back()[0]+eps-lambda_*l*l/2-mu});
    std::vector<IV> bs;
    { CertificateTimer timer("bdsup"); bs=bdsup(); }
    std::cout << "bounds:" << std::endl;
    coarse_list(bs);
    { CertificateTimer timer("global_grid"); global_grid(".00019",".00018",bs); }
    { CertificateTimer timer("inside_hess"); inside_hess(".00004",".00008"); }
    std::cout << "OK" << std::endl;
}
