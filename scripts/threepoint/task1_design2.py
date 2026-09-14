"""Design, stage 2: rescale the inverse-free basis columns by rational constants (norm ~ 1 at u*),
re-run pivot/row selection, margins, conditioning; structural rank checks; save design."""
import pickle, json, os, sys, time
from fractions import Fraction as Fr
import numpy as np, scipy.linalg
from mpmath import mp, mpf, matrix as mpmat, lu_solve, sqrt as msqrt, nstr, eigsy, mpmathify
mp.dps=50
here=os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0,here)
T0=time.time()
def log(*a): print(f"[{time.time()-T0:7.1f}s]",*a,flush=True)
exec(open(os.path.join(here,'task1_exact.py')).read().split("# ---------------- antiprism data in K ----------------")[0])
D=pickle.load(open(os.path.join(here,'task1_rows_polybasis.pkl'),'rb'))
rows=[({p:K(v) for p,v in row.items()},K(rhs)) for row,rhs in D['rows']]; names=D['names']; idx=D['idx']
x0=[Fr(s) for s in D['x0']]; nx=len(x0)
types=['FFA','FDN','FNA','DAA','NNA']
lab=['bound']+[f"pair{c}_{w}" for c in 'ADNF' for w in ('val','der')]+[f"tri{t}_{w}" for t in types for w in ('val','du','dv','dt')]
drop_dup={lab.index('triFFA_dv'),lab.index('triDAA_dt'),lab.index('triNNA_dv')}
keep=[q for q in range(len(rows)) if q not in drop_dup]
Jm=mpmat(len(keep),nx); bm=mpmat(len(keep),1)
for a,q in enumerate(keep):
    row,rhs=rows[q]; bm[a]=rhs.num(US)
    for p,v in row.items(): Jm[a,p]=v.num(US)
# ---- basis column scaling: column a of B_k has entries d_i (at i) and -n_i (at p0); norm at u* ----
kv=json.load(open(os.path.join(here,'kernel_vectors_exact.json')))
import sympy as sp
uu_=sp.symbols('u'); KMAX=5; nk={k:9-k for k in range(KMAX+1)}
def colinfo(k):
    v=[sp.sympify(s) for s in kv[str(k)]]; n=len(v); p0=next(i for i in range(n) if v[i]!=0); out=[]
    for i in range(n):
        if i==p0: continue
        num_,den_=sp.fraction(sp.together(v[i]))
        dn=mpf(str(sp.N(den_.subs(uu_,sp.Rational(str(US))),60))); nm=mpf(str(sp.N(num_.subs(uu_,sp.Rational(str(US))),60)))
        out.append(dict(i=i,p0=p0,num=sp.Poly(sp.expand(num_),uu_),den=sp.Poly(sp.expand(den_),uu_),norm=msqrt(dn*dn+nm*nm),dn=dn,nm=nm))
    return out
CI={k:colinfo(k) for k in range(KMAX+1)}
# rational scale: 1/norm rounded to 4 significant digits (power-of-two friendly not needed)
def rat_scale(x):
    from decimal import Decimal
    s=mpf(1)/x; e=int(mp.floor(mp.log10(s))); q=Fr(int(mp.nint(s*mpf(10)**(3-e))),10**(3-e)) if e<=3 else Fr(int(mp.nint(s*mpf(10)**(3-e))),1)*Fr(10**(e-3))
    return q
SC={k:[rat_scale(c['norm']) for c in CI[k]] for k in range(KMAX+1)}
for k in range(KMAX+1): log(f"k={k} column norms {[nstr(c['norm'],4) for c in CI[k]]} scales {[str(s) for s in SC[k]]}")
# unknown H'[a,b] in the scaled basis: Bs = B diag(sc)  =>  H'_scaled = diag(1/sc) H' diag(1/sc); row coefficient for H'_scaled[a,b] = coef * sc_a sc_b
# (x_new = H'_s[a,b] = H'[a,b]/(sc_a sc_b); the row term coef*H'[a,b] = coef*sc_a*sc_b*x_new)
scale_col=np.ones(nx,dtype=object); scale_col[0]=scale_col[1]=scale_col[2]=Fr(1)
for p,(k,i,j) in enumerate(idx): scale_col[3+p]=SC[k][i]*SC[k][j]
Js=mpmat(len(keep),nx)
for a in range(len(keep)):
    for p in range(nx): Js[a,p]=Jm[a,p]*mpf(scale_col[p].numerator)/scale_col[p].denominator
x0s=[x0[p]/scale_col[p] for p in range(nx)]
J=np.array([[float(Js[a,p]) for p in range(nx)] for a in range(len(keep))]); b=np.array([float(bm[a]) for a in range(len(keep))])
S=np.linalg.svd(J,compute_uv=False); rank=int((S>1e-9*S[0]).sum()); log(f"rank {rank}, sv range {S[0]:.2e} .. {S[rank-1]:.2e} | {S[rank]:.1e}")
# structural checks
vals=[keep.index(lab.index(l)) for l in lab if l.endswith('_val')]; bidx=keep.index(0)
def rk(rs): return np.linalg.matrix_rank(np.hstack([J[rs],b[rs,None]]),tol=1e-9)
log(f"rank of the 9 value rows: {rk(vals)}; with the bound row: {rk([bidx]+vals)}  (expect 9, 9: bound ∈ span(values) incl. constants)")
ders=[a for a in range(len(keep)) if a not in vals and a!=bidx]
log(f"rank of the 16 derivative rows: {rk(ders)}; values+derivatives: {rk(vals+ders)} (expect 16, 24: Euler mixes both)")
# pivot selection: exclude a0,a1,lam
cand=[p for p in range(nx) if p>=3]
Vt_r=np.linalg.svd(J)[2][:rank]
Q_,R_,pivc=scipy.linalg.qr(Vt_r[:,cand],pivoting=True); cols=sorted(cand[i] for i in pivc[:rank])
log("pivot unknowns:",[names[p] for p in cols])
Jc=J[:,cols]; others=[a for a in range(len(keep)) if a!=bidx]
Q2,R2,pivr=scipy.linalg.qr(Jc[others].T,pivoting=True); rsel=sorted([bidx]+[others[i] for i in pivr[:rank-1]])
Jp=Jc[rsel]; cnd=np.linalg.cond(Jp); log(f"selected rows cond {cnd:.3e}; dropped {[lab[keep[a]] for a in range(len(keep)) if a not in rsel]}")
# also with a0,a1,lam allowed, for comparison
Qa,Ra,pa=scipy.linalg.qr(Vt_r,pivoting=True); colsA=sorted(pa[:rank]); log(f"(for comparison, a0/a1/lam allowed: cond {np.linalg.cond(J[np.ix_(rsel,colsA)]):.2e}, pivots incl {[names[p] for p in colsA if p<3]})")
free=[p for p in range(nx) if p not in cols]
xr={p:Fr(str(np.format_float_positional(float(x0s[p]),precision=13,unique=False,trim='-'))) for p in free}
M=mpmat(rank,rank); cvec=mpmat(rank,1)
for a,q in enumerate(rsel):
    cvec[a]=bm[q]-sum(Js[q,p]*mpf(xr[p].numerator)/xr[p].denominator for p in free)
    for j,p in enumerate(cols): M[a,j]=Js[q,p]
psol=lu_solve(M,cvec)
xs={p:(psol[cols.index(p)] if p in cols else mpf(xr[p].numerator)/xr[p].denominator) for p in range(nx)}
res=[abs(sum(Js[a,p]*xs[p] for p in range(nx))-bm[a]) for a in range(len(keep))]
log("max residual over ALL 26 rows:",nstr(max(res),4),"; max |p - x0| over pivots:",nstr(max(abs(xs[p]-mpf(x0s[p].numerator)/x0s[p].denominator) for p in cols),4))
Mf=np.array([[float(M[i,j]) for j in range(rank)] for i in range(rank)]); Nf=np.linalg.inv(Mf)
log(f"||I - N M||_inf (double N): {np.abs(np.eye(rank)-Nf@Mf).sum(1).max():.2e};  ||N||_inf={np.abs(Nf).sum(1).max():.3e}; ||M||_inf={np.abs(Mf).sum(1).max():.3e}; max|c|={max(abs(float(cvec[i])) for i in range(rank)):.2e}")
# pivot values: 20-digit rationals, and how far they are from the true solution
phat={p:Fr(nstr(xs[p],22)) for p in cols}
log("max |p - phat(22 digits)|:",nstr(max(abs(xs[p]-mpf(phat[p].numerator)/phat[p].denominator) for p in cols),3))
Hs={k:mpmat(nk[k]-1,nk[k]-1) for k in range(KMAX+1)}
for p,(k,i,j) in enumerate(idx): Hs[k][i,j]=xs[3+p]; Hs[k][j,i]=xs[3+p]
for k in range(KMAX+1):
    ev=eigsy(Hs[k])[0]; log(f"H'_{k} (scaled basis) eigenvalues: min {nstr(min(ev),5)} max {nstr(max(ev),5)}")
# margins with scaled basis
Bn={}
for k in range(KMAX+1):
    n=nk[k]; m=n-1; Bk=mpmat(n,m)
    for a,c in enumerate(CI[k]):
        s=mpf(SC[k][a].numerator)/SC[k][a].denominator; Bk[c['i'],a]=c['dn']*s; Bk[c['p0'],a]=-c['nm']*s
    Bn[k]=Bk
from bv import Sk as Sk_num
Fmat={k:Bn[k]*Hs[k]*Bn[k].T for k in range(KMAX+1)}
def Fnum(x,y,z):
    tot=mpf(0)
    for k in range(KMAX+1):
        S3=Sk_num(k,8,float(x),float(y),float(z)); tot+=sum(Fmat[k][i,j]*mpf(S3[i,j]) for i in range(nk[k]) for j in range(nk[k]))
    return tot
a0n,a1n,lamn=xs[0],xs[1],xs[2]
w_=msqrt(2); r_=msqrt(1-US); y_=msqrt(2+2*US-w_*(1-US)); z_=msqrt(2+2*US+w_*(1-US)); E=(4*w_+2)/r_+8/y_+8/z_
log("bound - E(u*) =",nstr((64*a0n-8*(a0n+a1n)-8*Fnum(1,1,1))/2-E,5), " a0,a1,lam =",str(xr[0]),str(xr[1]),str(xr[2]))
def P(s): t=1-s*s/2; return (1-18*lamn)-s*(a0n+a1n*t+3*Fnum(1,t,t))
pts=[mpf(24)/25+(2-mpf(24)/25)*i/1200 for i in range(1201)]; pv=[P(s) for s in pts]
log("pair polynomial min on 1201 pts:",nstr(min(pv),5)," at chords:",[nstr(P(s),3) for s in (w_*r_,2*r_,y_,z_)])
def h(t): return 1/msqrt(2-2*t)
g=[mpf(-1)+mpf('1.5373')*i/30 for i in range(31)]; tv=[]
for a_ in g:
    for b_ in g:
        if b_<a_: continue
        for c_ in g:
            if c_<b_ or 1+2*a_*b_*c_-a_*a_-b_*b_-c_*c_<0: continue
            tv.append(lamn*(h(a_)+h(b_)+h(c_))-Fnum(a_,b_,c_))
log(f"triangle slack min on {len(tv)} pts:",nstr(min(tv),5))
design=dict(cols=cols,pivot_names=[names[p] for p in cols],rsel_labels=[lab[keep[a]] for a in rsel],
            dropped=[lab[keep[a]] for a in range(len(keep)) if a not in rsel],
            free={names[p]:str(xr[p]) for p in free},pivots_num={names[p]:str(phat[p]) for p in cols},pivots_50={names[p]:nstr(xs[p],50) for p in cols},
            scales={str(k):[str(s) for s in SC[k]] for k in range(KMAX+1)},
            basis={str(k):[dict(i=c['i'],p0=c['p0'],num=str(c['num'].as_expr()),den=str(c['den'].as_expr())) for c in CI[k]] for k in range(KMAX+1)},
            idx=idx,names=names,cond=float(cnd),normN=float(np.abs(Nf).sum(1).max()),normM=float(np.abs(Mf).sum(1).max()),
            Hmin={str(k):nstr(min(eigsy(Hs[k])[0]),6) for k in range(KMAX+1)})
json.dump(design,open(os.path.join(here,'task1_design.json'),'w'),indent=1)
log("saved task1_design.json")
