"""TASK 1 (implicit design): choose the 24 definitional rows / 24 pivot unknowns, check the rank-24
structure (bound row included), solve the 24x24 system at 50 digits, validate margins, emit Lean tables."""
import pickle, json, os, sys, time
sys.set_int_max_str_digits(0)
from fractions import Fraction as Fr
import numpy as np, scipy.linalg
from mpmath import mp, mpf, matrix as mpmat, lu_solve, sqrt as msqrt, nstr, eigsy
mp.dps=50
here=os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0,here)
T0=time.time()
def log(*a): print(f"[{time.time()-T0:7.1f}s]",*a,flush=True)
exec(open(os.path.join(here,'task1_exact.py')).read().split("# ---------------- antiprism data in K ----------------")[0])   # K, BASIS, US
D=pickle.load(open(os.path.join(here,'task1_rows_polybasis.pkl'),'rb'))
rows=[({p:K(v) for p,v in row.items()},K(rhs)) for row,rhs in D['rows']]; names=D['names']; idx=D['idx']
x0=[Fr(s) for s in D['x0']]; nx=len(x0)
# row labels: 0 bound; 1..8 pair (A val, A der, D val, D der, N val, N der, F val, F der); 9.. triangles (val,du,dv,dt) x 5
types=['FFA','FDN','FNA','DAA','NNA']
lab=['bound']+[f"pair{c}_{w}" for c in 'ADNF' for w in ('val','der')]+[f"tri{t}_{w}" for t in types for w in ('val','du','dv','dt')]
# drop duplicate gradient rows of the symmetric types: FFA du=dv (drop dv), DAA dv=dt (drop dt), NNA du=dv (drop dv)
drop_dup={lab.index('triFFA_dv'),lab.index('triDAA_dt'),lab.index('triNNA_dv')}
keep=[q for q in range(len(rows)) if q not in drop_dup]
J=np.zeros((len(keep),nx)); b=np.zeros(len(keep)); Jm=mpmat(len(keep),nx); bm=mpmat(len(keep),1)
for a,q in enumerate(keep):
    row,rhs=rows[q]; bm[a]=rhs.num(US); b[a]=float(bm[a])
    for p,v in row.items(): Jm[a,p]=v.num(US); J[a,p]=float(Jm[a,p])
# duplicates really duplicates?
for (i,j) in [(lab.index('triFFA_du'),lab.index('triFFA_dv')),(lab.index('triDAA_dv'),lab.index('triDAA_dt')),(lab.index('triNNA_du'),lab.index('triNNA_dv'))]:
    d=max(abs(float((rows[i][0][p]-rows[j][0][p]).num(US))) if p in rows[j][0] else abs(float(rows[i][0][p].num(US))) for p in rows[i][0])
    log(f"duplicate check {lab[i]} vs {lab[j]}: max diff {d:.1e}")
S=np.linalg.svd(J,compute_uv=False); rank=int((S>1e-9*S[0]).sum())
log(f"{len(keep)} rows after removing duplicates; numerical rank {rank}; sv tail {np.array2string(S[rank-2:rank+2],precision=2)}")
# left null vectors of [J|b]: supports
Jb=np.hstack([J,b[:,None]])
U_,S_,Vt=np.linalg.svd(Jb.T,full_matrices=True)
null=U_[:,rank:]   # left null space of Jb (columns)
log("left-null dim of [J|b]:",null.shape[1])
for c in range(null.shape[1]):
    v=null[:,c]; v=v/np.abs(v).max()
    supp=[(lab[keep[a]],round(float(v[a]),4)) for a in range(len(keep)) if abs(v[a])>1e-6]
    log(f"  null vector {c}: {supp}")
# pivot selection: exclude a0,a1,lam (cols 0,1,2); force bound row in
cand=[p for p in range(nx) if p>=3]
Vt_r=np.linalg.svd(J)[2][:rank]
Q_,R_,pivc=scipy.linalg.qr(Vt_r[:,cand],pivoting=True); cols=sorted(cand[i] for i in pivc[:rank])
log("pivot unknowns (a0,a1,lam excluded):",[names[p] for p in cols])
Jc=J[:,cols]
# row selection with bound forced: QR on the remaining rows' restriction to the pivot columns after projecting out the bound row
bidx=keep.index(0)
others=[a for a in range(len(keep)) if a!=bidx]
Q2,R2,pivr=scipy.linalg.qr(Jc[others].T,pivoting=True)
# choose rank-1 rows among others greedily but keep bound
rsel=[bidx]+[others[i] for i in pivr[:rank-1]]
Jp=Jc[rsel]; c=np.linalg.cond(Jp); log(f"selected 24 rows: cond {c:.3e}")
dropped=[lab[keep[a]] for a in range(len(keep)) if a not in rsel]; log("dropped rows:",dropped)
# also try the alternative: QR over all rows without forcing, to compare conditioning
Q3_,R3_,pivr3=scipy.linalg.qr(Jc.T,pivoting=True); log(f"unforced best cond {np.linalg.cond(Jc[sorted(pivr3[:rank])]):.3e}, would drop {[lab[keep[a]] for a in range(len(keep)) if a not in pivr3[:rank]]}")
rsel=sorted(rsel)
# fixed rationals (13 digits) for all non-pivot unknowns
free=[p for p in range(nx) if p not in cols]
xr={p:Fr(str(np.format_float_positional(float(x0[p]),precision=13,unique=False,trim='-'))) for p in free}
# 50-digit solve of the 24x24 system  M p = c  with c = rhs - J_free x_free
M=mpmat(rank,rank); cvec=mpmat(rank,1)
for a,q in enumerate(rsel):
    cvec[a]=bm[q]-sum(Jm[q,p]*mpf(xr[p].numerator)/xr[p].denominator for p in free)
    for j,p in enumerate(cols): M[a,j]=Jm[q,p]
psol=lu_solve(M,cvec)
xs={p:(psol[cols.index(p)] if p in cols else mpf(xr[p].numerator)/xr[p].denominator) for p in range(nx)}
res=[abs(sum(Jm[a,p]*xs[p] for p in range(nx))-bm[a]) for a in range(len(keep))]
log("max residual over ALL 26 rows at the 50-digit solution:",nstr(max(res),4),"(definitional rows:",nstr(max(res[a] for a in rsel),3),")")
log("max |p - x0| over pivots:",nstr(max(abs(xs[p]-mpf(x0[p].numerator)/x0[p].denominator) for p in cols),4))
# approximate inverse quality (for Task 1a): N = float inverse, ||I - N M||_inf
Mf=np.array([[float(M[i,j]) for j in range(rank)] for i in range(rank)]); Nf=np.linalg.inv(Mf)
E_=np.eye(rank)-Nf@Mf; log(f"||I - N M||_inf with double-precision N: {np.abs(E_).sum(1).max():.2e};  ||N||_inf = {np.abs(Nf).sum(1).max():.3e}; ||M||_inf={np.abs(Mf).sum(1).max():.3e}")
# ---- margins at the solution ----
KMAX=5; nk={k:9-k for k in range(KMAX+1)}
Hs={k:mpmat(nk[k]-1,nk[k]-1) for k in range(KMAX+1)}
for p,(k,i,j) in enumerate(idx): Hs[k][i,j]=xs[3+p]; Hs[k][j,i]=xs[3+p]
for k in range(KMAX+1):
    ev=eigsy(Hs[k])[0]; log(f"H'_{k} eigenvalues: min {nstr(min(ev),5)} max {nstr(max(ev),5)}")
# rebuild F numerically and check pair/triangle margins (as in task1_emit)
kv=json.load(open(os.path.join(here,'kernel_vectors_exact.json')))
import sympy as sp
uu_=sp.symbols('u')
def Bnum(k):
    v=[sp.sympify(s) for s in kv[str(k)]]; n=len(v); p0=next(i for i in range(n) if v[i]!=0); colsB=[]
    for i in range(n):
        if i==p0: continue
        num_,den_=sp.fraction(sp.together(v[i])); col=[mpf(0)]*n
        col[i]=mpf(str(sp.N(den_.subs(uu_,sp.Rational(str(US))),60))); col[p0]=-mpf(str(sp.N(num_.subs(uu_,sp.Rational(str(US))),60)))
        colsB.append(col)
    return colsB
Bn={k:Bnum(k) for k in range(KMAX+1)}
from bv import Sk as Sk_num
Fmat={}
for k in range(KMAX+1):
    n=nk[k]; m=n-1; Bk=mpmat(n,m)
    for a in range(m):
        for i in range(n): Bk[i,a]=Bn[k][a][i]
    Fmat[k]=Bk*Hs[k]*Bk.T
def Fnum(x,y,z):
    tot=mpf(0)
    for k in range(KMAX+1):
        S3=Sk_num(k,8,float(x),float(y),float(z))
        tot+=sum(Fmat[k][i,j]*mpf(S3[i,j]) for i in range(nk[k]) for j in range(nk[k]))
    return tot
a0n,a1n,lamn=xs[0],xs[1],xs[2]
w_=msqrt(2); r_=msqrt(1-US); y_=msqrt(2+2*US-w_*(1-US)); z_=msqrt(2+2*US+w_*(1-US)); E=(4*w_+2)/r_+8/y_+8/z_
log("bound - E(u*) =",nstr((64*a0n-8*(a0n+a1n)-8*Fnum(1,1,1))/2-E,5))
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
# ---- save design ----
design=dict(cols=cols,pivot_names=[names[p] for p in cols],rsel_labels=[lab[keep[a]] for a in rsel],dropped=dropped,
            free={names[p]:str(xr[p]) for p in free},pivots_num={names[p]:nstr(xs[p],40) for p in cols},
            idx=idx,names=names,cond=float(c))
json.dump(design,open(os.path.join(here,'task1_design.json'),'w'),indent=1)
log("saved task1_design.json")
