"""TASK 1, stage 3: exact LDL^T over K, assemble certData, validate all margins at 50 digits, render Lean."""
import pickle, json, os, sys, time, itertools
from fractions import Fraction as Fr
here=os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0,here)
exec(open(os.path.join(here,'task1_exact.py')).read().split("# ---------------- antiprism data in K ----------------")[0])   # K, BASIS, inv, US, log
from mpmath import mp, mpf, matrix as mpmat, eigsy, sqrt as msqrt, nstr
S=pickle.load(open(os.path.join(here,'task1_exact_solution.pkl'),'rb'))
cols,free,xr,X,names,idx=S['cols'],S['free'],S['xr'],S['X'],S['names'],S['idx']
def xval(p): return K(X[p]) if p in X else K.const(Fr(xr[p]))
a0,a1,lam=xval(0),xval(1),xval(2)
KMAX=5; nk={k:9-k for k in range(KMAX+1)}
# reconstruct H'_k (symmetric, over K)
Hs={k:[[K() for _ in range(nk[k]-1)] for _ in range(nk[k]-1)] for k in range(KMAX+1)}
for p,(k,i,j) in enumerate(idx):
    v=xval(3+p); Hs[k][i][j]=v; Hs[k][j][i]=v
log("H' reconstructed")
# exact kernel bases B_k (recompute as in task1_exact)
kv=json.load(open(os.path.join(here,'kernel_vectors_exact.json')))
import sympy as sp
def ratfun_to_K(expr_str):
    ex=sp.sympify(expr_str); n_,d_=sp.fraction(sp.together(ex))
    def toK(P):
        tot=K()
        for (kk,),c in sp.Poly(sp.expand(P),_u).terms():
            c=sp.Rational(c); tot=tot+U_**kk*K.const(Fr(int(c.p),int(c.q)))
        return tot
    return toK(n_)*inv(toK(d_))
V={k:[ratfun_to_K(s) for s in kv[str(k)]] for k in range(KMAX+1)}
def basis_perp(v):
    n=len(v); p0=next(i for i in range(n) if v[i].d); cols_=[]
    for i in range(n):
        if i==p0: continue
        col=[K() for _ in range(n)]; col[i]=K.const(1); col[p0]=K.const(0)-v[i]; cols_.append(col)
    return cols_
B={k:basis_perp(V[k]) for k in range(KMAX+1)}
# exact LDL^T:  H' = L Dg L^T,  L unit lower triangular
def ldl(H):
    n=len(H); L=[[K.const(1) if i==j else K() for j in range(n)] for i in range(n)]; Dg=[K() for _ in range(n)]
    A=[[H[i][j] for j in range(n)] for i in range(n)]
    for j in range(n):
        Dg[j]=A[j][j]-sum((L[j][k]*L[j][k]*Dg[k] for k in range(j)),K())
        dinv=inv(Dg[j])
        for i in range(j+1,n):
            L[i][j]=(A[i][j]-sum((L[i][k]*L[j][k]*Dg[k] for k in range(j)),K()))*dinv
    return L,Dg
Lk={}; Dk={}
for k in range(KMAX+1):
    L,Dg=ldl(Hs[k]); Lk[k]=L; Dk[k]=Dg
    log(f"LDL block {k}: D numerically", [nstr(d.num(US),6) for d in Dg])
# certificate vectors: for block k and column r: vec_r = sum_a B_k[a] * L[a][r]   (in K^{n_k}); D k r = Dg[r]
VEC={}; DD={}
for k in range(KMAX+1):
    m=nk[k]-1; VEC[k]=[]; DD[k]=[]
    for r in range(m):
        vec=[sum((B[k][a][i]*Lk[k][a][r] for a in range(m)),K()) for i in range(nk[k])]
        VEC[k].append(vec); DD[k].append(Dk[k][r])
    VEC[k].append([K() for _ in range(nk[k])]); DD[k].append(K())     # padding row (corank one)
log("certificate assembled")
# ---------- numerical validation at 50 digits ----------
from bv import Sk as Sk_num
import numpy as np
a0n,a1n,lamn=a0.num(US),a1.num(US),lam.num(US)
Fmat={k:[[sum((VEC[k][r][i]*VEC[k][r][j]*DD[k][r] for r in range(nk[k])),K()).num(US) for j in range(nk[k])] for i in range(nk[k])] for k in range(KMAX+1)}
log("a0,a1,lam =",nstr(a0n,15),nstr(a1n,15),nstr(lamn,15))
log("D min per block:",[nstr(min(DD[k][r].num(US) for r in range(nk[k]-1)),4) for k in range(KMAX+1)])
def Fnum(x,y,z):
    tot=mpf(0)
    for k in range(KMAX+1):
        S3=Sk_num(k,8,float(x),float(y),float(z))
        tot+=sum(Fmat[k][i][j]*mpf(S3[i,j]) for i in range(nk[k]) for j in range(nk[k]))
    return tot
r_=msqrt(1-US); y_=msqrt(2+2*US-msqrt(2)*(1-US)); z_=msqrt(2+2*US+msqrt(2)*(1-US)); w_=msqrt(2)
E=(4*w_+2)/r_+8/y_+8/z_
bound=(64*a0n-8*(a0n+a1n)-8*Fnum(1,1,1))/2
log("bound - E(u*) =",nstr(bound-E,5))
def h(t): return 1/msqrt(2-2*t)
def P(s): t=1-s*s/2; return (1-18*lamn)-s*(a0n+a1n*t+3*Fnum(1,t,t))
pts=[mpf(24)/25+(2-mpf(24)/25)*i/1200 for i in range(1201)]
pv=[P(s) for s in pts]; log("pair polynomial min on 1201 pts:",nstr(min(pv),5))
for s in (w_*r_,2*r_,y_,z_): log("   P at chord",nstr(s,8),"=",nstr(P(s),3))
g=[mpf(-1)+mpf('1.5373')*i/30 for i in range(31)]; tv=[]
for uu_ in g:
    for vv_ in g:
        if vv_<uu_: continue
        for tt_ in g:
            if tt_<vv_ or 1+2*uu_*vv_*tt_-uu_*uu_-vv_*vv_-tt_*tt_<0: continue
            tv.append(lamn*(h(uu_)+h(vv_)+h(tt_))-Fnum(uu_,vv_,tt_))
log(f"triangle slack min on {len(tv)} pts:",nstr(min(tv),5))
# heights
hs=[len(str(v.numerator))+len(str(v.denominator)) for k in range(KMAX+1) for r in range(nk[k]) for e in VEC[k][r]+[DD[k][r]] for v in e.d.values()]
log("rational heights in certData (digits): max",max(hs),"median",sorted(hs)[len(hs)//2],"entries",len(hs))
# ---------- Lean rendering ----------
def lean(x):
    if not x.d: return "0"
    terms=[]
    for (a,b,c,d,e),v in sorted(x.d.items()):
        f=[f"({v.numerator}/{v.denominator})"]
        if a: f.append(f"uStar ^ {a}")
        if b: f.append("Real.sqrt 2")
        if c: f.append("rStar")
        if d: f.append("s2Star")
        if e: f.append("s4Star")
        terms.append(" * ".join(f))
    return "(" + " + ".join(terms) + ")"
out=["/-- The exact certificate data (Task 1), generated by `threepoint/task1_emit.py`. -/",
     "noncomputable def certData : ThreePointCertData where",
     f"  a0 := {lean(a0)}", f"  a1 := {lean(a1)}", f"  lam := {lean(lam)}",
     "  L := fun k => match k with"]
for k in range(KMAX+1):
    rows=[", ".join(lean(VEC[k][r][i]) for i in range(nk[k])) for r in range(nk[k])]
    out.append(f"    | {k} => !![" + ";\n         ".join(rows) + "]")
out.append("  D := fun k => match k with")
for k in range(KMAX+1):
    out.append(f"    | {k} => ![" + ", ".join(lean(DD[k][r]) for r in range(nk[k])) + "]")
txt="\n".join(out)+"\n"
open(os.path.join(here,'certData_generated.lean'),'w').write(txt)
log("Lean text written: certData_generated.lean,",len(txt),"chars")
pickle.dump(dict(a0=a0.d,a1=a1.d,lam=lam.d,VEC={k:[[e.d for e in v] for v in VEC[k]] for k in VEC},DD={k:[e.d for e in DD[k]] for k in DD}),open(os.path.join(here,'certData_exact.pkl'),'wb'))
log("done")
