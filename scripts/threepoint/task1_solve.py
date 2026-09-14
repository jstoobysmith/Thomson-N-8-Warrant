"""TASK 1, stage 2: from task1_rows.pkl (exact tightness rows over K), choose 24 pivot unknowns by
rank-revealing pivoted QR (numerically), fix the rest at 13-digit rationals, and solve the 24x24
system over K EXACTLY as a (24*192)x(24*192) rational system with python-flint.  Validate against
the 50-digit solution, then emit the data."""
import pickle, json, os, sys, time
sys.set_int_max_str_digits(0)
from fractions import Fraction as Fr
import numpy as np, scipy.linalg
from flint import fmpq_mat, fmpq
here=os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0,here)
T0=time.time()
def log(*a): print(f"[{time.time()-T0:7.1f}s]",*a,flush=True)
exec(open(os.path.join(here,'task1_exact.py')).read().split("# ---------------- antiprism data in K ----------------")[0])   # field class K, BASIS, US
D=pickle.load(open(os.path.join(here,'task1_rows.pkl'),'rb'))
rows=[({p:K(v) for p,v in row.items()},K(rhs)) for row,rhs in D['rows']]; names=D['names']; idx=D['idx']
x0=[Fr(s) for s in D['x0']]; nx=len(x0); nr=len(rows)
log(f"{nr} rows, {nx} unknowns loaded")
# numeric Jacobian for pivoting
J=np.zeros((nr,nx)); b=np.zeros(nr)
for q,(row,rhs) in enumerate(rows):
    b[q]=float(rhs.num(US))
    for p,v in row.items(): J[q,p]=float(v.num(US))
S=np.linalg.svd(J,compute_uv=False); rank=int((S>1e-9*S[0]).sum()); log("numerical rank:",rank, "sv tail:",np.array2string(S[rank-2:rank+2],precision=2))
Q_,R_,pivc=scipy.linalg.qr(np.linalg.svd(J)[2][:rank],pivoting=True); cols=sorted(pivc[:rank].tolist())
Q2,R2,pivr=scipy.linalg.qr(J.T,pivoting=True); rsel=sorted(pivr[:rank].tolist())
Jp=J[np.ix_(rsel,cols)]; log("pivot block cond:",f"{np.linalg.cond(Jp):.3e}"); log("pivot unknowns:",[names[p] for p in cols])
free=[p for p in range(nx) if p not in cols]
xr=[Fr(str(np.format_float_positional(float(x0[p]),precision=13,unique=False,trim='-'))) if p in free else None for p in range(nx)]
# exact block system: for each selected row q:  sum_{p in cols} row[p]*x_p = rhs - sum_{p free} row[p]*xr_p
N=192; n=rank
M=fmpq_mat(n*N,n*N); RHS=fmpq_mat(n*N,1)
def mulmat_into(M,x,bi,bj):
    for j,m in enumerate(BASIS):
        col=x*K({m:Fr(1)})
        for k,v in col.d.items(): M[bi*N+BIDX[k],bj*N+j]=fmpq(v.numerator,v.denominator)
for a,q in enumerate(rsel):
    row,rhs=rows[q]
    r=rhs
    for p in free:
        if p in row: r=r-row[p]*K.const(xr[p])
    for k,v in r.d.items(): RHS[a*N+BIDX[k],0]=fmpq(v.numerator,v.denominator)
    for bj,p in enumerate(cols):
        if p in row: mulmat_into(M,row[p],a,bj)
    log(f"  assembled row {a+1}/{n}")
log("solving the",n*N,"x",n*N,"rational system ...")
sol=M.solve(RHS)
log("solved")
X={}
for bj,p in enumerate(cols):
    X[p]=K({BASIS[i]:Fr(int(sol[bj*N+i,0].p),int(sol[bj*N+i,0].q)) for i in range(N) if sol[bj*N+i,0]!=0})
# validate: residuals numerically at 50 digits, and compare with numerical x0
def val(p): return X[p].num(US) if p in X else mpf(xr[p].numerator)/xr[p].denominator
res=[]
for row,rhs in rows:
    tot=-rhs.num(US)
    for p,v in row.items(): tot+=v.num(US)*val(p)
    res.append(abs(tot))
log("max residual of ALL rows at the exact solution:",mp.nstr(max(res),4))
log("max |x_exact - x0| over pivots:",mp.nstr(max(abs(val(p)-mpf(x0[p].numerator)/x0[p].denominator) for p in cols),4))
try:
    hs=[len(str(v.numerator))+len(str(v.denominator)) for p in cols for v in X[p].d.values()]
    log("coefficient heights among pivots (digits): max",max(hs),"median",sorted(hs)[len(hs)//2],"count",len(hs))
except Exception as e: log("height stat failed:",repr(e))
pickle.dump(dict(cols=cols,free=free,xr={p:str(xr[p]) for p in free},X={p:{k:str(v) for k,v in X[p].d.items()} for p in cols},names=names,idx=idx),open(os.path.join(here,'task1_exact_solution.pkl'),'wb'))
log("saved task1_exact_solution.pkl")
