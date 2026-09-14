"""Task 1 prototype: the tightness system has rank 24 in 158 unknowns.  Fix 134 unknowns at short
RATIONALS and solve the remaining 24 exactly (here: to 50 digits, as a stand-in for the field solve).
Reports: which 24 unknowns, conditioning, size of the change, and whether PSD/inequalities survive."""
import json, sys, os, itertools
from fractions import Fraction
from mpmath import mp, mpf, matrix, sqrt, findroot, diff, eigsy, nstr, lu_solve, svd_r
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
mp.dps=50
here=os.path.dirname(os.path.abspath(__file__))
exec(open(os.path.join(here,'hp_project.py')).read().split("# starting point from double precision")[0].replace("Tc=json.load(open(os.path.join(here,sys.argv[1] if len(sys.argv)>1 else 'certificate_tight.json')))","Tc=json.load(open(os.path.join(here,sys.argv[1] if len(sys.argv)>1 else 'certificate_r5373.json')))"))
H0=[matrix(Tc['H'][str(k)]) for k in range(K+1)]
x0=matrix([mpf(Tc['a0']),mpf(Tc['a1']),mpf(Tc['lam'])]+[H0[k][i,j] for (k,i,j) in idx])
base=residuals(matrix([mpf(0)]*nx)); J=matrix(len(base),nx)
for p in range(nx):
    e=matrix([mpf(0)]*nx); e[p]=1; col=residuals(e)-base
    for q in range(len(base)): J[q,p]=col[q]
r0=residuals(x0); print("nx =",nx," equations =",len(base)," |residual(x0)| =",nstr(mp.norm(r0),4))
# rank-revealing: choose 24 independent equations and 24 pivot columns by greedy max-|pivot| elimination
Jn=matrix(J); rows=list(range(J.rows)); cols=list(range(nx))
Ared=[[J[q,p] for p in range(nx)] for q in range(J.rows)]
piv_rows=[]; piv_cols=[]
A=[row[:] for row in Ared]
for step in range(len(base)):
    best=None
    for q in rows:
        if q in piv_rows: continue
        for p in cols:
            if p in piv_cols: continue
            v=abs(A[q][p])
            if best is None or v>best[0]: best=(v,q,p)
    if best is None or best[0]<mpf(10)**-20: break
    _,q,p=best; piv_rows.append(q); piv_cols.append(p)
    for q2 in range(len(A)):
        if q2!=q and A[q2][p]!=0:
            f=A[q2][p]/A[q][p]
            for p2 in range(nx): A[q2][p2]-=f*A[q][p2]
print("rank =",len(piv_rows)," pivot columns (unknown indices):",sorted(piv_cols))
names=['a0','a1','lam']+[f"H{k}[{i},{j}]" for (k,i,j) in idx]
print("solved-for unknowns:",[names[p] for p in sorted(piv_cols)])
# fix the other 134 at 12-digit rationals; solve the 24 from the 24 pivot equations
free=[p for p in range(nx) if p not in piv_cols]
xr=matrix(x0)
for p in free: xr[p]=mpf(Fraction(str(nstr(x0[p],13))).numerator)/Fraction(str(nstr(x0[p],13))).denominator
# linear system for the 24 pivots: J[piv_rows, piv_cols] y = b - J[piv_rows, free] xr_free   (affine: residual = J x - b0 with b0=-base)
Jp=matrix(len(piv_rows),len(piv_cols)); rhs=matrix(len(piv_rows),1)
for a,q in enumerate(piv_rows):
    s=-base[q]
    for p in free: s-=J[q,p]*xr[p]
    rhs[a]=s
    for b,p in enumerate(piv_cols): Jp[a,b]=J[q,p]
y=lu_solve(Jp,rhs)
for b,p in enumerate(piv_cols): xr[p]=y[b]
print("residual after solving 24 unknowns:",nstr(mp.norm(residuals(xr)),4),"  |x_new - x0| =",nstr(mp.norm(xr-x0),4))
S=svd_r(Jp,compute_uv=False); print("24x24 pivot block condition number:",nstr(max(S)/min(S),5))
a0,a1,lam,H=unpack(xr)
for k in range(K+1):
    e,_=eigsy(H[k]); print(f"  H_{k} min eig = {nstr(min(e),6)}")
def Pf(s): t=1-s*s/2; return (1-18*lam)-s*(a0+a1*t+3*Fval(H,1,t,t))
pts=[mpf(24)/25+(2-mpf(24)/25)*i/800 for i in range(801)]
print("pair polynomial min on 801 pts:",nstr(min(Pf(s) for s in pts),6))
g=[mpf(-1)+mpf('1.5373')*i/24 for i in range(25)]; tv=[]
for uu in g:
    for vv in g:
        if vv<uu: continue
        for tt in g:
            if tt<vv or 1+2*uu*vv*tt-uu*uu-vv*vv-tt*tt<0: continue
            tv.append(lam*(h(uu)+h(vv)+h(tt))-Fval(H,uu,vv,tt))
print(f"triangle slack min on {len(tv)} pts:",nstr(min(tv),6))
json.dump(dict(pivot_unknowns=[names[p] for p in sorted(piv_cols)],free_count=len(free)),open(os.path.join(here,'task1_split_plan.json'),'w'),indent=1)
