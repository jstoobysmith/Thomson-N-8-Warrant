import json, sys, os
from fractions import Fraction
from mpmath import mp, mpf, matrix, nstr, lu_solve, svd_r, eigsy, qr
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
mp.dps=50
here=os.path.dirname(os.path.abspath(__file__))
src=open(os.path.join(here,'task1_split.py')).read().split("# rank-revealing: choose 24")[0]
exec(src)
names=["a0","a1","lam"]+[f"H{k}[{i},{j}]" for (k,i,j) in idx]
import numpy as np
Jn=np.array([[float(J[q,p]) for p in range(nx)] for q in range(J.rows)])
S=np.linalg.svd(Jn,compute_uv=False); print("singular values of J:",np.array2string(S[:27],precision=2))
rank=int((S>1e-9*S[0]).sum()); print("numerical rank:",rank)
# orthonormal row basis of J (rank r), then pivoted QR on its columns to pick r well-conditioned columns
U,S_,Vt=np.linalg.svd(Jn); R=Vt[:rank]                     # r x nx, rows span the row space
Q_,R_,piv=__import__('scipy.linalg',fromlist=['qr']).qr(R,pivoting=True)
cols=sorted(piv[:rank].tolist()); print("chosen columns:",[names[p] for p in cols])
# equations: take r independent rows via pivoted QR on J^T columns
Q2,R2,piv2=__import__('scipy.linalg',fromlist=['qr']).qr(Jn.T,pivoting=True); rows=sorted(piv2[:rank].tolist())
Jp=np.array([[Jn[q,p] for p in cols] for q in rows]); print("pivot block cond:",f"{np.linalg.cond(Jp):.3e}")
# solve in mp
free=[p for p in range(nx) if p not in cols]; xr=matrix(x0)
for p in free:
    fr=Fraction(str(nstr(x0[p],13))); xr[p]=mpf(fr.numerator)/fr.denominator
Jpm=matrix(rank,rank); rhs=matrix(rank,1)
for a,q in enumerate(rows):
    s=-base[q]
    for p in free: s-=J[q,p]*xr[p]
    rhs[a]=s
    for b,p in enumerate(cols): Jpm[a,b]=J[q,p]
y=lu_solve(Jpm,rhs)
for b,p in enumerate(cols): xr[p]=y[b]
print("residual after solve:",nstr(mp.norm(residuals(xr)),4),"  |x_new - x0| =",nstr(mp.norm(xr-x0),4))
a0,a1,lam,H=unpack(xr)
print("min eig H_k:",[nstr(min(eigsy(H[k])[0]),5) for k in range(K+1)])
def Pf(s): t=1-s*s/2; return (1-18*lam)-s*(a0+a1*t+3*Fval(H,1,t,t))
print("pair min on 801 pts:",nstr(min(Pf(mpf(24)/25+(2-mpf(24)/25)*i/800) for i in range(801)),6))
g=[mpf(-1)+mpf('1.5373')*i/24 for i in range(25)]; tv=[]
for uu in g:
    for vv in g:
        if vv<uu: continue
        for tt in g:
            if tt<vv or 1+2*uu*vv*tt-uu*uu-vv*vv-tt*tt<0: continue
            tv.append(lam*(h(uu)+h(vv)+h(tt))-Fval(H,uu,vv,tt))
print(f"triangle min on {len(tv)} pts:",nstr(min(tv),6))
