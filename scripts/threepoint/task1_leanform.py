"""The pivot system in exactly the form used in Lean (rows in chord variables: pairP value/derivative,
triP = abc*slack value and coordinate derivatives), from the inner-product-form rows by the chain rule.
Outputs: conditioning, the rational approximate inverse N, ||I - N M||, residual at pivotsNum."""
import pickle, json, os, sys
from fractions import Fraction as Fr
import numpy as np
from mpmath import mp, mpf, matrix as mpmat, lu_solve, sqrt as msqrt, nstr, norm
mp.dps=50
here=os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0,here)
exec(open(os.path.join(here,'task1_exact.py')).read().split("# ---------------- antiprism data in K ----------------")[0])
D=pickle.load(open(os.path.join(here,'task1_rows_polybasis.pkl'),'rb'))
rows=[({p:K(v) for p,v in row.items()},K(rhs)) for row,rhs in D['rows']]; names=D['names']; idx=D['idx']; nx=len(names)
des=json.load(open(os.path.join(here,'task1_design.json')))
types=['FFA','FDN','FNA','DAA','NNA']
lab=['bound']+[f"pair{c}_{w}" for c in 'ADNF' for w in ('val','der')]+[f"tri{t}_{w}" for t in types for w in ('val','du','dv','dt')]
# numeric inner-product-form rows (scaled unknowns as in design2)
KMAX=5
SC={int(k):[Fr(s) for s in v] for k,v in des['scales'].items()}
scale_col=[Fr(1)]*3+[SC[k][i]*SC[k][j] for (k,i,j) in idx]
Jm=mpmat(len(rows),nx); bm=mpmat(len(rows),1)
for q,(row,rhs) in enumerate(rows):
    bm[q]=rhs.num(US)
    for p,v in row.items(): Jm[q,p]=v.num(US)*mpf(scale_col[p].numerator)/scale_col[p].denominator
# chords and inner products at u*
w_=msqrt(2); r_=msqrt(1-US); y_=msqrt(2+2*US-w_*(1-US)); z_=msqrt(2+2*US+w_*(1-US))
CH={'A':w_*r_,'D':2*r_,'N':y_,'F':z_}
def rowvec(l): q=lab.index(l); return [Jm[q,p] for p in range(nx)]+[bm[q]]     # affine row: coeffs, rhs
def comb(terms):   # sum c*row
    out=[mpf(0)]*(nx+1)
    for c,l in terms:
        r=rowvec(l)
        for i in range(nx+1): out[i]+=c*r[i]
    return out
# Lean rows: bound: (64a0-8(a0+a1)-8F)/2 - E  = (1/2)*(python bound row: 28a0-4a1-4F = E)
L={}
L['bound']=comb([(mpf(1)/2,'bound')])
for X in 'ADNF':
    L[f'pair{X}_val']=comb([(1,f'pair{X}_val')]); L[f'pair{X}_der']=comb([(1,f'pair{X}_der')])
for t in types:
    a,b,c=[CH[ch] for ch in t]
    L[f'tri{t}_val']=comb([(a*b*c,f'tri{t}_val')])
    # d/da [abc*slack(t(a),t(b),t(c))] = bc*slack + abc*(-a)*d_u slack
    L[f'tri{t}_da']=comb([(b*c,f'tri{t}_val'),(-a*b*c*a,f'tri{t}_du')])
    L[f'tri{t}_db']=comb([(a*c,f'tri{t}_val'),(-a*b*c*b,f'tri{t}_dv')])
    L[f'tri{t}_dc']=comb([(a*b,f'tri{t}_val'),(-a*b*c*c,f'tri{t}_dt')])
leanrows=['bound','pairA_der','pairD_val','pairD_der','pairN_val','pairN_der','pairF_val','pairF_der',
 'triFFA_val','triFFA_da','triFFA_dc','triFDN_val','triFDN_da','triFDN_dc','triFNA_val','triFNA_da','triFNA_db','triFNA_dc',
 'triDAA_val','triDAA_da','triDAA_db','triNNA_val','triNNA_da','triNNA_dc']
cols=des['cols']; free=[p for p in range(nx) if p not in cols]
xr={names.index(n):Fr(v) for n,v in des['free'].items()}
phat={names.index(n):Fr(v) for n,v in des['pivots_num'].items()}
M=mpmat(24,24); cvec=mpmat(24,1)
for a,l in enumerate(leanrows):
    r=L[l]
    cvec[a]=r[nx]-sum(r[p]*mpf(xr[p].numerator)/xr[p].denominator for p in free)
    for j,p in enumerate(cols): M[a,j]=r[p]
psol=lu_solve(M,cvec)
print("Lean-form system: max |p_lean - p_design| =",nstr(max(abs(psol[j]-mpf(des['pivots_50'][names[p]])) for j,p in enumerate(cols)),3))
Mf=np.array([[float(M[i,j]) for j in range(24)] for i in range(24)]); Nf=np.linalg.inv(Mf)
E_=np.eye(24)-Nf@Mf
print(f"cond {np.linalg.cond(Mf):.3e}  ||M||inf {np.abs(Mf).sum(1).max():.3e}  ||N||inf {np.abs(Nf).sum(1).max():.3e}  ||I-NM||inf {np.abs(E_).sum(1).max():.2e}")
# rational N with 17 significant digits, and exact-ish check in 50 digits
Nr=[[Fr(np.format_float_positional(Nf[i,j],precision=17,unique=False,trim='-')) for j in range(24)] for i in range(24)]
Nm=mpmat(24,24)
for i in range(24):
    for j in range(24): Nm[i,j]=mpf(Nr[i][j].numerator)/Nr[i][j].denominator
Em=mpmat(24,24)
for i in range(24):
    for j in range(24): Em[i,j]=(1 if i==j else 0)-sum(Nm[i,k]*M[k,j] for k in range(24))
eta=max(sum(abs(Em[i,j]) for j in range(24)) for i in range(24))
print("with 17-digit rational N: ||I - N M||inf =",nstr(eta,3))
res=[cvec[a]-sum(M[a,j]*mpf(phat[p].numerator)/phat[p].denominator for j,p in enumerate(cols)) for a in range(24)]
print("residual ||pivotRhs - M pivotsNum||inf at 50 digits:",nstr(max(abs(x) for x in res),3), " => |pivots - pivotsNum| <=",nstr(max(sum(abs(Nm[i,j]) for j in range(24)) for i in range(24))/(1-eta)*max(abs(x) for x in res),3))
des['leanform']=dict(rows=leanrows,cond=float(np.linalg.cond(Mf)),normM=float(np.abs(Mf).sum(1).max()),normN=float(np.abs(Nf).sum(1).max()),
                     eta_17digit=float(eta),approx_inverse=[[str(x) for x in row] for row in Nr])
json.dump(des,open(os.path.join(here,'task1_design.json'),'w'),indent=1)
print("saved approx_inverse into task1_design.json")
