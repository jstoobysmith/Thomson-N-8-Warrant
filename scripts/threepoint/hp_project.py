"""High-precision stage (mpmath, 50 digits): project the double-precision tight certificate onto the
EXACT affine space of tightness conditions, then verify PSD margins and the inequalities in high precision.
The tightness conditions are affine in x=(a0,a1,lam,vec H_k), so one least-squares step is an exact projection."""
import json, sys, os, itertools
from mpmath import mp, mpf, matrix, sqrt, findroot, chebyt, lu_solve, eigsy, diff, nstr
import sympy as sp
mp.dps=50
here=os.path.dirname(os.path.abspath(__file__))
C=json.load(open(os.path.join(here,'certificate_numerical.json')))
Tc=json.load(open(os.path.join(here,sys.argv[1] if len(sys.argv)>1 else 'certificate_tight.json')))
d=C['d']; K=C['KMAX']; N=8
# ---- u* to 50 digits, antiprism data exactly ----
s2=sqrt(2)
def apE(u): return (4*s2+2)/sqrt(1-u)+8/sqrt((2-s2)+(2+s2)*u)+8/sqrt((2+s2)+(2-s2)*u)
ust=findroot(lambda u: diff(apE,u), mpf('0.31408936788920186517709977'))
ESTAR=apE(ust)
r=sqrt(1-ust); hh=sqrt(ust); ss=r/s2
P=[[r,0,hh],[0,r,hh],[-r,0,hh],[0,-r,hh],[ss,ss,-hh],[-ss,ss,-hh],[-ss,-ss,-hh],[ss,-ss,-hh]]
G=[[sum(P[i][k]*P[j][k] for k in range(3)) for j in range(8)] for i in range(8)]
AP_t=[]; 
for i in range(8):
    for j in range(i+1,8):
        if not any(abs(G[i][j]-x)<mpf(10)**-20 for x in AP_t): AP_t.append(G[i][j])
AP_tri=[]
for i in range(8):
    for j in range(i+1,8):
        for k in range(j+1,8):
            tr=tuple(sorted([G[i][j],G[i][k],G[j][k]]))
            if not any(all(abs(tr[m]-x[m])<mpf(10)**-20 for m in range(3)) for x in AP_tri): AP_tri.append(tr)
print("u* =",nstr(ust,30)," E(u*) =",nstr(ESTAR,30)); print(len(AP_t),"distances,",len(AP_tri),"triangle types")
# ---- exact kernel vectors at u* ----
kv=json.load(open(os.path.join(here,'kernel_vectors_exact.json'))); u=sp.symbols('u')
V=[]
for k in range(K+1):
    V.append([mpf(str(sp.N(sp.sympify(e).subs(u,sp.Float(str(ust),60)),60))) for e in kv[str(k)]])
# ---- BV matrices in mpmath ----
def Qk(k,U,Vv,T):
    c=sp.Poly(sp.chebyshevt(k,sp.Symbol('x')),sp.Symbol('x')).all_coeffs()[::-1]
    w=(1-U*U)*(1-Vv*Vv); x=T-U*Vv; out=mpf(0)
    for j,cj in enumerate(c):
        if cj!=0 and (k-j)%2==0: out+=int(cj)*x**j*w**((k-j)//2)
    return out
def Yk(k,U,Vv,T):
    m=d-k+1; q=Qk(k,U,Vv,T); return matrix([[U**i*Vv**j*q for j in range(m)] for i in range(m)])
def Sk(k,U,Vv,T):
    acc=matrix(d-k+1,d-k+1)
    for p in itertools.permutations((U,Vv,T)): acc+=Yk(k,*p)
    return acc/6
def h(t): return 1/sqrt(2-2*t)
def hp(t): return (2-2*t)**mpf(-1.5)
# ---- unknown vector x = (a0,a1,lam, vech(H_k) ...), F_k = W_k H_k W_k^T ----
W=[matrix(Tc['W'][str(k)]) for k in range(K+1)]
n=[d-k+1 for k in range(K+1)]; m=[n[k]-1 for k in range(K+1)]
idx=[]; 
for k in range(K+1):
    for i in range(m[k]):
        for j in range(i,m[k]): idx.append((k,i,j))
nx=3+len(idx)
def unpack(x):
    a0,a1,lam=x[0],x[1],x[2]; H=[matrix(m[k],m[k]) for k in range(K+1)]
    for p,(k,i,j) in enumerate(idx): H[k][i,j]=x[3+p]; H[k][j,i]=x[3+p]
    return a0,a1,lam,H
def Fval(H,U,Vv,T,Sfun=Sk):
    tot=mpf(0)
    for k in range(K+1):
        S=Sfun(k,U,Vv,T); M=W[k].T*S*W[k]
        tot+=sum(H[k][i,j]*M[i,j] for i in range(m[k]) for j in range(m[k]))
    return tot
def residuals(x):
    a0,a1,lam,H=unpack(x); res=[]
    res.append((N*N*a0-N*(a0+a1)-N*Fval(H,1,1,1))/2-ESTAR)
    def Pf(s): t=1-s*s/2; return (1-18*lam)-s*(a0+a1*t+3*Fval(H,1,t,t))
    for t in AP_t:
        s=sqrt(2-2*t); res.append(Pf(s)); res.append(diff(Pf,s))
    for tr in AP_tri:
        x0,y0,z0=tr
        res.append(lam*(h(x0)+h(y0)+h(z0))-Fval(H,x0,y0,z0))
        for ax in range(3):
            def Fax(w,ax=ax):
                p=[x0,y0,z0]; p[ax]=w; return Fval(H,*p)
            res.append(lam*hp([x0,y0,z0][ax])-diff(Fax,[x0,y0,z0][ax]))
    return matrix(res)
# starting point from double precision
H0=[matrix(Tc['H'][str(k)]) for k in range(K+1)]
x0=[mpf(Tc['a0']),mpf(Tc['a1']),mpf(Tc['lam'])]+[H0[k][i,j] for (k,i,j) in idx]
x0=matrix(x0)
r0=residuals(x0); print("residual norm before projection:",nstr(mp.norm(r0),5))
# Jacobian (affine map): columns by unit perturbations
J=matrix(len(r0),nx)
base=residuals(matrix([mpf(0)]*nx))
for p in range(nx):
    e=matrix([mpf(0)]*nx); e[p]=1
    col=residuals(e)-base
    for q in range(len(r0)): J[q,p]=col[q]
# minimum-norm correction: x = x0 - J^T (J J^T)^+ r0   (use SVD-free approach via normal equations with regularisation on rank deficiency)
JJt=J*J.T
# rank-revealing: eigen-decompose JJt, pseudo-invert
ev,U=eigsy(JJt); tol=mpf(10)**-30*max(abs(e) for e in ev)
pinv=matrix(len(r0),len(r0))
for q in range(len(ev)):
    if abs(ev[q])>tol:
        uq=U[:,q]; pinv+= (uq*uq.T)/ev[q]
print("rank of tightness system:",sum(1 for e in ev if abs(e)>tol),"of",len(r0),"equations")
x1=x0-J.T*(pinv*r0)
r1=residuals(x1); print("residual norm after projection :",nstr(mp.norm(r1),5))
print("|x1-x0| =",nstr(mp.norm(x1-x0),5))
a0,a1,lam,H=unpack(x1)
print("a0,a1,lam =",nstr(a0,20),nstr(a1,20),nstr(lam,20))
for k in range(K+1):
    e,_=eigsy(H[k]); print(f"  H_{k} min eig = {nstr(min(e),8)}")
# inequalities in high precision on moderate grids
def Pf(s): t=1-s*s/2; return (1-18*lam)-s*(a0+a1*t+3*Fval(H,1,t,t))
pts=[mpf(-1)+mpf('1.537')*i/1500 for i in range(1501)]
pv=[Pf(sqrt(2-2*t)) for t in pts]; print("pair polynomial min on 1501 pts:",nstr(min(pv),6))
g=[mpf(-1)+mpf('1.537')*i/28 for i in range(29)]
tv=[]
for uu in g:
    for vv in g:
        if vv<uu: continue
        for tt in g:
            if tt<vv or 1+2*uu*vv*tt-uu*uu-vv*vv-tt*tt<0: continue
            tv.append(lam*(h(uu)+h(vv)+h(tt))-Fval(H,uu,vv,tt))
print(f"triangle slack min on {len(tv)} pts:",nstr(min(tv),6))
out=dict(dps=50,a0=str(a0),a1=str(a1),lam=str(lam),ustar=str(ust),Estar=str(ESTAR),
         H={str(k):[[str(H[k][i,j]) for j in range(m[k])] for i in range(m[k])] for k in range(K+1)},
         W={str(k):[[str(W[k][i,j]) for j in range(m[k])] for i in range(n[k])] for k in range(K+1)},
         kernel_v={str(k):[str(v) for v in V[k]] for k in range(K+1)})
json.dump(out,open(os.path.join(here,'certificate_hp.json'),'w'),indent=1); print("written certificate_hp.json")
