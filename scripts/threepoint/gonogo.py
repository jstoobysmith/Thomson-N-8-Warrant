"""GO/NO-GO test for sharpness of the three-point bound at N=8.
Impose exact tightness at the antiprism as LINEAR constraints and maximise the PSD margin mu."""
import numpy as np, cvxpy as cp, json, sys, os, time
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from bv import Sk
from numpy.polynomial import legendre as L
C=json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'certificate_numerical.json')))
d=C['d']; K=C['KMAX']; N=8; ESTAR=C['target_E_ustar']; tlo,thi=-1.0,0.537
AP_t=C['antiprism_inner_products']; AP_tri=[tuple(x) for x in C['antiprism_triangle_types']]
V=[np.array(C['kernel_vectors'][str(k)]) for k in range(K+1)]
def h(t): return 1.0/np.sqrt(2-2*t)
def hp(t): return (2-2*t)**-1.5
# orthonormal bases W_k of v_k^perp
W=[]
for k in range(K+1):
    v=V[k]/np.linalg.norm(V[k]); Q,_=np.linalg.qr(np.column_stack([v,np.eye(len(v))])); W.append(Q[:,1:len(v)])
n=[d-k+1 for k in range(K+1)]
H=[cp.Variable((n[k]-1,n[k]-1),symmetric=True) for k in range(K+1)]
a0=cp.Variable(); a1=cp.Variable(); lam=cp.Variable(); mu=cp.Variable()
def Fexpr(x,y,z,dS=None):
    tot=0
    for k in range(K+1):
        S=Sk(k,d,x,y,z) if dS is None else dS(k,x,y,z)
        tot=tot+cp.sum(cp.multiply(H[k],W[k].T@S@W[k]))
    return tot
def dSk(axis,e=1e-6):
    def f(k,x,y,z):
        p=[x,y,z]; pp=p[:]; pm=p[:]; pp[axis]+=e; pm[axis]-=e
        return (Sk(k,d,*pp)-Sk(k,d,*pm))/(2*e)
    return f
cons=[lam>=0, lam<=1/18, a1>=0]
for k in range(K+1): cons.append(H[k]>>mu*np.eye(n[k]-1))
# --- exact tightness (linear) ---
cons.append((N*N*a0-N*(a0+a1)-N*Fexpr(1.,1.,1.))/2==ESTAR)
def Pexpr(s):
    t=1-s*s/2; return (1-18*lam)-s*(a0+a1*t+3*Fexpr(1.,t,t))
def dPexpr(s,e=1e-6): return (Pexpr(s+e)-Pexpr(s-e))/(2*e)
for t in AP_t:
    s=np.sqrt(2-2*t); cons+= [Pexpr(s)==0, dPexpr(s)==0]
def Texpr(x,y,z): return lam*(h(x)+h(y)+h(z))-Fexpr(x,y,z)
for tr in AP_tri:
    x,y,z=tr; cons.append(Texpr(x,y,z)==0)
    for ax in range(3):
        grad_h=[hp(x),hp(y),hp(z)][ax]
        cons.append(lam*grad_h-Fexpr(x,y,z,dSk(ax))==0)
# --- inequalities on grids ---
for t in np.linspace(tlo,thi,700): cons.append(Pexpr(np.sqrt(2-2*t))>=0)
g=np.linspace(tlo,thi,30); tri=[(u,v,t) for u in g for v in g if v>=u for t in g if t>=v and 1+2*u*v*t-u*u-v*v-t*t>=-1e-12]
for tr in tri: cons.append(Texpr(*tr)>=0)
t0=time.time()
p=cp.Problem(cp.Maximize(mu),cons); p.solve(solver=cp.CLARABEL,tol_gap_abs=1e-10,tol_gap_rel=1e-10,tol_feas=1e-10,max_iter=800)
print(f"status={p.status}   mu* = {mu.value}   ({time.time()-t0:.0f}s)")
if mu.value is not None:
    print(f"a0={a0.value:.8f} a1={a1.value:.8f} lambda={lam.value:.8f}")
    Fv=[W[k]@H[k].value@W[k].T for k in range(K+1)]
    for k in range(K+1):
        ev=np.linalg.eigvalsh(H[k].value); print(f"  H_{k}: min eig {ev.min():+.3e}  max {ev.max():.3e}")
    json.dump(dict(a0=float(a0.value),a1=float(a1.value),lam=float(lam.value),mu=float(mu.value),
                   H={str(k):H[k].value.tolist() for k in range(K+1)},W={str(k):W[k].tolist() for k in range(K+1)},
                   F={str(k):Fv[k].tolist() for k in range(K+1)}),
              open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'certificate_tight.json'),'w'),indent=1)
    print("written certificate_tight.json")
    print("\nVERDICT:", "GO — a certificate exactly tight at the antiprism exists with positive PSD margin" if mu.value>1e-7 else "NO-GO — no strictly feasible tight certificate at this degree/grid")
