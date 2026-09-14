"""Robust tight certificate: fix PSD margin, maximise weighted inequality slack; sample the boundary of Delta."""
import numpy as np, cvxpy as cp, json, sys, os, time
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from bv import Sk
here=os.path.dirname(os.path.abspath(__file__))
C=json.load(open(os.path.join(here,'certificate_numerical.json')))
d=C['d']; K=C['KMAX']; N=8; ESTAR=C['target_E_ustar']; tlo,thi=-1.0,0.5373
AP_t=C['antiprism_inner_products']; AP_tri=[tuple(x) for x in C['antiprism_triangle_types']]
V=[np.array(C['kernel_vectors'][str(k)]) for k in range(K+1)]
MU=float(sys.argv[1]) if len(sys.argv)>1 else 1.5e-3; NG=int(sys.argv[2]) if len(sys.argv)>2 else 40
PREV=sys.argv[3] if len(sys.argv)>3 else None; NV=int(sys.argv[4]) if len(sys.argv)>4 else 100
def h(t): return 1.0/np.sqrt(2-2*t)
def hp(t): return (2-2*t)**-1.5
W=[]
for k in range(K+1):
    v=V[k]/np.linalg.norm(V[k]); Q,_=np.linalg.qr(np.column_stack([v,np.eye(len(v))])); W.append(Q[:,1:len(v)])
n=[d-k+1 for k in range(K+1)]
H=[cp.Variable((n[k]-1,n[k]-1),symmetric=True) for k in range(K+1)]
a0=cp.Variable(); a1=cp.Variable(); lam=cp.Variable(); eps=cp.Variable()
def Fexpr(x,y,z,dS=None):
    tot=0
    for k in range(K+1):
        S=Sk(k,d,x,y,z) if dS is None else dS(k,x,y,z); tot=tot+cp.sum(cp.multiply(H[k],W[k].T@S@W[k]))
    return tot
def dSk(axis,e=1e-6):
    def f(k,x,y,z):
        p=[x,y,z]; pp=p[:]; pm=p[:]; pp[axis]+=e; pm[axis]-=e; return (Sk(k,d,*pp)-Sk(k,d,*pm))/(2*e)
    return f
cons=[lam>=0, lam<=1/18, a1>=0]+[H[k]>>MU*np.eye(n[k]-1) for k in range(K+1)]
cons.append((N*N*a0-N*(a0+a1)-N*Fexpr(1.,1.,1.))/2==ESTAR)
def Pexpr(s): t=1-s*s/2; return (1-18*lam)-s*(a0+a1*t+3*Fexpr(1.,t,t))
def dPexpr(s,e=1e-6): return (Pexpr(s+e)-Pexpr(s-e))/(2*e)
for t in AP_t:
    s=np.sqrt(2-2*t); cons+=[Pexpr(s)==0, dPexpr(s)==0]
def Texpr(x,y,z): return lam*(h(x)+h(y)+h(z))-Fexpr(x,y,z)
for tr in AP_tri:
    x,y,z=tr; cons.append(Texpr(x,y,z)==0)
    for ax in range(3): cons.append(lam*[hp(x),hp(y),hp(z)][ax]-Fexpr(x,y,z,dSk(ax))==0)
# --- local positive-definiteness at the touching points (LMIs; the Hessian is linear in the unknowns) ---
ETA=float(sys.argv[6]) if len(sys.argv)>6 else 2e-4
def hpp(t): return 3*(2-2*t)**-2.5
def d2Sk(a,b,e=1e-4):
    def f(k,x,y,z):
        p=[x,y,z]
        def S(da,db):
            q=p[:]; q[a]+=da; q[b]+=db; return Sk(k,d,*q)
        if a==b: return (S(e,0)-2*Sk(k,d,*p)+S(-e,0))/(e*e)
        return (S(e,e)-S(e,-e)-S(-e,e)+S(-e,-e))/(4*e*e)
    return f
for tr in AP_tri:
    x,y,z=tr; rows=[]
    for a in range(3):
        row=[]
        for b in range(3):
            row.append((lam*hpp([x,y,z][a]) if a==b else 0)-Fexpr(x,y,z,d2Sk(a,b)))
        rows.append(cp.hstack([cp.reshape(r_,(1,1),order='C') if not np.isscalar(r_) else np.array([[r_]]) for r_ in row]))
    Hm=cp.vstack(rows); Hs=(Hm+Hm.T)/2
    cons.append(Hs>>ETA*np.eye(3))
for t in AP_t:
    s=np.sqrt(2-2*t); e=1e-4; cons.append((Pexpr(s+e)-2*Pexpr(s)+Pexpr(s-e))/(e*e)>=ETA)
print(f"added Hessian LMIs at 5 triangle types and P''>= {ETA} at 4 distances")
# weighted inequality margins
tg=np.linspace(tlo,thi,1500); qp=np.array([np.prod([(t-ti)**2 for ti in AP_t]) for t in tg]); qp/=qp.max()
for t,q in zip(tg,qp): cons.append(Pexpr(np.sqrt(2-2*t))>=eps*q)
g=np.linspace(tlo,thi,NG); tri=[(u,v,t) for u in g for v in g if v>=u for t in g if t>=v and 1+2*u*v*t-u*u-v*v-t*t>=-1e-12]
# boundary of Delta (degenerate triangles) and the box faces
for u in g:
    for v in g:
        if v<u: continue
        disc=(1-u*u)*(1-v*v)
        for t in (u*v+np.sqrt(disc), u*v-np.sqrt(disc)):
            if tlo<=t<=thi: tri.append(tuple(sorted((u,v,t))))
for u in g:
    for v in g:
        if v>=u and 1+2*u*v*thi-u*u-v*v-thi*thi>=0 and v<=thi: tri.append(tuple(sorted((u,v,thi))))
# cutting planes: points where the previous certificate's triangle slack is small/negative on a fine grid
if PREV:
    Tp=json.load(open(os.path.join(here,PREV))); Fp=[np.array(Tp['F'][str(k)]) for k in range(K+1)]; lp=Tp['lam']
    def Tprev(x,y,z): return lp*(h(x)+h(y)+h(z))-sum(np.sum(Fp[k]*Sk(k,d,x,y,z)) for k in range(K+1))
    gv=np.linspace(tlo,thi,NV); cnt=0
    for u in gv:
        for v in gv:
            if v<u: continue
            for t in gv:
                if t<v or 1+2*u*v*t-u*u-v*v-t*t<-1e-12: continue
                if Tprev(u,v,t)<2e-5: tri.append((u,v,t)); cnt+=1
    print(f"added {cnt} cutting-plane points from {PREV} on a {NV}/axis grid")
loc=np.arange(-0.1,0.1001,0.0125); cnt=0
for tr in AP_tri:
    for dx in loc:
        for dy in loc:
            for dz in loc:
                q=(tr[0]+dx,tr[1]+dy,tr[2]+dz)
                if all(tlo<=x<=thi for x in q) and 1+2*q[0]*q[1]*q[2]-q[0]**2-q[1]**2-q[2]**2>=0 and (dx,dy,dz)!=(0,0,0):
                    tri.append(tuple(sorted(q))); cnt+=1
print(f"added {cnt} dense local points near the touching types")
tri=np.array(sorted(set(tri)))
qt=np.array([np.prod([np.sum((np.array(x)-np.array(m))**2) for m in AP_tri]) for x in tri]); qt/=qt.max()
for x,q in zip(tri,qt): cons.append(Texpr(*x)>=eps*q)
t0=time.time(); p=cp.Problem(cp.Maximize(eps),cons); p.solve(solver=cp.CLARABEL,tol_gap_abs=1e-10,tol_gap_rel=1e-10,tol_feas=1e-10,max_iter=800)
print(f"status={p.status}  eps*={(eps.value if eps.value is not None else float('nan')):.3e}  (PSD margin fixed {MU}, {len(tri)} triangle pts incl. boundary, {time.time()-t0:.0f}s)")
if eps.value is None: sys.exit(2)
Fv=[W[k]@H[k].value@W[k].T for k in range(K+1)]
json.dump(dict(a0=float(a0.value),a1=float(a1.value),lam=float(lam.value),mu=MU,eps=float(eps.value),
               H={str(k):H[k].value.tolist() for k in range(K+1)},W={str(k):W[k].tolist() for k in range(K+1)},
               F={str(k):Fv[k].tolist() for k in range(K+1)}),open(os.path.join(here,(sys.argv[5] if len(sys.argv)>5 else 'certificate_robust.json')),'w'),indent=1)
print("written", sys.argv[5] if len(sys.argv)>5 else "certificate_robust.json")
