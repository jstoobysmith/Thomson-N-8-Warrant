import numpy as np, json, sys, os
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from bv import Sk
here=os.path.dirname(os.path.abspath(__file__))
C=json.load(open(os.path.join(here,'certificate_numerical.json'))); T=json.load(open(os.path.join(here,sys.argv[1] if len(sys.argv)>1 else 'certificate_tight.json')))
d=C['d']; K=C['KMAX']; N=8; ESTAR=C['target_E_ustar']; tlo,thi=-1.0,0.5373
a0,a1,lam=T['a0'],T['a1'],T['lam']; F=[np.array(T['F'][str(k)]) for k in range(K+1)]; V=[np.array(C['kernel_vectors'][str(k)]) for k in range(K+1)]
def h(t): return 1.0/np.sqrt(2-2*t)
def Fun(x,y,z): return sum(np.sum(F[k]*Sk(k,d,x,y,z)) for k in range(K+1))
B=(N*N*a0-N*(a0+a1)-N*Fun(1.,1.,1.))/2
print(f"bound = {B:.10f}   E(u*) = {ESTAR:.10f}   diff = {B-ESTAR:+.2e}")
print("kernel residuals |F_k v_k|/|v_k|:",[f"{np.linalg.norm(F[k]@V[k])/np.linalg.norm(V[k]):.1e}" for k in range(K+1)])
print("min eig of F_k on v^perp:",[f"{np.sort(np.linalg.eigvalsh(F[k]))[1]:.2e}" for k in range(K+1)])
def P(s): t=1-s*s/2; return (1-18*lam)-s*(a0+a1*t+3*Fun(1.,t,t))
tt=np.linspace(tlo,thi,20000); pv=np.array([P(np.sqrt(2-2*t)) for t in tt])
print(f"pair polynomial on 20000 pts: min = {pv.min():+.3e} at t={tt[pv.argmin()]:.4f}")
for t in C['antiprism_inner_products']:
    s=np.sqrt(2-2*t); e=1e-6; print(f"   at antiprism s={s:.5f}: P={P(s):+.1e}  P'={(P(s+e)-P(s-e))/(2*e):+.1e}")
def Tf(x,y,z): return lam*(h(x)+h(y)+h(z))-Fun(x,y,z)
ng=int(sys.argv[2]) if len(sys.argv)>2 else 80
g=np.linspace(tlo,thi,ng); tri=np.array([(u,v,t) for u in g for v in g if v>=u for t in g if t>=v and 1+2*u*v*t-u*u-v*v-t*t>=-1e-12])
tv=np.array([Tf(*x) for x in tri])
print(f"triangle slack on {len(tri)} pts ({ng}/axis): min = {tv.min():+.3e} at {tri[tv.argmin()].round(3)}")
for tr in C['antiprism_triangle_types']:
    e=1e-6; gr=[(Tf(*(np.array(tr)+e*np.eye(3)[i]))-Tf(*(np.array(tr)-e*np.eye(3)[i])))/(2*e) for i in range(3)]
    print(f"   at antiprism {tuple(round(x,4) for x in tr)}: T={Tf(*tr):+.1e}  |grad|={np.linalg.norm(gr):.1e}")

loc=np.arange(-0.08,0.0801,0.004); worst=(1e9,None)
for tr in C['antiprism_triangle_types']:
    for dx in loc:
        for dy in loc:
            for dz in loc:
                q=(tr[0]+dx,tr[1]+dy,tr[2]+dz)
                if all(tlo<=x<=thi for x in q) and 1+2*q[0]*q[1]*q[2]-q[0]**2-q[1]**2-q[2]**2>=0:
                    val=Tf(*q)
                    if val<worst[0]: worst=(val,q)
print(f"LOCAL fine check (spacing 0.004 within 0.08 of each touching type): min T = {worst[0]:+.3e} at {tuple(round(x,4) for x in worst[1])}")
