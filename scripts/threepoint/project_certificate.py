"""Step 2 of the finishing plan: project the numerical certificate onto the exact kernel constraints
F_k v_k = 0, and check (a) PSD margin on v_k^perp, (b) double zeros of the pair polynomial,
(c) vanishing gradient of the triangle slack at the antiprism triangle types, (d) the bound."""
import numpy as np, json, sys, os
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from bv import Sk
C=json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'certificate_numerical.json')))
d=C['d']; K=C['KMAX']; a0,a1,lam=C['a0'],C['a1'],C['lam']; N=8; TARGET=C['target_E_ustar']
F=[np.array(C['F'][str(k)]) for k in range(K+1)]; V=[np.array(C['kernel_vectors'][str(k)]) for k in range(K+1)]
def h(t): return 1.0/np.sqrt(2-2*t)
print("(a) project F_k -> P F_k P with P = I - v v^T/|v|^2, and PSD margin on v^perp:")
Fp=[]
for k in range(K+1):
    v=V[k]/np.linalg.norm(V[k]); P=np.eye(len(v))-np.outer(v,v); Fk=P@F[k]@P; Fk=(Fk+Fk.T)/2; Fp.append(Fk)
    ev=np.linalg.eigvalsh(Fk); print(f"   k={k}: |F_k - PF_kP| = {np.abs(F[k]-Fk).max():.2e}   eigenvalues on v^perp: min={np.sort(ev)[1]:.3e}  (kernel eig {ev[0]:+.1e})")
def Fun(Fs,x,y,z): return sum(np.sum(Fs[k]*Sk(k,d,x,y,z)) for k in range(K+1))
B0=(N*N*a0-N*(a0+a1)-N*Fun(F,1.,1.,1.))/2; B1=(N*N*a0-N*(a0+a1)-N*Fun(Fp,1.,1.,1.))/2
print(f"\n(d) bound before projection {B0:.9f}, after {B1:.9f}, E(u*) = {TARGET:.9f}")
print("\n(b) pair polynomial  P(s) = (1-18 lam) - s[a0 + a1 t + 3F(1,t,t)],  t = 1 - s^2/2, at the antiprism distances (value, derivative):")
def Ps(s,Fs): t=1-s*s/2; return (1-18*lam)-s*(a0+a1*t+3*Fun(Fs,1.,t,t))
for t in C['antiprism_inner_products']:
    s=np.sqrt(2-2*t); e=1e-6
    print(f"   s={s:.6f}: P={Ps(s,Fp):+.2e}   P'={(Ps(s+e,Fp)-Ps(s-e,Fp))/(2*e):+.2e}")
print("\n(c) triangle slack  T = lam(h(u)+h(v)+h(t)) - F(u,v,t) at the antiprism triangle types (value, |gradient|):")
def T(x,y,z,Fs): return lam*(h(x)+h(y)+h(z))-Fun(Fs,x,y,z)
for tr in C['antiprism_triangle_types']:
    e=1e-6; g=[(T(*(np.array(tr)+e*np.eye(3)[i]),Fp)-T(*(np.array(tr)-e*np.eye(3)[i]),Fp))/(2*e) for i in range(3)]
    print(f"   {tuple(round(x,4) for x in tr)}: T={T(*tr,Fp):+.2e}  |grad|={np.linalg.norm(g):.2e}")
