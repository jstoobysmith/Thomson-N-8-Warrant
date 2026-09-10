"""Ballpark of M = max |D^3 T| on Delta ∩ box (finite differences, double precision) and the implied
radius rho = 3*eta/M of the Hessian-controlled ball at each touching type (eta = min Hessian eigenvalue)."""
import numpy as np, json, sys, os, itertools
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from bv import Sk
here=os.path.dirname(os.path.abspath(__file__))
C=json.load(open(os.path.join(here,'certificate_numerical.json'))); Tc=json.load(open(os.path.join(here,sys.argv[1] if len(sys.argv)>1 else 'certificate_pd.json')))
d=C['d']; K=C['KMAX']; lam=Tc['lam']; F=[np.array(Tc['F'][str(k)]) for k in range(K+1)]; tlo,thi=-1.0,0.537
def h(t): return 1.0/np.sqrt(2-2*t)
def T(p): return lam*(h(p[0])+h(p[1])+h(p[2]))-sum(np.sum(F[k]*Sk(k,d,*p)) for k in range(K+1))
def d3(p,e=2e-3):
    """all third partials via central differences; returns max abs"""
    m=0.0
    for a,b,c in itertools.combinations_with_replacement(range(3),3):
        # generic third mixed difference
        tot=0.0
        for sa in (1,-1):
            for sb in (1,-1):
                for sc in (1,-1):
                    q=np.array(p,float); q[a]+=sa*e; q[b]+=sb*e; q[c]+=sc*e
                    tot+=sa*sb*sc*T(q)
        m=max(m,abs(tot/(8*e**3)))
    return m
rng=np.random.default_rng(0); pts=[]
while len(pts)<400:
    p=rng.uniform(tlo+0.02,thi-0.02,3)
    if 1+2*p[0]*p[1]*p[2]-p@p>=0.02: pts.append(p)
M=max(d3(p) for p in pts)
print(f"estimated max |D^3 T| over {len(pts)} interior sample points: M ≈ {M:.3f}")
for tr in C['antiprism_triangle_types']:
    print(f"   near touching type {tuple(round(x,3) for x in tr)}: |D^3 T| ≈ {d3(tr):.3f}")
eta=float(sys.argv[2]) if len(sys.argv)>2 else 1e-3
print(f"\nwith Hessian margin eta={eta}: controlled-ball radius rho = 3*eta/M ≈ {3*eta/M:.2e}")
print("(inside the ball  T >= eta/2 |d|^2 - M/6 |d|^3 > 0;  outside, interval branch-and-bound must certify T > 0)")
