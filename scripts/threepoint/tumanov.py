import numpy as np
from scipy.optimize import minimize
exec(open('/private/tmp/claude-502/-Users-js4814-Documents-GitHub-MyComandCenter/0962e486-bbae-4fbd-bb57-0b9929536462/scratchpad/lp.py').read().split('print("=== plain LP')[0])
iu=np.triu_indices(8,1)
def norm(v):
    X=v.reshape(8,3); return X/np.linalg.norm(X,axis=1,keepdims=True)
def tvals(X): return (X@X.T)[iu]
def Gk(X,k):    # sum_{i<j} (4 - r^2)^k = sum (2+2t)^k     [Tumanov's G_k]
    return float(np.sum((2+2*tvals(X))**k))
def energy(X): 
    d=np.sqrt(2-2*tvals(X)); return float(np.sum(1.0/d))
u=0.31408936726; h=np.sqrt(u); r=np.sqrt(1-u); s=r/np.sqrt(2)
AP=np.array([[r,0,h],[0,r,h],[-r,0,h],[0,-r,h],[s,s,-h],[-s,s,-h],[-s,-s,-h],[s,-s,-h]])
c=1/np.sqrt(3); CUBE=np.array([[a*c,b*c,d*c] for a in(1,-1) for b in(1,-1) for d in(1,-1)])
rng=np.random.default_rng(7)
print("Tumanov-style test for N=8: is the square antiprism the MINIMISER of")
print("sum_{i<j} G_k(r) with G_k(r)=(4-r^2)^k ?   (this is what makes an analytic proof possible)\n")
print(f"{'k':>3s} {'G_k(antiprism)':>18s} {'G_k(global min found)':>22s} {'antiprism optimal?':>20s}")
for k in [1,2,3,4,5,6,8,10]:
    best=np.inf; bx=None
    for _ in range(400):
        r0=minimize(lambda v: Gk(norm(v),k), rng.normal(size=24), method='L-BFGS-B',
                    options=dict(maxiter=40000,ftol=1e-16,gtol=1e-12))
        if r0.fun<best: best, bx = r0.fun, r0.x
    ga=Gk(AP,k)
    ok = abs(ga-best)<1e-7*max(1,abs(ga))
    print(f"{k:3d} {ga:18.9f} {best:22.9f} {('YES' if ok else 'no  (loses by %.6f)'%(ga-best)):>20s}")
print()
print(f"   for reference, G_k(cube):  k=1 {Gk(CUBE,1):.6f}  k=2 {Gk(CUBE,2):.6f}  k=3 {Gk(CUBE,3):.6f}")
print(f"   antiprism is a 3-design? M_1,M_2,M_3 = {[round(float(legvals(3,(AP@AP.T).ravel())[j].sum()),6) for j in (1,2,3)]}")
print(f"   cube      is a 3-design? M_1,M_2,M_3 = {[round(float(legvals(3,(CUBE@CUBE.T).ravel())[j].sum()),6) for j in (1,2,3)]}")
