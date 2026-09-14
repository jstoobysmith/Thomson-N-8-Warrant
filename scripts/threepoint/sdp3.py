import numpy as np, cvxpy as cp, sys, time
from numpy.polynomial import legendre as L
sys.path.insert(0,'/private/tmp/claude-502/-Users-js4814-Documents-GitHub-MyComandCenter/0962e486-bbae-4fbd-bb57-0b9929536462/scratchpad')
from bv import Sk
TARGET=19.6752878612; N=8
def h(t): return 1.0/np.sqrt(2-2*t)
def leg(D,t):
    return np.array([L.legval(t,[0]*j+[1]) for j in range(D+1)])

def three_point_bound(D,d,tmax,nt=400,ng=22,verbose=False):
    t0=time.time()
    # --- constraint 1 grid ---
    tg=np.linspace(-1,tmax,nt)
    # --- constraint 2 grid (triangles, u<=v<=t, in Delta) ---
    g=np.linspace(-1,tmax,ng); tri=[]
    for u in g:
        for v in g:
            if v<u: continue
            for t in g:
                if t<v: continue
                if 1+2*u*v*t-u*u-v*v-t*t>=-1e-12: tri.append((u,v,t))
    tri=np.array(tri)
    # --- variables ---
    a=cp.Variable(D+1)
    Fs=[cp.Variable((d-k+1,d-k+1),PSD=True) for k in range(d+1)]
    cons=[a[1:]>=0]
    # objective pieces
    S111=[Sk(k,d,1.0,1.0,1.0) for k in range(d+1)]
    F111=sum(cp.sum(cp.multiply(Fs[k],S111[k])) for k in range(d+1))
    obj=(N*N*a[0]-N*cp.sum(a)-N*F111)/2
    # constraint 1: f(t)+3F(1,t,t) <= h(t)
    P=np.array([leg(D,t) for t in tg])          # (nt, D+1)
    S1tt=[[Sk(k,d,1.0,t,t) for k in range(d+1)] for t in tg]
    for i,t in enumerate(tg):
        F1=sum(cp.sum(cp.multiply(Fs[k],S1tt[i][k])) for k in range(d+1))
        cons.append(P[i]@a+3*F1<=h(t))
    # constraint 2: F(u,v,t) <= 0 on triangles
    for (u,v,t) in tri:
        Fuvt=sum(cp.sum(cp.multiply(Fs[k],Sk(k,d,u,v,t))) for k in range(d+1))
        cons.append(Fuvt<=0)
    prob=cp.Problem(cp.Maximize(obj),cons)
    prob.solve(solver=cp.CLARABEL,verbose=verbose)
    return prob.value, len(tri), time.time()-t0

print(f"three-point (Cohn-Woo-type) SDP bound for N=8 Coulomb.  target E(u*) = {TARGET:.7f}\n")
print(f"{'D_lp':>5s} {'d_3pt':>6s} {'t_max':>7s} {'#tri':>6s} {'bound':>12s} {'vs LP 19.6478':>15s} {'time':>6s}")
for D,d,tmax in [(12,0,1.0),(12,4,1.0),(12,6,1.0),(12,8,1.0),(16,8,1.0),(16,8,0.537),(16,10,0.537)]:
    try:
        b,ntri,dt=three_point_bound(D,d,tmax)
        flag='  <-- EXCEEDS LP CEILING' if b>19.6479 else ''
        flag2='  *** REACHES TARGET ***' if b>=TARGET-1e-6 else ''
        print(f"{D:5d} {d:6d} {tmax:7.3f} {ntri:6d} {b:12.7f} {b-19.647792:+15.7f} {dt:6.0f}s{flag}{flag2}",flush=True)
    except Exception as e:
        print(f"{D:5d} {d:6d} {tmax:7.3f}   failed: {e}",flush=True)
