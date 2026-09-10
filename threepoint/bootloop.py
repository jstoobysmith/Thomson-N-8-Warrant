import numpy as np, sys, time, pickle
sys.path.insert(0,'/private/tmp/claude-502/-Users-js4814-Documents-GitHub-MyComandCenter/0962e486-bbae-4fbd-bb57-0b9929536462/scratchpad')
from force3 import forced
import cvxpy as cp
from bv import Sk
from sdp3b import leg, h
from force3 import tri_grid2
N=8; EMAX=19.6753; TARGET=19.6752878612
D,d=16,10
def main_bound(tlo,thi,nt=500,ng=26):
    tg=np.linspace(tlo,thi,nt); tri=tri_grid2(tlo,thi,ng)
    a=cp.Variable(D+1); Fs=[cp.Variable((d-k+1,d-k+1),PSD=True) for k in range(d+1)]
    cons=[a[1:]>=0]
    F111=sum(cp.sum(cp.multiply(Fs[k],Sk(k,d,1.,1.,1.))) for k in range(d+1))
    B=(N*N*a[0]-N*cp.sum(a)-N*F111)/2
    for t in tg:
        F1=sum(cp.sum(cp.multiply(Fs[k],Sk(k,d,1.,t,t))) for k in range(d+1))
        cons.append(leg(D,t)@a+3*F1<=h(t))
    for (u,v,t) in tri:
        cons.append(sum(cp.sum(cp.multiply(Fs[k],Sk(k,d,u,v,t))) for k in range(d+1))<=0)
    p=cp.Problem(cp.Maximize(B),cons); p.solve(solver=cp.CLARABEL,tol_gap_abs=1e-9,tol_gap_rel=1e-9,tol_feas=1e-9,max_iter=400)
    return p.value
def shrink(side,tlo,thi,lo,hi,iters=5):
    """bisect for the extreme t0 on `side` that is still excluded (B+delta>EMAX). returns new endpoint."""
    # 'hi': search t0 in [lo,hi]; excluded(t0) is monotone: larger t0 easier. find smallest excluded.
    # 'lo': search t0 in [lo,hi]; smaller t0 easier. find largest excluded.
    for _ in range(iters):
        mid=(lo+hi)/2
        val,_,_,_=forced(D,d,tlo,thi,side,mid)
        if val>EMAX:
            if side=='hi': hi=mid
            else: lo=mid
        else:
            if side=='hi': lo=mid
            else: hi=mid
    return hi if side=='hi' else lo    # the last point verified excluded (conservative)
tlo,thi=-1.0,0.537
for it in range(8):
    t0=time.time()
    B=main_bound(tlo,thi)
    print(f"round {it}: range t in [{tlo:+.4f},{thi:+.4f}]  (dist in [{np.sqrt(2-2*thi):.4f},{np.sqrt(2-2*tlo):.4f}])   3-pt bound B = {B:.7f}   gap to target = {TARGET-B:+.7f}",flush=True)
    if B>=TARGET: print("   *** BOUND REACHES THE CONJECTURED MINIMUM ***",flush=True); break
    nthi=shrink('hi',tlo,thi,0.3141,thi)
    ntlo=shrink('lo',tlo,thi,tlo,-0.7991)
    print(f"   forced-pair shrink: thi {thi:+.4f} -> {nthi:+.4f},  tlo {tlo:+.4f} -> {ntlo:+.4f}   ({time.time()-t0:.0f}s)",flush=True)
    if abs(nthi-thi)<1e-4 and abs(ntlo-tlo)<1e-4: print("   converged (no further shrink)",flush=True); break
    thi,tlo=nthi,ntlo
