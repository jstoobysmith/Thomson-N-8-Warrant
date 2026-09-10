import numpy as np, cvxpy as cp, sys, time
from numpy.polynomial import legendre as L
sys.path.insert(0,'/private/tmp/claude-502/-Users-js4814-Documents-GitHub-MyComandCenter/0962e486-bbae-4fbd-bb57-0b9929536462/scratchpad')
from bv import Sk
from sdp3b import leg, h
N=8; EMAX=19.6753
def tri_grid2(tlo,thi,ng):
    g=np.linspace(tlo,thi,ng); out=[]
    for u in g:
        for v in g[g>=u]:
            for t in g[g>=v]:
                if 1+2*u*v*t-u*u-v*v-t*t>=-1e-12: out.append((u,v,t))
    return np.array(out)
def forced(D,d,tlo,thi,side,t0,nt=500,ng=26):
    """max B + delta, with slack h-f-3F(1,t,t) >= delta on the forced side ([t0,thi] if side='hi', [tlo,t0] if 'lo')."""
    t1=time.time()
    tg=np.linspace(tlo,thi,nt); tri=tri_grid2(tlo,thi,ng)
    a=cp.Variable(D+1); Fs=[cp.Variable((d-k+1,d-k+1),PSD=True) for k in range(d+1)]; delta=cp.Variable()
    cons=[a[1:]>=0, delta>=0]
    F111=sum(cp.sum(cp.multiply(Fs[k],Sk(k,d,1.,1.,1.))) for k in range(d+1))
    B=(N*N*a[0]-N*cp.sum(a)-N*F111)/2
    for t in tg:
        F1=sum(cp.sum(cp.multiply(Fs[k],Sk(k,d,1.,t,t))) for k in range(d+1))
        forcedhere=(t>=t0) if side=='hi' else (t<=t0)
        cons.append(leg(D,t)@a+3*F1+(delta if forcedhere else 0)<=h(t))
    for (u,v,t) in tri:
        cons.append(sum(cp.sum(cp.multiply(Fs[k],Sk(k,d,u,v,t))) for k in range(d+1))<=0)
    prob=cp.Problem(cp.Maximize(B+delta),cons)
    prob.solve(solver=cp.CLARABEL,tol_gap_abs=1e-9,tol_gap_rel=1e-9,tol_feas=1e-9,max_iter=400)
    return prob.value, B.value, delta.value, time.time()-t1
if __name__=="__main__":
    side=sys.argv[1]; tlo=float(sys.argv[2]); thi=float(sys.argv[3])
    t0s=[float(x) for x in sys.argv[4:]]
    print(f"forced pair on side={side}, current range t in [{tlo},{thi}]; need B+delta > {EMAX}")
    for t0 in t0s:
        val,Bv,dv,dt=forced(16,10,tlo,thi,side,t0)
        ok=val>EMAX
        print(f"   t0={t0:+.3f} (s={np.sqrt(2-2*t0):.4f}):  B={Bv:.6f}  delta={dv:.6f}  B+delta={val:.6f}  {'EXCLUDES pairs beyond t0' if ok else '-'}  ({dt:.0f}s)",flush=True)
