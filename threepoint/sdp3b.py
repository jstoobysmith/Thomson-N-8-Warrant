import numpy as np, cvxpy as cp, sys, time, pickle
from numpy.polynomial import legendre as L
sys.path.insert(0,'/private/tmp/claude-502/-Users-js4814-Documents-GitHub-MyComandCenter/0962e486-bbae-4fbd-bb57-0b9929536462/scratchpad')
from bv import Sk
TARGET=19.6752878612; N=8
def h(t): return 1.0/np.sqrt(2-2*t)
def leg(D,t): return np.array([L.legval(t,[0]*j+[1]) for j in range(D+1)])
def tri_grid(tmax,ng):
    g=np.linspace(-1,tmax,ng); out=[]
    for u in g:
        for v in g[g>=u]:
            for t in g[g>=v]:
                if 1+2*u*v*t-u*u-v*v-t*t>=-1e-12: out.append((u,v,t))
    return np.array(out)

def solve(D,d,tmax,nt,ng,tag):
    t0=time.time()
    tg=np.linspace(-1,tmax,nt); tri=tri_grid(tmax,ng)
    a=cp.Variable(D+1); Fs=[cp.Variable((d-k+1,d-k+1),PSD=True) for k in range(d+1)]
    cons=[a[1:]>=0]
    F111=sum(cp.sum(cp.multiply(Fs[k],Sk(k,d,1.,1.,1.))) for k in range(d+1))
    obj=(N*N*a[0]-N*cp.sum(a)-N*F111)/2
    for t in tg:
        F1=sum(cp.sum(cp.multiply(Fs[k],Sk(k,d,1.,t,t))) for k in range(d+1))
        cons.append(leg(D,t)@a+3*F1<=h(t))
    for (u,v,t) in tri:
        cons.append(sum(cp.sum(cp.multiply(Fs[k],Sk(k,d,u,v,t))) for k in range(d+1))<=0)
    prob=cp.Problem(cp.Maximize(obj),cons)
    prob.solve(solver=cp.CLARABEL,tol_gap_abs=1e-10,tol_gap_rel=1e-10,tol_feas=1e-10,max_iter=500)
    av=a.value; Fv=[F.value for F in Fs]
    print(f"[{tag}] D={D} d={d} tmax={tmax} nt={nt} ng={ng} (#tri={len(tri)}): status={prob.status}  bound={prob.value:.7f}  ({time.time()-t0:.0f}s)",flush=True)
    # ---- post-hoc verification on MUCH finer grids ----
    def f(t): return leg(D,t)@av
    def F(u,v,t): return sum(np.sum(Fv[k]*Sk(k,d,u,v,t)) for k in range(d+1))
    tf=np.linspace(-1,tmax,20000)
    c1=np.array([h(t)-f(t)-3*F(1.,t,t) for t in tf])
    trif=tri_grid(tmax,70)
    c2=np.array([F(u,v,t) for (u,v,t) in trif])
    Fv111=F(1.,1.,1.)
    bound=(N*N*av[0]-N*av.sum()-N*Fv111)/2
    print(f"[{tag}]   verify: min over 20000 t of  h-f-3F(1,t,t) = {c1.min():+.3e}  (need >=0)  at t={tf[c1.argmin()]:.4f}",flush=True)
    print(f"[{tag}]   verify: max over {len(trif)} triangles of F(u,v,t) = {c2.max():+.3e}  (need <=0)  at {trif[c2.argmax()].round(3)}",flush=True)
    print(f"[{tag}]   recomputed bound = {bound:.7f}   gap to target = {TARGET-bound:+.7f}",flush=True)
    pickle.dump(dict(D=D,d=d,tmax=tmax,a=av,F=Fv,bound=bound),open(f'sol_{tag}.pkl','wb'))
    return bound

if __name__=="__main__":
    D,d,tmax,nt,ng,tag=int(sys.argv[1]),int(sys.argv[2]),float(sys.argv[3]),int(sys.argv[4]),int(sys.argv[5]),sys.argv[6]
    solve(D,d,tmax,nt,ng,tag)
