import numpy as np, cvxpy as cp, sys, time, pickle
sys.path.insert(0,'/private/tmp/claude-502/-Users-js4814-Documents-GitHub-MyComandCenter/0962e486-bbae-4fbd-bb57-0b9929536462/scratchpad')
from bv import Sk
from sdp3b import leg, h
from force3 import tri_grid2
N=8; TARGET=19.6752878612
def gen_bound(D,d,tlo,thi,nt=500,ng=26,use_lambda=True,tag=''):
    t0=time.time(); tg=np.linspace(tlo,thi,nt); tri=tri_grid2(tlo,thi,ng)
    a=cp.Variable(D+1); Fs=[cp.Variable((d-k+1,d-k+1),PSD=True) for k in range(d+1)]
    lam=cp.Variable() if use_lambda else 0.0
    cons=[a[1:]>=0]+([lam>=0, lam<=1.0/18] if use_lambda else [])
    F111=sum(cp.sum(cp.multiply(Fs[k],Sk(k,d,1.,1.,1.))) for k in range(d+1))
    B=(N*N*a[0]-N*cp.sum(a)-N*F111)/2
    for t in tg:
        F1=sum(cp.sum(cp.multiply(Fs[k],Sk(k,d,1.,t,t))) for k in range(d+1))
        cons.append(leg(D,t)@a+3*F1<=(1-18*lam)*h(t))
    for (u,v,t) in tri:
        Fu=sum(cp.sum(cp.multiply(Fs[k],Sk(k,d,u,v,t))) for k in range(d+1))
        cons.append(Fu<=lam*(h(u)+h(v)+h(t)))
    p=cp.Problem(cp.Maximize(B),cons)
    p.solve(solver=cp.CLARABEL,tol_gap_abs=1e-9,tol_gap_rel=1e-9,tol_feas=1e-9,max_iter=500)
    lv=lam.value if use_lambda else 0.0
    print(f"{tag} D={D} d={d} range=[{tlo:+.3f},{thi:+.3f}] lambda={'on' if use_lambda else 'off'}: bound={p.value:.7f}  lambda*={lv:.6f}  gap={TARGET-p.value:+.7f}  ({time.time()-t0:.0f}s)",flush=True)
    pickle.dump(dict(D=D,d=d,tlo=tlo,thi=thi,a=a.value,F=[F.value for F in Fs],lam=lv,bound=p.value),open(f'solg_{tag}.pkl','wb'))
    return p.value
if __name__=="__main__":
    tlo,thi=-0.9372,0.4395
    gen_bound(16,10,tlo,thi,use_lambda=False,tag='L0')
    gen_bound(16,10,tlo,thi,use_lambda=True,tag='L1')
