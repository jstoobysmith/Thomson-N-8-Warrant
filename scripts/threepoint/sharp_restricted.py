import numpy as np, cvxpy as cp, sys, time, pickle
sys.path.insert(0,'/private/tmp/claude-502/-Users-js4814-Documents-GitHub-MyComandCenter/0962e486-bbae-4fbd-bb57-0b9929536462/scratchpad')
from bv import Sk
from sdp3b import leg, h
from force3 import tri_grid2
from sharp import AP_t, AP_tri
N=8; TARGET=19.6752878612; SUPPORT=[1,2,3,4,7,12]
def run(D,d,tlo,thi,nt,ng,tag):
    t0=time.time(); tg=np.concatenate([np.linspace(tlo,thi,nt),AP_t]); tri=np.vstack([tri_grid2(tlo,thi,ng),np.array(AP_tri)])
    a=cp.Variable(D+1); Fs=[cp.Variable((d-k+1,d-k+1),PSD=True) for k in range(d+1)]; lam=cp.Variable()
    cons=[a[1:]>=0,lam>=0,lam<=1/18]+[a[k]==0 for k in range(1,D+1) if k not in SUPPORT]
    F111=sum(cp.sum(cp.multiply(Fs[k],Sk(k,d,1.,1.,1.))) for k in range(d+1))
    B=(N*N*a[0]-N*cp.sum(a)-N*F111)/2
    for t in tg:
        F1=sum(cp.sum(cp.multiply(Fs[k],Sk(k,d,1.,t,t))) for k in range(d+1)); cons.append(leg(D,t)@a+3*F1<=(1-18*lam)*h(t))
    for (uu,vv,tt) in tri:
        cons.append(sum(cp.sum(cp.multiply(Fs[k],Sk(k,d,uu,vv,tt))) for k in range(d+1))<=lam*(h(uu)+h(vv)+h(tt)))
    p=cp.Problem(cp.Maximize(B),cons); p.solve(solver=cp.CLARABEL,tol_gap_abs=1e-10,tol_gap_rel=1e-10,tol_feas=1e-10,max_iter=600)
    av=a.value; Fv=[F.value for F in Fs]; lv=lam.value
    print(f"[{tag}] D={D} d={d} Legendre support {SUPPORT}: bound={p.value:.8f}  E(u*)-bound={TARGET-p.value:+.2e}  lambda={lv:.7f} ({time.time()-t0:.0f}s)",flush=True)
    print(f"[{tag}]   a_k = { {k:round(float(av[k]),7) for k in range(D+1) if abs(av[k])>1e-9} }",flush=True)
    for k in range(d+1):
        ev=np.linalg.eigvalsh(Fv[k]); print(f"[{tag}]   F_{k} ({d-k+1}x{d-k+1}): trace={np.trace(Fv[k]):.3e}  eigenvalues>1e-7: {int((ev>1e-7).sum())}   max={ev.max():.3e}",flush=True)
    pickle.dump(dict(D=D,d=d,tlo=tlo,thi=thi,a=av,F=Fv,lam=lv,bound=p.value,support=SUPPORT),open(f'sharp_{tag}.pkl','wb'))
run(12,8,-1.0,0.537,1500,44,'RS8')
