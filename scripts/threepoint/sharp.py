import numpy as np, cvxpy as cp, sys, time, pickle
sys.path.insert(0,'/private/tmp/claude-502/-Users-js4814-Documents-GitHub-MyComandCenter/0962e486-bbae-4fbd-bb57-0b9929536462/scratchpad')
from bv import Sk
from sdp3b import leg, h
from force3 import tri_grid2
N=8; TARGET=19.6752878612
u=0.31408936788920186517709977; hh=np.sqrt(u); r=np.sqrt(1-u); s=r/np.sqrt(2)
AP=np.array([[r,0,hh],[0,r,hh],[-r,0,hh],[0,-r,hh],[s,s,-hh],[-s,s,-hh],[-s,-s,-hh],[s,-s,-hh]]); G=AP@AP.T
AP_t=sorted(set(np.round(G[np.triu_indices(8,1)],12)))
AP_tri=sorted(set(tuple(sorted((G[i,j],G[i,k],G[j,k]))) for i in range(8) for j in range(i+1,8) for k in range(j+1,8)))
def run(D,d,tlo,thi,nt,ng,tag,ngver=80):
    t0=time.time(); tg=np.concatenate([np.linspace(tlo,thi,nt),AP_t]); tri=np.vstack([tri_grid2(tlo,thi,ng),np.array(AP_tri)])
    a=cp.Variable(D+1); Fs=[cp.Variable((d-k+1,d-k+1),PSD=True) for k in range(d+1)]; lam=cp.Variable()
    cons=[a[1:]>=0,lam>=0,lam<=1/18]
    F111=sum(cp.sum(cp.multiply(Fs[k],Sk(k,d,1.,1.,1.))) for k in range(d+1))
    B=(N*N*a[0]-N*cp.sum(a)-N*F111)/2
    for t in tg:
        F1=sum(cp.sum(cp.multiply(Fs[k],Sk(k,d,1.,t,t))) for k in range(d+1)); cons.append(leg(D,t)@a+3*F1<=(1-18*lam)*h(t))
    for (uu,vv,tt) in tri:
        cons.append(sum(cp.sum(cp.multiply(Fs[k],Sk(k,d,uu,vv,tt))) for k in range(d+1))<=lam*(h(uu)+h(vv)+h(tt)))
    p=cp.Problem(cp.Maximize(B),cons); p.solve(solver=cp.CLARABEL,tol_gap_abs=1e-10,tol_gap_rel=1e-10,tol_feas=1e-10,max_iter=600)
    av=a.value; Fv=[F.value for F in Fs]; lv=lam.value
    print(f"[{tag}] D={D} d={d} ng={ng}+antiprism: bound={p.value:.8f}  E(u*)={TARGET:.8f}  E(u*)-bound={TARGET-p.value:+.2e}  lambda={lv:.6f} ({time.time()-t0:.0f}s)",flush=True)
    def f(t): return leg(D,t)@av
    def F(x,y,z): return sum(np.sum(Fv[k]*Sk(k,d,x,y,z)) for k in range(d+1))
    trif=tri_grid2(tlo,thi,ngver); v2=np.array([F(*x)-lv*sum(h(y) for y in x) for x in trif])
    tf=np.linspace(tlo,thi,20000); v1=np.array([f(t)+3*F(1.,t,t)-(1-18*lv)*h(t) for t in tf])
    print(f"[{tag}]   fine-grid verification: pair-constraint max violation {v1.max():+.2e};  triangle-constraint max violation {v2.max():+.2e} at {trif[v2.argmax()].round(3)}",flush=True)
    print(f"[{tag}]   at antiprism: pair slacks {[f'{(1-18*lv)*h(t)-f(t)-3*F(1.,t,t):+.1e}' for t in AP_t]}",flush=True)
    print(f"[{tag}]   at antiprism: tri  slacks {[f'{lv*sum(h(y) for y in x)-F(*x):+.1e}' for x in AP_tri]}",flush=True)
    pickle.dump(dict(D=D,d=d,tlo=tlo,thi=thi,a=av,F=Fv,lam=lv,bound=p.value),open(f'sharp_{tag}.pkl','wb'))
if __name__=="__main__":
    run(int(sys.argv[1]),int(sys.argv[2]),-0.9372,0.4395,int(sys.argv[3]),int(sys.argv[4]),sys.argv[5])
