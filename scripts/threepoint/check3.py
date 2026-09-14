import numpy as np, pickle, sys
from numpy.polynomial import legendre as L
sys.path.insert(0,'/private/tmp/claude-502/-Users-js4814-Documents-GitHub-MyComandCenter/0962e486-bbae-4fbd-bb57-0b9929536462/scratchpad')
from bv import Sk
S=pickle.load(open('/private/tmp/claude-502/-Users-js4814-Documents-GitHub-MyComandCenter/0962e486-bbae-4fbd-bb57-0b9929536462/scratchpad/sol_A.pkl','rb'))
D,d,av,Fv,B=S['D'],S['d'],S['a'],S['F'],S['bound']; N=8
def h(t): return 1.0/np.sqrt(2-2*t)
def f(t): return np.array([L.legval(t,[0]*j+[1]) for j in range(D+1)])@av
def F(u,v,t): return sum(np.sum(Fv[k]*Sk(k,d,u,v,t)) for k in range(d+1))
def decompose(X):
    G=X@X.T; E=sum(h(G[i,j]) for i in range(N) for j in range(i+1,N))
    Mk=[sum(L.legval(G[i,j],[0]*k+[1]) for i in range(N) for j in range(N)) for k in range(D+1)]
    design=sum(av[k]*Mk[k] for k in range(1,D+1))
    BV=0.0
    for k in range(d+1):
        M=np.zeros((d-k+1,d-k+1))
        for i in range(N):
            for j in range(N):
                for l in range(N): M+=Sk(k,d,G[i,j],G[i,l],G[j,l])
        BV+=np.sum(Fv[k]*M)
    dist=-sum(F(G[i,j],G[i,l],G[j,l]) for i in range(N) for j in range(N) for l in range(N) if len({i,j,l})==3)
    slack=sum(h(G[i,j])-f(G[i,j])-3*F(1.,G[i,j],G[i,j]) for i in range(N) for j in range(N) if i!=j)
    # identity: 2E = 2B + design + BV + dist + slack   where BV := sum_{ijk} F >= 0 by Bachoc-Vallentin
    #   note BV = 8F(1,1,1) + 3*sum_{i!=j}F(1,t,t) + sum_dist F,  so this is the same bookkeeping as before
    return E, design, BV, dist, slack, 2*E-(2*B+design+BV+dist+slack)
u=0.31408936726; hh=np.sqrt(u); r=np.sqrt(1-u); s=r/np.sqrt(2)
AP=np.array([[r,0,hh],[0,r,hh],[-r,0,hh],[0,-r,hh],[s,s,-hh],[-s,s,-hh],[-s,-s,-hh],[s,-s,-hh]])
rng=np.random.default_rng(1)
print(f"{'config':12s} {'E':>10s} {'design':>9s} {'BVtotal':>9s} {'-sumF':>9s} {'slack':>9s} {'residual':>10s}  all>=0?  E>=B?")
cfgs=[('antiprism',AP)]
while len(cfgs)<6:
    X=rng.normal(size=(8,3)); X/=np.linalg.norm(X,axis=1,keepdims=True)
    G=X@X.T; np.fill_diagonal(G,-1)
    if G.max()<=0.537: cfgs.append(('random',X))
for nm,X in cfgs:
    E,de,bv,di,sl,res=decompose(X)
    print(f"{nm:12s} {E:10.6f} {de:9.5f} {bv:9.5f} {di:9.5f} {sl:9.5f} {res:+10.2e}  {all(v>=-1e-6 for v in (de,bv,di,sl))}   {E>=B-1e-9}")
print(f"\n(B = {B:.6f}; residual must be ~0 for the identity to hold; the four terms must be >= 0)")
