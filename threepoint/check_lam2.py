import numpy as np, pickle, sys
from numpy.polynomial import legendre as L
sys.path.insert(0,'/private/tmp/claude-502/-Users-js4814-Documents-GitHub-MyComandCenter/0962e486-bbae-4fbd-bb57-0b9929536462/scratchpad')
from bv import Sk
S=pickle.load(open('sharp_S10.pkl','rb'))
D,d,av,Fv,lam,B,tlo,thi=S['D'],S['d'],S['a'],S['F'],S['lam'],S['bound'],S['tlo'],S['thi']; N=8
def h(t): return 1.0/np.sqrt(2-2*t)
def f(t): return np.array([L.legval(t,[0]*j+[1]) for j in range(D+1)])@av
def F(x,y,z): return sum(np.sum(Fv[k]*Sk(k,d,x,y,z)) for k in range(d+1))
def terms(X):
    G=X@X.T; E=sum(h(G[i,j]) for i in range(N) for j in range(i+1,N))
    design=sum(av[k]*sum(L.legval(G[i,j],[0]*k+[1]) for i in range(N) for j in range(N)) for k in range(1,D+1))
    BV=0.0
    for k in range(d+1):
        M=np.zeros((d-k+1,d-k+1))
        for i in range(N):
            for j in range(N):
                for l in range(N): M+=Sk(k,d,G[i,j],G[i,l],G[j,l])
        BV+=np.sum(Fv[k]*M)
    tri=sum(lam*(h(G[i,j])+h(G[i,l])+h(G[j,l]))-F(G[i,j],G[i,l],G[j,l]) for i in range(N) for j in range(N) for l in range(N) if len({i,j,l})==3)
    pair=sum((1-18*lam)*h(G[i,j])-f(G[i,j])-3*F(1.,G[i,j],G[i,j]) for i in range(N) for j in range(N) if i!=j)
    return E,design,BV,tri,pair,2*E-(2*B+design+BV+tri+pair)
u=0.31408936788920186517709977; hh=np.sqrt(u); r=np.sqrt(1-u); s=r/np.sqrt(2)
AP=np.array([[r,0,hh],[0,r,hh],[-r,0,hh],[0,-r,hh],[s,s,-hh],[-s,s,-hh],[-s,-s,-hh],[s,-s,-hh]])
rng=np.random.default_rng(3); cfgs=[('antiprism',AP)]
while len(cfgs)<7:
    X=rng.normal(size=(8,3)); X/=np.linalg.norm(X,axis=1,keepdims=True); G=X@X.T; np.fill_diagonal(G,0)
    if G.max()<=thi and G.min()>=tlo: cfgs.append(('random',X))
print(f"identity with lambda:  2E - 2B = design + BV + [lam*sum h - F over distinct triples] + [(1-18lam)h - f - 3F(1,t,t) over pairs]")
print(f"{'config':10s} {'E':>10s} {'design':>9s} {'BV':>9s} {'tri':>9s} {'pair':>9s} {'residual':>10s}")
for nm,X in cfgs:
    E,de,bv,tr,pa,res=terms(X)
    print(f"{nm:10s} {E:10.6f} {de:9.6f} {bv:9.6f} {tr:9.6f} {pa:9.6f} {res:+10.1e}   all>=0: {min(de,bv,tr,pa)>-1e-6}")
