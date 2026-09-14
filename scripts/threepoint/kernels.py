import numpy as np, pickle, sys
sys.path.insert(0,'/private/tmp/claude-502/-Users-js4814-Documents-GitHub-MyComandCenter/0962e486-bbae-4fbd-bb57-0b9929536462/scratchpad')
from bv import Sk
d=8; N=8
u=0.31408936788920186517709977; hh=np.sqrt(u); r=np.sqrt(1-u); s=r/np.sqrt(2)
AP=np.array([[r,0,hh],[0,r,hh],[-r,0,hh],[0,-r,hh],[s,s,-hh],[-s,s,-hh],[-s,-s,-hh],[s,-s,-hh]]); G=AP@AP.T
S=pickle.load(open('sharp_RS8.pkl','rb')); Fv=S['F']
print("M_k(antiprism) := sum_{i,j,l} S_k(t_ij,t_il,t_jl)   (PSD by Bachoc-Vallentin)")
print(f"{'k':>2s} {'size':>5s} {'rank(M_k)':>10s} {'eigs of M_k':>40s}   <F_k, M_k>   F_k kernel dim")
for k in range(d+1):
    M=np.zeros((d-k+1,d-k+1))
    for i in range(N):
        for j in range(N):
            for l in range(N): M+=Sk(k,d,G[i,j],G[i,l],G[j,l])
    M=(M+M.T)/2; ev=np.linalg.eigvalsh(M); rk=int((ev>1e-8*max(1,ev.max())).sum())
    evF=np.linalg.eigvalsh(Fv[k]); kd=int((evF<1e-7).sum())
    print(f"{k:2d} {d-k+1:5d} {rk:10d} {np.array2string(ev[-3:],precision=3):>40s}   {np.sum(Fv[k]*M):+.2e}   {kd}")
    if rk==1:
        w,V=np.linalg.eigh(M); v=V[:,-1]; v=v/v[np.argmax(abs(v))]
        print(f"     range vector (normalised): {np.round(v,6)}")
        print(f"     F_k v = {np.round(Fv[k]@v,7)}  (should be ~0: complementary slackness)")
