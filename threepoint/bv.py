import numpy as np
from numpy.polynomial import chebyshev as C, legendre as L
from itertools import permutations

def Qk(k,u,v,t):
    """((1-u^2)(1-v^2))^{k/2} T_k((t-uv)/sqrt((1-u^2)(1-v^2))) as a polynomial (n=3: S^{n-2}=S^1)."""
    c=C.cheb2poly([0]*k+[1])          # T_k monomial coeffs
    w=(1-u*u)*(1-v*v); x=t-u*v
    out=0.0
    for j,cj in enumerate(c):
        if cj!=0 and (k-j)%2==0: out=out+cj*x**j*w**((k-j)//2)
    return out

def Yk(k,d,u,v,t):
    m=d-k+1
    q=Qk(k,u,v,t)
    ui=np.array([u**i for i in range(m)]); vj=np.array([v**j for j in range(m)])
    return np.outer(ui,vj)*q

def Sk(k,d,u,v,t):
    """symmetrised over S_3 acting on (u,v,t)"""
    acc=np.zeros((d-k+1,d-k+1))
    for p in permutations((u,v,t)): acc+=Yk(k,d,*p)
    return acc/6.0

if __name__=="__main__":
    rng=np.random.default_rng(0)
    d=6
    print("Bachoc-Vallentin check: sum_{x,y,z in C} S_k(x.y,x.z,y.z) must be PSD")
    for trial in range(3):
        N=rng.integers(4,10)
        X=rng.normal(size=(N,3)); X/=np.linalg.norm(X,axis=1,keepdims=True)
        G=X@X.T
        worst=1e9
        for k in range(d+1):
            M=np.zeros((d-k+1,d-k+1))
            for i in range(N):
                for j in range(N):
                    for l in range(N):
                        M+=Sk(k,d,G[i,j],G[i,l],G[j,l])
            M=(M+M.T)/2
            worst=min(worst,np.linalg.eigvalsh(M).min())
        print(f"  N={N}: min eigenvalue over k=0..{d} = {worst:+.3e}   {'PSD OK' if worst>-1e-9 else 'FAIL'}")
    # also: S_3 symmetry of S_k
    u,v,t=0.3,-0.2,0.5
    A=Sk(2,d,u,v,t); B=Sk(2,d,t,u,v); print("  symmetric under permutation:", np.allclose(A,B))
