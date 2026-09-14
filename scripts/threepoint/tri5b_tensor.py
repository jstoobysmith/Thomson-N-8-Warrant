"""Coefficient tensor of F(u,v,t) = sum_k <M_k, S_k(u,v,t)>, degree <= 8 in each variable."""
import numpy as np, tri5b_eval as tri
N=9
def pmul(A,B):
    """multiply two 3-var coefficient tensors (numpy arrays)"""
    out=np.zeros((A.shape[0]+B.shape[0]-1,A.shape[1]+B.shape[1]-1,A.shape[2]+B.shape[2]-1))
    idx=np.argwhere(np.abs(A)>0)
    for (i,j,k) in idx:
        out[i:i+B.shape[0], j:j+B.shape[1], k:k+B.shape[2]] += A[i,j,k]*B
    return out
def var(which,deg=1,coef=1.0):
    sh=[1,1,1]; sh[which]=deg+1
    A=np.zeros(sh); idx=[0,0,0]; idx[which]=deg; A[tuple(idx)]=coef
    return A
def const(c):
    A=np.zeros((1,1,1)); A[0,0,0]=c; return A
def padd(A,B):
    sh=tuple(max(A.shape[i],B.shape[i]) for i in range(3))
    out=np.zeros(sh); out[:A.shape[0],:A.shape[1],:A.shape[2]]+=A
    out[:B.shape[0],:B.shape[1],:B.shape[2]]+=B; return out
def M_matrices():
    return [tri.Bf[k]@tri.HPIV[k]@tri.Bf[k].T for k in range(6)]
MM=M_matrices()
def Qpoly(k,perm):
    """Q3_k(x,y,z) as tensor in (u,v,t) where (x,y,z)=perm of (u,v,t) given as indices"""
    px,py,pz=perm
    X=padd(var(pz),pmul(var(px),var(py))*-1.0)          # z - x*y
    W=pmul(padd(const(1.0),pmul(var(px),var(px))*-1.0), padd(const(1.0),pmul(var(py),var(py))*-1.0))
    if k==0: return const(1.0)
    if k==1: return X
    if k==2: return padd(pmul(X,X)*2.0, W*-1.0)
    if k==3: return padd(pmul(pmul(X,X),X)*4.0, pmul(X,W)*-3.0)
    if k==4: return padd(padd(pmul(pmul(X,X),pmul(X,X))*8.0, pmul(pmul(X,X),W)*-8.0), pmul(W,W))
    if k==5: return padd(padd(pmul(pmul(pmul(X,X),pmul(X,X)),X)*16.0, pmul(pmul(pmul(X,X),X),W)*-20.0),
                         pmul(X,pmul(W,W))*5.0)
def wpoly(M,px,py):
    n=M.shape[0]; out=np.zeros((1,1,1))
    for i in range(n):
        for j in range(n):
            if M[i,j]!=0.0:
                out=padd(out, pmul(var(px,i,1.0),var(py,j,M[i,j])))
    return out
def Ftensor():
    tot=np.zeros((1,1,1))
    for k in range(6):
        M=MM[k]
        for (px,py,pz) in [(0,1,2),(0,2,1),(1,2,0)]:
            tot=padd(tot, pmul(wpoly(M,px,py), Qpoly(k,(px,py,pz))))
    return tot/3.0
if __name__=="__main__":
    C=Ftensor(); print("tensor shape",C.shape, "nnz",np.count_nonzero(np.abs(C)>1e-14))
    def Fev(C,u,v,t):
        return sum(C[i,j,k]*u**i*v**j*t**k for i in range(C.shape[0]) for j in range(C.shape[1]) for k in range(C.shape[2]))
    import numpy.random as R
    rng=R.default_rng(0)
    for _ in range(4):
        u,v,t=rng.uniform(-1,0.5,3)
        print("check", Fev(C,u,v,t), tri.Fh(tri.HPIV,u,v,t))
