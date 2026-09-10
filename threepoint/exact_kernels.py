"""Exact kernel vectors v_k(u) of the sharp certificate: the antiprism family is vertex-transitive,
so M_k = sum_{i,j,l} S_k(antiprism) = 8 * A_0 with A_0 = sum_{j,l} S_k(t_0j, t_0l, t_jl); A_0 has rank 1."""
import sympy as sp, itertools, json
u=sp.symbols('u'); s2=sp.sqrt(2)
d=8
def Qk(k,U,V,T):
    c=sp.Poly(sp.chebyshevt(k,sp.Symbol('x')),sp.Symbol('x')).all_coeffs()[::-1]
    w=(1-U**2)*(1-V**2); x=T-U*V; out=0
    for j,cj in enumerate(c):
        if cj!=0 and (k-j)%2==0: out+=cj*x**j*w**((k-j)//2)
    return sp.expand(out)
def Yk(k,U,V,T):
    m=d-k+1; q=Qk(k,U,V,T)
    return sp.Matrix(m,m,lambda i,j: U**i*V**j*q)
def Sk(k,U,V,T):
    acc=sp.zeros(d-k+1,d-k+1)
    for p in itertools.permutations((U,V,T)): acc+=Yk(k,*p)
    return acc/6
# antiprism: point 0 = (r,0,h); inner products with the other 7 (h^2=u, r^2=1-u)
r2=1-u
t_sq_adj=u              # (0,r,h),(0,-r,h)
t_sq_diag=2*u-1         # (-r,0,h)
t_cross_near=r2/s2-u    # (s,s,-h),(s,-s,-h)
t_cross_far=-r2/s2-u    # (-s,s,-h),(-s,-s,-h)
# Gram row of point 0 (index: 0=self,1..7 others), and full Gram for the pairs (j,l)
import numpy as np
h=sp.sqrt(u); r=sp.sqrt(1-u); s=r/s2
P=[sp.Matrix([r,0,h]),sp.Matrix([0,r,h]),sp.Matrix([-r,0,h]),sp.Matrix([0,-r,h]),
   sp.Matrix([s,s,-h]),sp.Matrix([-s,s,-h]),sp.Matrix([-s,-s,-h]),sp.Matrix([s,-s,-h])]
G=[[sp.simplify((P[i].T*P[j])[0]) for j in range(8)] for i in range(8)]
out={}
for k in range(6):
    A=sp.zeros(d-k+1,d-k+1)
    for j in range(8):
        for l in range(8):
            A+=Sk(k,G[0][j],G[0][l],G[j][l])
    A=A.applyfunc(lambda e: sp.simplify(sp.expand(e)))
    # rank-1: take the column with largest constant part; v = that column / its leading entry
    col=None
    for c in range(A.cols):
        if any(e!=0 for e in A[:,c]): col=A[:,c]; break
    piv=[e for e in col if e!=0][0]
    v=(col/piv).applyfunc(sp.simplify)
    # check rank 1 symbolically: A - (col * col^T)/piv == 0 ?  (A symmetric rank-1 => A = col col^T / pivot-ish); do numeric spot-check instead
    uv=sp.Rational(314089,1000000)
    An=np.array(A.subs(u,uv).evalf(30).tolist(),dtype=float)
    rk=np.linalg.matrix_rank(An,tol=1e-9*abs(An).max())
    print(f"k={k}: size {d-k+1}, numeric rank at u=0.314089: {rk}")
    print("   v_k(u) =",[sp.factor(e) for e in v])
    out[str(k)]=[str(e) for e in v]
json.dump(out,open('/Users/js4814/Documents/GitHub/MyComandCenter/Thomson/threepoint/kernel_vectors_exact.json','w'),indent=1)
print("written kernel_vectors_exact.json")
