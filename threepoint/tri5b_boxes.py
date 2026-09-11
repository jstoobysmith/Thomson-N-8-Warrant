"""[Tri5b] Branch and bound in exactly the form the Lean checker will replay:
   * one global coefficient tensor C for F(u,v,t)   (degree <= 8 per variable)
   * per box: Taylor shift of C to the centre; the affine tangent-line minorant of
     lam*h(u) with a RATIONAL chord a0; an S-procedure multiplier sigma >= 0 for the Gram
     polynomial; the degree<=2 part kept, the rest bounded by sum |coef| h^alpha;
     the quadratic minimised axis-wise (loAxis) with cross terms bounded.
"""
import numpy as np, math, sys, tri5b_eval as tri, tri5b_tensor as tensor
from fractions import Fraction as Fr

C = tensor.Ftensor()
LAM = tri.lamF
CHORDLO = 9619/10000
UHI = 1 - CHORDLO**2/2
G = np.zeros((3,3,3)); G[0,0,0]=1.0; G[1,1,1]=2.0; G[2,0,0]=-1.0; G[0,2,0]=-1.0; G[0,0,2]=-1.0
def pad(A,sh):
    out=np.zeros(sh); out[:A.shape[0],:A.shape[1],:A.shape[2]]=A; return out
GG = pad(G,C.shape)
RHO=1/500
def uof(a): return 1-a*a/2
CUBES=[[ (uof(w+RHO), uof(w-RHO)) for w in t ] for t in tri.TOUCH]
TAU=[tuple(uof(w) for w in t) for t in tri.TOUCH]

SH={}
def shift_tensor(A, c):
    out=A.copy()
    for ax in range(3):
        m=A.shape[ax]
        T=np.zeros((m,m))
        for i in range(m):
            for j in range(i+1):
                T[j,i]=math.comb(i,j)*c[ax]**(i-j)
        out=np.tensordot(T,out,axes=([1],[ax])); out=np.moveaxis(out,0,ax)
    return out

def loAxis(g,q):
    """exact min of g*e+q*e^2 over |e|<=1"""
    if 2*q <= abs(g): return q-abs(g)
    return -(g*g)/(4*q)

def lower_bound(box, sig, a0s=None):
    c=[(box[2*i]+box[2*i+1])/2 for i in range(3)]
    h=[(box[2*i+1]-box[2*i])/2 for i in range(3)]
    A = -C - sig*GG
    Sh = shift_tensor(A,c)
    val=Sh[0,0,0]; g=[0.0]*3; q=[[0.0]*3 for _ in range(3)]; tail=0.0
    for i in range(3):
        idx=[0,0,0]; idx[i]=1; g[i]+=Sh[tuple(idx)]*h[i]
        idx=[0,0,0]; idx[i]=2; q[i][i]+=Sh[tuple(idx)]*h[i]*h[i]
    for i in range(3):
        for j in range(i+1,3):
            idx=[0,0,0]; idx[i]=1; idx[j]=1; q[i][j]+=Sh[tuple(idx)]*h[i]*h[j]
    for i in range(Sh.shape[0]):
        for j in range(Sh.shape[1]):
            for k in range(Sh.shape[2]):
                if i+j+k>=3 and Sh[i,j,k]!=0.0:
                    tail+=abs(Sh[i,j,k])*h[0]**i*h[1]**j*h[2]**k
    # the tangent-line minorant of lam/sqrt(2-2u) at a rational chord a0 ~ sqrt(2-2*c[i])
    for i in range(3):
        a0 = a0s[i] if a0s else math.sqrt(2-2*c[i])
        # lam*(1/a0 - (2-2u-a0^2)/(2 a0^3)) with u = c[i]+h[i]*e
        val += LAM*(1/a0 - (2-2*c[i]-a0*a0)/(2*a0**3))
        g[i] += LAM*(2*h[i])/(2*a0**3)
    lb = val - abs(q[0][1]) - abs(q[0][2]) - abs(q[1][2]) - tail
    for i in range(3): lb += loAxis(g[i], q[i][i])
    return lb

def poly_range(A, box):
    lo=0.0; hi=0.0
    def pw(l,u,n):
        if n==0: return 1.0,1.0
        vals=[l**n,u**n]
        if l<0<u and n%2==0: vals.append(0.0)
        return min(vals),max(vals)
    for i in range(A.shape[0]):
        for j in range(A.shape[1]):
            for k in range(A.shape[2]):
                a=A[i,j,k]
                if a==0: continue
                l1,u1=pw(box[0],box[1],i); l2,u2=pw(box[2],box[3],j); l3,u3=pw(box[4],box[5],k)
                cand=[x*y*z for x in (l1,u1) for y in (l2,u2) for z in (l3,u3)]
                lo += min(cand)*a if a>0 else max(cand)*a
                hi += max(cand)*a if a>0 else min(cand)*a
    return lo,hi

def in_cube(b):
    return any(all(cb[i][0]<=b[2*i] and b[2*i+1]<=cb[i][1] for i in range(3)) for cb in CUBES)
def outside(b):
    if b[0]>b[3] or b[2]>b[5]: return True
    return poly_range(GG,b)[1] < 0

SIGS=[0.0]+[10**(-4+0.25*i) for i in range(25)]
def run(maxdepth=40):
    global LEAVES
    LEAVES=[]
    stack=[(-1.0,UHI,-1.0,UHI,-1.0,UHI,0)]
    nv=0; fail=[]
    while stack:
        *b,d=stack.pop(); b=tuple(b)
        if outside(b) or in_cube(b): continue
        nv+=1
        ok=None
        for sg in SIGS:
            if lower_bound(b,sg)>0: ok=sg; break
        if ok is not None: LEAVES.append((b,ok)); continue
        if d>=maxdepth: fail.append(b); continue
        w=[b[1]-b[0],b[3]-b[2],b[5]-b[4]]
        ax=int(np.argmax(w)); mid=(b[2*ax]+b[2*ax+1])/2
        for cb in CUBES:
            for e in cb[ax]:
                if b[2*ax]+1e-13 < e < b[2*ax+1]-1e-13: mid=e; break
        n1=list(b); n1[2*ax+1]=mid; n2=list(b); n2[2*ax]=mid
        stack.append(tuple(n1)+(d+1,)); stack.append(tuple(n2)+(d+1,))
        if nv>300000: print("ABORT"); break
    return nv,len(LEAVES),fail
if __name__=="__main__":
    md=int(sys.argv[1]) if len(sys.argv)>1 else 40
    nv,nl,f=run(md)
    print("visited",nv,"leaves",nl,"fail",len(f))
    for b in f[:4]:
        c=[(b[2*i]+b[2*i+1])/2 for i in range(3)]
        print("   fail w=%.1e"%max(b[2*i+1]-b[2*i] for i in range(3)), np.round(c,5))
