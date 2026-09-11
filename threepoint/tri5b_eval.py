import numpy as np, mpmath as mp, tri5b_leandata as L
from fractions import Fraction as Fr

mp.mp.dps = 60
def _ustar():
    s2 = mp.sqrt(2)
    f = lambda u: (2*s2+1)/mp.sqrt(1-u)**3 - 4*(2+s2)/mp.sqrt((2-s2)+(2+s2)*u)**3 - 4*(2-s2)/mp.sqrt((2+s2)+(2-s2)*u)**3
    return mp.findroot(f, mp.mpf('0.31408936788'))
USTAR = _ustar()
ustar = float(USTAR)

a0F, a1F, lamF = [float(x) for x in L.a_consts()]
PIV = np.array([float(x) for x in L.pivotsNum()])
SLOT = L.SLOT

Bf = [np.array([[float(x) for x in row] for row in Mk], float) for Mk in L.B_entries(ustar, float)]
Hf = [np.array([[float(x) for x in row] for row in Mk], float) for Mk in L.Hfix_entries(float)]

def Q3(k,u,v,t):
    w=(1-u**2)*(1-v**2); x=t-u*v
    return [1, x, 2*x**2-w, 4*x**3-3*x*w, 8*x**4-8*x**2*w+w**2, 16*x**5-20*x**3*w+5*x*w**2][k]

def S3(k,u,v,t):
    n=9-k
    acc=np.zeros((n,n))
    for (p,q,r) in [(u,v,t),(u,t,v),(v,u,t),(v,t,u),(t,u,v),(t,v,u)]:
        qk=Q3(k,p,q,r)
        acc += np.outer(np.array([p**i for i in range(n)]), np.array([q**j for j in range(n)]))*qk
    return acc/6.0

def Hp(p):
    out=[]
    for k in range(6):
        M=Hf[k].copy()
        for j,(kk,a,b) in enumerate(SLOT):
            if kk==k:
                M[a,b]+=p[j]
                if a!=b: M[b,a]+=p[j]
        out.append(M)
    return out

HPIV = Hp(PIV)

def Fh(H,u,v,t):
    return sum(float(np.sum(H[k]*(Bf[k].T@S3(k,u,v,t)@Bf[k]))) for k in range(6))

def Gh(j,u,v,t):
    k,a,b=SLOT[j]
    M=Bf[k].T@S3(k,u,v,t)@Bf[k]
    return M[a,b]+ (M[b,a] if a!=b else 0.0)

def triP_H(H,a,b,c):
    return lamF*(b*c+a*c+a*b) - a*b*c*Fh(H,1-a*a/2,1-b*b/2,1-c*c/2)

def triP(a,b,c): return triP_H(HPIV,a,b,c)

def pertsum(a,b,c):
    u,v,t=1-a*a/2,1-b*b/2,1-c*c/2
    return abs(a*b*c)*sum(abs(Gh(j,u,v,t)) for j in range(24))

s2=mp.sqrt(2); rS=float(mp.sqrt(1-USTAR)); s2S=float(mp.sqrt(2+2*USTAR-s2*(1-USTAR))); s4S=float(mp.sqrt(2+2*USTAR+s2*(1-USTAR)))
A=float(mp.sqrt(2))*rS; D=2*rS; N=s2S; Ff=s4S
TOUCH=[(Ff,Ff,A),(Ff,D,N),(Ff,N,A),(D,A,A),(N,N,A)]
CHORD=[A,D,N,Ff]
