import re, json
from mpmath import mp, mpf, sqrt, findroot, matrix, norm
mp.dps=60
S2=sqrt(2)
def Ep(u): return (2*S2+1)/(1-u)**mpf(1.5) - 4*(2+S2)/((2-S2)+(2+S2)*u)**mpf(1.5) - 4*(2-S2)/((2+S2)+(2-S2)*u)**mpf(1.5)
U=findroot(Ep, mpf('0.3140893678892018673812332'))
R=sqrt(1-U); S2S=sqrt(2+2*U-S2*(1-U)); S4S=sqrt(2+2*U+S2*(1-U))

# --- parse Bpoly from CertData.lean ---
src=open('/Users/josephsmith/LocalGithub/ThompsonEight/Thomson/ThreePoint/CertData.lean').read()
Bp={}
body=src[src.index('def Bpoly'):src.index('/-- The basis matrices')]
for m in re.finditer(r'^\s*\|\s*(\d+),\s*(\d+),\s*(\d+)\s*=>\s*(-?)\((\d+)(?:/(\d+))?\s*:\s*ℝ\)\s*\*\s*\((.*)\)\s*$', body, re.M):
    k,i,a,sg,nu,de,poly = m.group(1),m.group(2),m.group(3),m.group(4),m.group(5),m.group(6),m.group(7)
    c = mpf(int(nu))/mpf(int(de)) if de else mpf(int(nu))
    if sg=='-': c=-c
    # poly like  (1 : ℝ) + (-2 : ℝ) * uStar + (3 : ℝ) * uStar ^ 2
    val=mpf(0)
    for t in re.finditer(r'\((-?\d+)\s*:\s*ℝ\)(\s*\*\s*uStar(\s*\^\s*(\d+))?)?', poly):
        co=mpf(int(t.group(1)))
        if t.group(2) is None: p=0
        elif t.group(4) is None: p=1
        else: p=int(t.group(4))
        val += co*U**p
    assert (int(k),int(i),int(a)) not in Bp; Bp[(int(k),int(i),int(a))]=c*val
def B(k):
    n=9-k
    return matrix([[Bp.get((k,i,a),mpf(0)) for a in range(n)] for i in range(n)])
Bs=[B(k) for k in range(6)]
print("Bpoly entries parsed:", len(Bp))

slot=[(0,0,2),(0,0,6),(0,0,7),(0,1,3),(0,2,4),(0,3,6),(0,5,7),(1,0,0),(1,0,1),(1,0,2),(1,2,3),(2,0,0),(2,0,1),(2,1,2),(2,3,5),(3,0,0),(3,0,1),(3,0,3),(3,1,2),(4,0,0),(4,0,1),(4,0,2),(5,0,0),(5,0,1)]

def Q3(k,u,v,t):
    x=t-u*v; y=(1-u**2)*(1-v**2)
    return [mpf(1), x, 2*x**2-y, 4*x**3-3*x*y, 8*x**4-8*x**2*y+y**2, 16*x**5-20*x**3*y+5*x*y**2][k]
def S3e(k,u,v,t,i,j):
    s=mpf(0)
    for (a,b,c) in ((u,v,t),(u,t,v),(v,u,t),(v,t,u),(t,u,v),(t,v,u)):
        s += a**i * b**j * Q3(k,a,b,c)
    return s/6
def M(k,u,v,t,a,b):
    n=9-k; Bk=Bs[k]; s=mpf(0)
    for i in range(n):
        if Bk[i,a]==0: continue
        for l in range(n):
            if Bk[l,b]==0: continue
            s += Bk[i,a]*S3e(k,u,v,t,i,l)*Bk[l,b]
    return s
def Gh(j,u,v,t):
    k,a,b=slot[j]
    return M(k,u,v,t,a,b) if a==b else M(k,u,v,t,a,b)+M(k,u,v,t,b,a)

chord=[S2*R, 2*R, S2S, S4S]
touch=[(S4S,S4S,S2*R),(S4S,2*R,S2S),(S4S,S2S,S2*R),(2*R,S2*R,S2*R),(S2S,S2S,S2*R)]
def tof(s): return 1-s**2/2

def pairLin(j,s): return -(3*s)*Gh(j,mpf(1),tof(s),tof(s))
def triLin(j,a,b,c): return -(a*b*c)*Gh(j,tof(a),tof(b),tof(c))

def d(f,x0,h=mpf('1e-15')):
    return (f(x0+h)-f(x0-h))/(2*h)

rows=[('bound',),('pd',0),('pv',1),('pd',1),('pv',2),('pd',2),('pv',3),('pd',3),
      ('tv',0),('td',0,0),('td',0,2),('tv',1),('td',1,0),('td',1,2),
      ('tv',2),('td',2,0),('td',2,1),('td',2,2),('tv',3),('td',3,0),('td',3,1),
      ('tv',4),('td',4,0),('td',4,2)]
def entry(i,j):
    r=rows[i]
    if r[0]=='bound': return -4*Gh(j,mpf(1),mpf(1),mpf(1))
    if r[0]=='pv': return pairLin(j,chord[r[1]])
    if r[0]=='pd': return d(lambda s: pairLin(j,s), chord[r[1]])
    if r[0]=='tv':
        a,b,c=touch[r[1]]; return triLin(j,a,b,c)
    if r[0]=='td':
        m,cc=r[1],r[2]; a,b,c=touch[m]
        return d(lambda x: triLin(j, a+(x if cc==0 else 0), b+(x if cc==1 else 0), c+(x if cc==2 else 0)), mpf(0))
Mx=matrix(24,24)
for i in range(24):
    for j in range(24): Mx[i,j]=entry(i,j)
import numpy as np
A=np.array([[float(Mx[i,j]) for j in range(24)] for i in range(24)])
print("cond", np.linalg.cond(A,np.inf))
print("normM(inf)", np.abs(A).sum(1).max())
Ninv=np.linalg.inv(A)
print("normMinv(inf)", np.abs(Ninv).sum(1).max())
print("json cond/normN/normM", json.load(open('/Users/josephsmith/LocalGithub/ThompsonEight/threepoint/task1_design.json'))['cond'], json.load(open('/Users/josephsmith/LocalGithub/ThompsonEight/threepoint/task1_design.json'))['normN'], json.load(open('/Users/josephsmith/LocalGithub/ThompsonEight/threepoint/task1_design.json'))['normM'])
np.save('A.npy',A)

# --- deliverable: the rational approximate inverse N for Task 1a ---
from fractions import Fraction as Fr
N = np.linalg.inv(A)
DEN = 10**12
Nq = [[Fr(round(N[i][j]*DEN), DEN) for j in range(24)] for i in range(24)]
Nf = np.array([[float(x) for x in row] for row in Nq])
E = np.eye(24) - Nf @ A
print("||I - N*M||_inf =", np.abs(E).sum(1).max())
json.dump({"den": DEN,
           "N_num": [[int(Nq[i][j]*DEN) for j in range(24)] for i in range(24)],
           "normE_inf": float(np.abs(E).sum(1).max()),
           "normM_inf": float(np.abs(A).sum(1).max()),
           "normNinv_inf": float(np.abs(N).sum(1).max()),
           "M_float": A.tolist()},
          open('/Users/josephsmith/LocalGithub/ThompsonEight/threepoint/task1a_pivotmatrix.json','w'))
print("wrote task1a_pivotmatrix.json")
