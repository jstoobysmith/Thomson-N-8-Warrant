import re, sympy as sp, itertools
u, u0, w = sp.symbols('u u0 w')   # w = sqrt2
src=open('Thomson/ThreePoint/CertData.lean').read()
body=src[src.index('def Bpoly'):src.index('/-- The basis matrices')]
Bp={}
for m in re.finditer(r'^\s*\|\s*(\d+),\s*(\d+),\s*(\d+)\s*=>\s*(-?)\((\d+)(?:/(\d+))?\s*:\s*ℝ\)\s*\*\s*\((.*)\)\s*$', body, re.M):
    k,i,a,sg,nu,de,poly = m.groups()
    c = sp.Rational(int(nu), int(de) if de else 1)*(-1 if sg=='-' else 1)
    val=0
    for t in re.finditer(r'\((-?\d+)\s*:\s*ℝ\)(\s*\*\s*uStar(\s*\^\s*(\d+))?)?', poly):
        co=int(t.group(1)); p=0 if t.group(2) is None else (1 if t.group(4) is None else int(t.group(4)))
        val += co*u0**p
    Bp[(int(k),int(i),int(a))]=c*val
def B(k): n=9-k; return sp.Matrix(n,n,lambda i,a: Bp.get((k,i,a),0))
def Q3(k,x,y,z):
    X=z-x*y; Y=(1-x**2)*(1-y**2)
    return [1, X, 2*X**2-Y, 4*X**3-3*X*Y, 8*X**4-8*X**2*Y+Y**2, 16*X**5-20*X**3*Y+5*X*Y**2][k]
def S3(k,x,y,z):
    n=9-k; acc=sp.zeros(n,n)
    for (a,b,c) in itertools.permutations((x,y,z)):
        q=Q3(k,a,b,c); acc+=sp.Matrix(n,n,lambda i,j: a**i*b**j*q)
    return acc/6
tA=u; tD=2*u-1; tN=-u+w*(1-u)/2; tF=-u-w*(1-u)/2
pairs=[(8,tA),(4,tD),(8,tN),(8,tF)]
tris=[(8,(tF,tF,tA)),(16,(tF,tD,tN)),(16,(tF,tN,tA)),(8,(tD,tA,tA)),(8,(tN,tN,tA))]
def red(e): return sp.expand(sp.expand(e).subs(w**2,2).subs(w**3,2*w).subs(w**4,4))
def red_full(e):
    e=sp.expand(e); p=sp.Poly(e,w); out=0
    for (d,),c in p.terms():
        out+= c*(2**(d//2))*(w if d%2 else 1)
    return sp.expand(out)
for k in range(6):
    n=9-k
    A = 8*S3(k,1,1,1)
    for m,t in pairs: A += 6*m*S3(k,1,t,t)
    for m,(x,y,z) in tris: A += 6*m*S3(k,x,y,z)
    A = A.applyfunc(red_full)
    # rank check at u=u0 numerically
    An = A.subs({u:sp.Rational(314,1000), w:sp.sqrt(2)}).evalf(30)
    print("k",k,"rank of Acomb at u=0.314:", sp.Matrix(An).rank(iszerofunc=lambda x: abs(x)<1e-20))
    Bk=B(k)
    psi = (Bk.T*A*Bk).applyfunc(red_full)
    # value at u=u0
    val = psi.subs(u,u0).applyfunc(red_full)
    print("   psi(u0,u0)==0 :", val==sp.zeros(n,n))
    dpsi = psi.applyfunc(lambda e: sp.diff(e,u)).subs(u,u0).applyfunc(red_full)
    print("   d/du psi |u=u0 ==0 :", dpsi==sp.zeros(n,n))
    # check that (u-u0)^2 divides
    ok=True
    for i in range(n):
        for j in range(i,n):
            q,r = sp.div(sp.Poly(psi[i,j],u), sp.Poly((u-u0)**2,u))
            if not r.is_zero: ok=False
    print("   (u-u0)^2 | psi :", ok, " max terms:", max(len(sp.Poly(psi[i,j],u,u0,w).terms()) for i in range(n) for j in range(n)))
