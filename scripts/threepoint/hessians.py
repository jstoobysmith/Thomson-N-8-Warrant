"""Hessian of the triangle slack T(u,v,t) = lam(h(u)+h(v)+h(t)) - F(u,v,t) at the five antiprism
triangle types, and second derivative of the pair polynomial at the four distances, for the
high-precision certificate.  Positive definiteness is what the rigorous local argument needs."""
import json, sys, os, itertools
from mpmath import mp, mpf, matrix, sqrt, eigsy, diff, nstr, findroot
import sympy as sp
mp.dps=40
here=os.path.dirname(os.path.abspath(__file__))
Hc=json.load(open(os.path.join(here,sys.argv[1] if len(sys.argv)>1 else 'certificate_hp.json')))
C=json.load(open(os.path.join(here,'certificate_numerical.json'))); d=C['d']; K=C['KMAX']
a0,a1,lam=mpf(Hc['a0']),mpf(Hc['a1']),mpf(Hc['lam']); ust=mpf(Hc['ustar'])
H=[matrix([[mpf(x) for x in row] for row in Hc['H'][str(k)]]) for k in range(K+1)]
W=[matrix([[mpf(x) for x in row] for row in Hc['W'][str(k)]]) for k in range(K+1)]
F=[W[k]*H[k]*W[k].T for k in range(K+1)]
def Qk(k,U,V,T):
    c=sp.Poly(sp.chebyshevt(k,sp.Symbol('x')),sp.Symbol('x')).all_coeffs()[::-1]
    w=(1-U*U)*(1-V*V); x=T-U*V; out=mpf(0)
    for j,cj in enumerate(c):
        if cj!=0 and (k-j)%2==0: out+=int(cj)*x**j*w**((k-j)//2)
    return out
def Sk(k,U,V,T):
    m=d-k+1; acc=matrix(m,m)
    for p in itertools.permutations((U,V,T)):
        q=Qk(k,*p); acc+=matrix([[p[0]**i*p[1]**j*q for j in range(m)] for i in range(m)])
    return acc/6
def Fun(x,y,z): return sum(sum(F[k][i,j]*Sk(k,x,y,z)[i,j] for i in range(d-k+1) for j in range(d-k+1)) for k in range(K+1))
def h(t): return 1/sqrt(2-2*t)
def T(x,y,z): return lam*(h(x)+h(y)+h(z))-Fun(x,y,z)
s2=sqrt(2); r=sqrt(1-ust); hh=sqrt(ust); ss=r/s2
P=[[r,0,hh],[0,r,hh],[-r,0,hh],[0,-r,hh],[ss,ss,-hh],[-ss,ss,-hh],[-ss,-ss,-hh],[ss,-ss,-hh]]
G=[[sum(P[i][k]*P[j][k] for k in range(3)) for j in range(8)] for i in range(8)]
types={}
for i in range(8):
    for j in range(i+1,8):
        for k in range(j+1,8):
            key=tuple(sorted([G[i][j],G[i][k],G[j][k]])); kk=tuple(nstr(x,8) for x in key)
            types[kk]=key
print("Hessian of the triangle slack at each antiprism triangle type (eigenvalues):")
allpd=True
for kk,tr in sorted(types.items()):
    x0=list(tr); Hm=matrix(3,3)
    for a in range(3):
        for b in range(3):
            def f(p,q,a=a,b=b):
                p_=x0[:]; p_[a]+=p; p_[b]+=q if a!=b else 0
                if a==b: p_[a]=x0[a]+p
                return T(*p_)
            if a==b: Hm[a,a]=diff(lambda p: T(*[x0[m]+(p if m==a else 0) for m in range(3)]),0,2)
            else: Hm[a,b]=diff(lambda p,q: T(*[x0[m]+(p if m==a else (q if m==b else 0)) for m in range(3)]),(0,0),(1,1))
    ev,_=eigsy(Hm); pd=min(ev)>0; allpd&=pd
    print(f"   {kk}: T={nstr(T(*x0),3)}  eig = {[nstr(e,6) for e in ev]}   {'PD' if pd else 'NOT PD'}")
print("all five Hessians positive definite:",allpd)
print("\nsecond derivative of the pair polynomial P(s) at the four distances (must be > 0):")
def Pf(s): t=1-s*s/2; return (1-18*lam)-s*(a0+a1*t+3*Fun(1,t,t))
for t in sorted(set(nstr(G[i][j],25) for i in range(8) for j in range(i+1,8))):
    s=sqrt(2-2*mpf(t)); print(f"   s={nstr(s,8)}: P={nstr(Pf(s),3)}  P'={nstr(diff(Pf,s),3)}  P''={nstr(diff(Pf,s,2),8)}")
