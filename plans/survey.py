import re, json, itertools, numpy as np
from fractions import Fraction as Fr
from mpmath import mp, mpf, sqrt, findroot
mp.dps=40
S2=sqrt(2)
def Ep(u): return (2*S2+1)/(1-u)**mpf(1.5) - 4*(2+S2)/((2-S2)+(2+S2)*u)**mpf(1.5) - 4*(2-S2)/((2+S2)+(2-S2)*u)**mpf(1.5)
U=findroot(Ep, mpf('0.3140893678892018673812332'))
uf=float(U); r=float(sqrt(1-U)); s2=float(sqrt(2+2*U-S2*(1-U))); s4=float(sqrt(2+2*U+S2*(1-U))); w=float(S2)
src=open('Thomson/ThreePoint/CertData.lean').read()
body=src[src.index('def Bpoly'):src.index('/-- The basis matrices')]
Bp={}
for m in re.finditer(r'^\s*\|\s*(\d+),\s*(\d+),\s*(\d+)\s*=>\s*(-?)\((\d+)(?:/(\d+))?\s*:\s*ℝ\)\s*\*\s*\((.*)\)\s*$', body, re.M):
    k,i,a,sg,nu,de,poly = m.groups()
    c = int(nu)/(int(de) if de else 1)*(-1 if sg=='-' else 1); val=0.0
    for t in re.finditer(r'\((-?\d+)\s*:\s*ℝ\)(\s*\*\s*uStar(\s*\^\s*(\d+))?)?', poly):
        co=int(t.group(1)); p=0 if t.group(2) is None else (1 if t.group(4) is None else int(t.group(4)))
        val += co*uf**p
    Bp[(int(k),int(i),int(a))]=c*val
B=[np.array([[Bp.get((k,i,a),0.0) for a in range(9-k)] for i in range(9-k)]) for k in range(6)]
hb=src[src.index('def HfixTable'):src.index('/-- Symmetrised fixed entries')]
Hf={}
for m in re.finditer(r'\|\s*(\d+),\s*(\d+),\s*(\d+)\s*=>\s*\((-?\d+)/(\d+)\s*:\s*ℝ\)', hb):
    k,a,b,nu,de=map(int,m.groups()); Hf[(k,a,b)]=nu/de
slot=[(0,0,2),(0,0,6),(0,0,7),(0,1,3),(0,2,4),(0,3,6),(0,5,7),(1,0,0),(1,0,1),(1,0,2),(1,2,3),(2,0,0),(2,0,1),(2,1,2),(2,3,5),(3,0,0),(3,0,1),(3,0,3),(3,1,2),(4,0,0),(4,0,1),(4,0,2),(5,0,0),(5,0,1)]
pn=[float(Fr(x)) for x in re.findall(r'\((-?\d+)/(\d+) : ℝ\)', src[src.index('def pivotsNum'):src.index('/-- The 24 definitional rows')]) for x in [x[0]+'/'+x[1]]]
def Hmat(p):
    H=[np.zeros((9-k,9-k)) for k in range(6)]
    for (k,a,b),v in Hf.items(): H[k][a,b]=v; H[k][b,a]=v
    for j,(k,a,b) in enumerate(slot): H[k][a,b]=p[j]; H[k][b,a]=p[j]
    return H
a0=944368722101/1e12; a1=2445383048987/1e13; lam=97932235147/1e13
H=Hmat(pn); Mk=[B[k]@H[k]@B[k].T for k in range(6)]
for k in range(6):
    ev=np.linalg.eigvalsh(H[k][:8-k,:8-k]); print("H'_%d eig min %.3e"%(k,ev.min()))
def Q3(k,x,y,z):
    X=z-x*y; Y=(1-x*x)*(1-y*y)
    return [1+0*X, X, 2*X**2-Y, 4*X**3-3*X*Y, 8*X**4-8*X**2*Y+Y**2, 16*X**5-20*X**3*Y+5*X*Y**2][k]
def F(u,v,t):
    tot=0.0
    for k in range(6):
        n=9-k; M=Mk[k]
        for (x,y,z) in itertools.permutations((u,v,t)):
            xp=np.array([x**i for i in range(n)]); yp=np.array([y**j for j in range(n)])
            tot += (xp@M@yp)*Q3(k,x,y,z)/6
    return tot
def triP(a,b,c): return lam*(b*c+a*c+a*b) - a*b*c*F(1-a*a/2,1-b*b/2,1-c*c/2)
def pairP(s): t=1-s*s/2; return (1-18*lam)-s*(a0+a1*t+3*F(1,t,t))
chords=[w*r,2*r,s2,s4]; names='ADNF'
touch=[(s4,s4,w*r),(s4,2*r,s2),(s4,s2,w*r),(2*r,w*r,w*r),(s2,s2,w*r)]
print("chords",chords)
print("pair values/derivs at chords:")
for s in chords:
    h=1e-4; print("  P=%.2e P'=%.2e P''=%.4e"%(pairP(s),(pairP(s+h)-pairP(s-h))/(2*h),(pairP(s+h)-2*pairP(s)+pairP(s-h))/h**2))
ss=np.linspace(0.96,2,2001); pv=np.array([pairP(s) for s in ss])
d=np.array([min(abs(s-c) for c in chords) for s in ss])
for dd in [0.01,0.02,0.05,0.1]:
    m=d>=dd; print("  pair min at dist>=%.2f from roots: %.3e"%(dd,pv[m].min()))
print("triangle Taylor data at touching types (chord vars):")
for m,(a,b,c) in enumerate(touch):
    h=2e-3; x0=np.array([a,b,c]); Hs=np.zeros((3,3))
    f0=triP(*x0)
    for i in range(3):
        for j in range(3):
            e=np.zeros(3); e[i]+=h; f=np.zeros(3); f[j]+=h
            Hs[i,j]=(triP(*(x0+e+f))-triP(*(x0+e-f))-triP(*(x0-e+f))+triP(*(x0-e-f)))/(4*h*h)
    ev=np.linalg.eigvalsh(Hs)
    # cubic size along the soft direction
    vmin=np.linalg.eigh(Hs)[1][:,0]
    vals=[(d_, triP(*(x0+d_*vmin)), triP(*(x0-d_*vmin))) for d_ in [1e-3,3e-3,1e-2,3e-2,1e-1]]
    print(" type",m,"T=%.1e"%f0,"Hess eig",["%.2e"%e for e in ev])
    for d_,p_,mi in vals: print("    |d|=%.0e  T(+)=%.2e T(-)=%.2e  ratio to quad: %.2f %.2f"%(d_,p_,mi,p_/(0.5*ev[0]*d_*d_),mi/(0.5*ev[0]*d_*d_)))
# global min on sorted region grid, by distance
rng=np.linspace(0.96,2,70); best={}
for a in rng:
    for b in rng:
        if b>a: continue
        for c in rng:
            if c>b: continue
            g=1+2*(1-a*a/2)*(1-b*b/2)*(1-c*c/2)-(1-a*a/2)**2-(1-b*b/2)**2-(1-c*c/2)**2
            if g<-0.05: continue
            v=triP(a,b,c); dist=min(max(abs(a-t[0]),abs(b-t[1]),abs(c-t[2])) for t in touch)
            key=(0.0 if dist<0.02 else 0.02 if dist<0.05 else 0.05 if dist<0.1 else 0.1 if dist<0.2 else 0.2, g>=0)
            best[key]=min(best.get(key,1e9),v)
for k_ in sorted(best): print("  triP min, dist class %.2f inGram=%s : %.3e"%(k_[0],k_[1],best[k_]))
print("---- locate negatives ----")
rng=np.linspace(0.96,2,105); worst=[]
for a in rng:
    for b in rng:
        if b>a: continue
        for c in rng:
            if c>b: continue
            g=1+2*(1-a*a/2)*(1-b*b/2)*(1-c*c/2)-(1-a*a/2)**2-(1-b*b/2)**2-(1-c*c/2)**2
            if g<0: continue
            v=triP(a,b,c)
            if v<0: worst.append((v,a,b,c,g))
worst.sort(); print("count neg:",len(worst)); 
for wv in worst[:8]: print("  T=%.3e at (%.4f,%.4f,%.4f) gram=%.3e"%wv)
print("min over c>=0.962 only:")
rng2=np.linspace(0.962,2,105); mn=(1,None)
for a in rng2:
    for b in rng2:
        if b>a: continue
        for c in rng2:
            if c>b: continue
            g=1+2*(1-a*a/2)*(1-b*b/2)*(1-c*c/2)-(1-a*a/2)**2-(1-b*b/2)**2-(1-c*c/2)**2
            if g<0: continue
            dist=min(max(abs(a-t[0]),abs(b-t[1]),abs(c-t[2])) for t in touch)
            if dist<0.02: continue
            v=triP(a,b,c)
            if v<mn[0]: mn=(v,(a,b,c,g,dist))
print("  min:",mn)
# pair at s in [0.96,0.962]
print("pair P at 0.96, 0.961, 0.962:", pairP(0.96), pairP(0.961), pairP(0.962))
print("---- 70-grid argmin inGram ----")
rng=np.linspace(0.96,2,70); mn=(1,None)
for a in rng:
    for b in rng:
        if b>a: continue
        for c in rng:
            if c>b: continue
            g=1+2*(1-a*a/2)*(1-b*b/2)*(1-c*c/2)-(1-a*a/2)**2-(1-b*b/2)**2-(1-c*c/2)**2
            if g<0: continue
            v=triP(a,b,c)
            if v<mn[0]: mn=(v,(a,b,c,g))
print(mn)
a,b,c,g=mn[1]
# local refine around it
import scipy.optimize as so
def obj(x):
    a,b,c=x; g=1+2*(1-a*a/2)*(1-b*b/2)*(1-c*c/2)-(1-a*a/2)**2-(1-b*b/2)**2-(1-c*c/2)**2
    return triP(a,b,c)+ (1e3*g*g if g<0 else 0)
res=so.minimize(obj,[a,b,c],method='Nelder-Mead',options={'xatol':1e-7,'fatol':1e-12})
a,b,c=res.x; g=1+2*(1-a*a/2)*(1-b*b/2)*(1-c*c/2)-(1-a*a/2)**2-(1-b*b/2)**2-(1-c*c/2)**2
print("refined min: T=%.3e at (%.6f,%.6f,%.6f) gram=%.3e; inner products %.4f %.4f %.4f"%(triP(a,b,c),a,b,c,g,1-a*a/2,1-b*b/2,1-c*c/2))
print("---- strip near s=0.962 ----")
for L in [0.9619,0.96195,0.96197,0.961977,0.962,0.9625]:
    mn=(1,None)
    for a in np.linspace(L,2,400):
        for b in [L]+list(np.linspace(L,min(a,L+0.05),6)):
            c=L
            g=1+2*(1-a*a/2)*(1-b*b/2)*(1-c*c/2)-(1-a*a/2)**2-(1-b*b/2)**2-(1-c*c/2)**2
            if g<0 or b>a: continue
            v=triP(a,b,c)
            if v<mn[0]: mn=(v,(a,b,c))
    print("  c=%.6f: min T = %.3e at %s"%(L,mn[0],mn[1]))
