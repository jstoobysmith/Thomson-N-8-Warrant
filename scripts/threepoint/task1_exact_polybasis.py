"""TASK 1 — exact certificate data (blueprint §12.7, Tasks.lean Task 1).
Field K = Q(w,u,r,y,z): w=√2, u=u*, r=√(1-u), y=s2, z=s4; relations
  w^2=2, r^2=1-u, y^2=2+2u-w(1-u), z^2=2+2u+w(1-u), u^12 = -Σ_{k<12}(a_k + w b_k) u^k  (minimal polynomial).
Basis u^a w^b r^c y^d z^e (a<12, b,c,d,e∈{0,1}); dim 192.  Elements: dict {(a,b,c,d,e): Fraction}.
Fix 95 unknowns at 13-digit rationals; solve the 24 pivot unknowns exactly as a (24·192)² rational system."""
import json, sys, os, itertools, time
from fractions import Fraction as Fr
import numpy as np
from flint import fmpq_mat, fmpq
import sympy as sp
here=os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0,here)
T0=time.time()
def log(*a): print(f"[{time.time()-T0:7.1f}s]",*a,flush=True)
# ---------------- minimal polynomial ----------------
_u,_w=sp.symbols('u w'); s2=sp.sqrt(2); a_=2-s2; b_=2+s2
c1=(4*s2+2)/2; c2=4*b_; c3=4*a_
num=sp.expand(sp.numer(sp.together((c1**2/(1-_u)**3+c2**2/(a_+b_*_u)**3-c3**2/(b_+a_*_u)**3)**2-4*c1**2*c2**2/(1-_u)**3/(a_+b_*_u)**3)))
fac=[f for f,m in sp.factor_list(num,extension=s2)[1] if sp.Poly(f,_u).degree()==12][0]
P=sp.Poly(fac,_u).monic(); e=sp.expand(P.as_expr())
Bp=sp.Poly(sp.expand(e.coeff(s2)),_u); Ap=sp.Poly(sp.expand(e-s2*Bp.as_expr()),_u)
MP={k:(Fr(int(sp.Rational(Ap.coeff_monomial(_u**k)).p),int(sp.Rational(Ap.coeff_monomial(_u**k)).q)),
       Fr(int(sp.Rational(Bp.coeff_monomial(_u**k)).p),int(sp.Rational(Bp.coeff_monomial(_u**k)).q))) for k in range(12)}
log("minimal polynomial ready; A(u) leading coeffs",Ap.coeff_monomial(_u**12), "B deg",Bp.degree())
# ---------------- field arithmetic ----------------
class K:
    __slots__=('d',)
    def __init__(self,d=None): self.d={k:v for k,v in (d or {}).items() if v!=0}
    @staticmethod
    def const(c): return K({(0,0,0,0,0):Fr(c)})
    @staticmethod
    def mono(a=0,b=0,c=0,d=0,e=0,coef=1): return K({(a,b,c,d,e):Fr(coef)})
    def __add__(s,o):
        r=dict(s.d)
        for k,v in o.d.items(): r[k]=r.get(k,0)+v
        return K(r)
    def __sub__(s,o): return s+o*K.const(-1)
    def __neg__(s): return s*K.const(-1)
    def __mul__(s,o):
        if not isinstance(o,K): o=K.const(o)
        r={}
        for (a,b,c,d,e),v in s.d.items():
            for (a2,b2,c2,d2,e2),v2 in o.d.items():
                k=(a+a2,b+b2,c+c2,d+d2,e+e2); r[k]=r.get(k,0)+v*v2
        return K(r).reduce()
    __rmul__=__mul__
    def reduce(s):
        # reduce w^2, r^2, y^2, z^2 then u^12
        cur=dict(s.d); out={}
        changed=True
        while changed:
            changed=False; nxt={}
            for (a,b,c,d,e),v in cur.items():
                if v==0: continue
                if b>=2: nxt[(a,b-2,c,d,e)]=nxt.get((a,b-2,c,d,e),0)+2*v; changed=True
                elif c>=2:   # r^2 = 1-u
                    nxt[(a,b,c-2,d,e)]=nxt.get((a,b,c-2,d,e),0)+v; nxt[(a+1,b,c-2,d,e)]=nxt.get((a+1,b,c-2,d,e),0)-v; changed=True
                elif d>=2:   # y^2 = 2+2u-w+wu
                    for (da,db),cf in (((0,0),2),((1,0),2),((0,1),-1),((1,1),1)):
                        kk=(a+da,b+db,c,d-2,e); nxt[kk]=nxt.get(kk,0)+cf*v
                    changed=True
                elif e>=2:   # z^2 = 2+2u+w-wu
                    for (da,db),cf in (((0,0),2),((1,0),2),((0,1),1),((1,1),-1)):
                        kk=(a,b+db,c,d,e-2); kk=(a+da,b+db,c,d,e-2); nxt[kk]=nxt.get(kk,0)+cf*v
                    changed=True
                elif a>=12:  # u^12 = -sum (a_k + w b_k) u^k
                    for k,(ak,bk) in MP.items():
                        kk=(a-12+k,b,c,d,e); nxt[kk]=nxt.get(kk,0)-ak*v
                        kk2=(a-12+k,b+1,c,d,e); nxt[kk2]=nxt.get(kk2,0)-bk*v
                    changed=True
                else: nxt[(a,b,c,d,e)]=nxt.get((a,b,c,d,e),0)+v
            cur=nxt
        return K(cur)
    def __pow__(s,n):
        r=K.const(1); b=s
        while n:
            if n&1: r=r*b
            b=b*b; n>>=1
        return r
    def num(s,U):   # numeric value at 50 digits
        from mpmath import mpf, sqrt
        w=sqrt(2); r=sqrt(1-U); y=sqrt(2+2*U-w*(1-U)); z=sqrt(2+2*U+w*(1-U)); tot=mpf(0)
        for (a,b,c,d,e),v in s.d.items(): tot+=mpf(v.numerator)/v.denominator*U**a*w**b*r**c*y**d*z**e
        return tot
U_=K.mono(1); W_=K.mono(0,1); R_=K.mono(0,0,1); Yv=K.mono(0,0,0,1); Zv=K.mono(0,0,0,0,1)
BASIS=[(a,b,c,d,e) for a in range(12) for b in range(2) for c in range(2) for d in range(2) for e in range(2)]
BIDX={m:i for i,m in enumerate(BASIS)}
from mpmath import mp, mpf, findroot, diff, sqrt as msqrt
mp.dps=50
def apE(u):
    q=msqrt(2); return (4*q+2)/msqrt(1-u)+8/msqrt((2-q)+(2+q)*u)+8/msqrt((2+q)+(2-q)*u)
US=findroot(lambda u: diff(apE,u), mpf('0.31408936788920186517709977'))
# sanity: minimal polynomial and relations numerically
log("minpoly at u*:", mp.nstr((U_**12).num(US)-(U_**12).num(US),3), " check u^12 reduce consistency:", mp.nstr(abs((U_**13).num(US)-US**13),3), " y^2:",mp.nstr(abs((Yv*Yv).num(US)-(2+2*US-msqrt(2)*(1-US))),3))
# inverse via multiplication matrix
def mulmat(x):
    M=fmpq_mat(192,192)
    for j,m in enumerate(BASIS):
        col=x*K({m:Fr(1)})
        for k,v in col.d.items(): M[BIDX[k],j]=fmpq(v.numerator,v.denominator)
    return M
def inv(x):
    M=mulmat(x); rhs=fmpq_mat(192,1); rhs[0,0]=fmpq(1)
    sol=M.solve(rhs); return K({BASIS[i]:Fr(int(sol[i,0].p),int(sol[i,0].q)) for i in range(192) if sol[i,0]!=0})
log("field arithmetic ready; testing inverse of y:", mp.nstr(abs((inv(Yv)*Yv).num(US)-1),3))
# ---------------- antiprism data in K ----------------
half=Fr(1,2)
tA=U_                                  # square edge inner product u
tD=U_*2-K.const(1)                     # diagonal 2u-1
# cross: (1-u)/w - u  =  (1-u) w/2 - u
tN=(K.const(1)-U_)*W_*half-U_
tF=K.const(0)-(K.const(1)-U_)*W_*half-U_
CH={'A':W_*R_,'D':R_*2,'N':Yv,'F':Zv}      # chord lengths s = sqrt(2-2t): A: w r, D: 2r, N: y (s2), F: z (s4)
TT={'A':tA,'D':tD,'N':tN,'F':tF}
for k in CH: log(f"  chord {k}: s^2 vs 2-2t:", mp.nstr(abs((CH[k]*CH[k]).num(US)-(2-2*TT[k].num(US))),3))
types=[('F','F','A'),('F','D','N'),('F','N','A'),('D','A','A'),('N','N','A')]   # chord triples of the 5 triangle types (sorted t: see Tasks.lean)
# ---------------- S3 matrices symbolically, then evaluated in K ----------------
from bv import Sk as Sk_num
d=8; KMAX=5
uu,vv,tt=sp.symbols('uu vv tt')
def Q3s(k):
    c=sp.Poly(sp.chebyshevt(k,sp.Symbol('x')),sp.Symbol('x')).all_coeffs()[::-1]
    wq=(1-uu**2)*(1-vv**2); x=tt-uu*vv; out=0
    for j,cj in enumerate(c):
        if cj!=0 and (k-j)%2==0: out+=cj*x**j*wq**((k-j)//2)
    return sp.expand(out)
def S3poly(k):
    m=d-k+1; q=Q3s(k); ent={}
    for i in range(m):
        for j in range(m):
            tot=0
            for p in itertools.permutations((uu,vv,tt)):
                tot+=p[0]**i*p[1]**j*q.subs({uu:p[0],vv:p[1],tt:p[2]},simultaneous=True)
            ent[(i,j)]=sp.Poly(sp.expand(tot/6),uu,vv,tt)
    return ent
S3P={k:S3poly(k) for k in range(KMAX+1)}
log("S3 polynomials built")
def evalpoly(P,X,Yk,Z):
    """evaluate sympy Poly in (uu,vv,tt) at K elements X,Yk,Z (powers cached)"""
    tot=K()
    pw={}
    def pwr(base,n,key):
        if (key,n) not in pw: pw[(key,n)]=base**n if n>0 else K.const(1)
        return pw[(key,n)]
    for (i,j,l),c in P.terms():
        c=sp.Rational(c); term=pwr(X,i,'x')*pwr(Yk,j,'y')*pwr(Z,l,'z')*K.const(Fr(int(c.p),int(c.q)))
        tot=tot+term
    return tot
def dpoly(P,var): return sp.Poly(sp.diff(P.as_expr(),var),uu,vv,tt)
def S3K(k,X,Yk,Z,deriv=None):
    m=d-k+1; out={}
    for (i,j),P in S3P[k].items():
        if deriv is not None: P=dpoly(P,deriv)
        out[(i,j)]=evalpoly(P,X,Yk,Z)
    return out
# ---------------- unknown parametrisation, from task1_split2 (exact kernels) ----------------
C=json.load(open(os.path.join(here,'certificate_numerical.json')))
Tc=json.load(open(os.path.join(here,'certificate_r5373b.json')))
kv=json.load(open(os.path.join(here,'kernel_vectors_exact.json')))
# exact kernel vectors v_k(u) in K (rational functions of u -> numerator*inverse(denominator))
def toKpoly(P):
    tot=K()
    for (k,),c in sp.Poly(sp.expand(P),_u).terms():
        c=sp.Rational(c); tot=tot+U_**k*K.const(Fr(int(c.p),int(c.q)))
    return tot
VN={}; VD={}; V={}
for k in range(KMAX+1):
    VN[k]=[]; VD[k]=[]; V[k]=[]
    for s_ in kv[str(k)]:
        n_,d_=sp.fraction(sp.together(sp.sympify(s_)))
        VN[k].append(toKpoly(n_)); VD[k].append(toKpoly(d_)); V[k].append(toKpoly(n_)*inv(toKpoly(d_)))
log("exact kernel vectors in K (numerators/denominators kept)")
# INVERSE-FREE basis of v^perp: columns d_i e_i - n_i e_{p0}   (v_{p0} = 1), polynomial entries
def basis_perp(k):
    v=V[k]; n=len(v)
    p0=next(i for i in range(n) if v[i].d)
    assert v[p0].d=={(0,0,0,0,0):Fr(1)}
    cols=[]
    for i in range(n):
        if i==p0: continue
        col=[K() for _ in range(n)]; col[i]=VD[k][i]; col[p0]=K.const(0)-VN[k][i]
        cols.append(col)
    return cols
B={k:basis_perp(k) for k in range(KMAX+1)}
for k in range(KMAX+1):
    chk=max(abs(sum((V[k][i]*B[k][a][i]).num(US) for i in range(len(V[k])))) for a in range(len(B[k])))
    log(f"  v_{k} ⟂ basis check: {mp.nstr(chk,3)}")
# convert numerical H (in numerical orthonormal basis W_k) to the exact basis B_k: F_k = W H W^T = B H' B^T
Hn={}; Wn={}
for k in range(KMAX+1):
    Wk=np.array(Tc['W'][str(k)]); Hk=np.array(Tc['H'][str(k)]); Fk=Wk@Hk@Wk.T
    Bk=np.array([[float(B[k][a][i].num(US)) for a in range(len(B[k]))] for i in range(len(V[k]))])
    Bp=np.linalg.pinv(Bk); Hn[k]=Bp@Fk@Bp.T
log("numerical H in exact basis; sizes",[Hn[k].shape for k in range(KMAX+1)])
# unknown vector: a0,a1,lam, then H'_k upper triangle
idx=[]
for k in range(KMAX+1):
    m=Hn[k].shape[0]
    for i in range(m):
        for j in range(i,m): idx.append((k,i,j))
nx=3+len(idx); names=['a0','a1','lam']+[f"H{k}[{i},{j}]" for (k,i,j) in idx]
x0=[Fr(Tc['a0']),Fr(Tc['a1']),Fr(Tc['lam'])]+[Fr(float(Hn[k][i,j])) for (k,i,j) in idx]
log("unknowns:",nx)
# Fsum as a K-linear function of the unknowns: F(X,Y,Z) = sum_k sum_{a<=b} H[a,b] * (2-delta_ab) * (B_a^T S B_b)   [symmetric H]
def F_coeffs(X,Yk,Z,deriv=None):
    """returns dict unknown_index -> K coefficient for F at (X,Yk,Z)"""
    out={}
    for k in range(KMAX+1):
        S=S3K(k,X,Yk,Z,deriv); n=len(V[k]); cols=B[k]
        # precompute S*col_b
        Scol=[[sum((S[(i,j)]*cols[b][j] for j in range(n)),K()) for i in range(n)] for b in range(len(cols))]
        for p,(kk,a,b) in enumerate(idx):
            if kk!=k: continue
            val=sum((cols[a][i]*Scol[b][i] for i in range(n)),K())
            if a!=b: val=val*2
            out[3+p]=val
    return out
one=K.const(1)
rows=[]   # each row: (dict unknown->K, rhs K)
# bound: (64 a0 - 8(a0+a1) - 8 F(1,1,1))/2 = E(u)  =>  28 a0 - 4 a1 - 4F111 - E = 0
Fc=F_coeffs(one,one,one)
Eu=(W_*4+K.const(2))*inv(R_)+K.const(8)*inv(Yv)+K.const(8)*inv(Zv)
row={0:K.const(28),1:K.const(-4)}
for p,v in Fc.items(): row[p]=v*K.const(-4)
rows.append((row,Eu)); log("row: bound")
# pair: P(s)=(1-18lam) - s(a0 + a1 t + 3F(1,t,t)) = 0 ; P'(s) = -(a0 + a1 t + 3F) + s^2 (a1 + 3 dF/dt) = 0   (t=1-s^2/2, dt/ds=-s)
for key in ['A','D','N','F']:
    s=CH[key]; t=TT[key]; s2v=s*s
    Fc=F_coeffs(one,t,t); Fd=F_coeffs(one,t,t,deriv=vv); Fd2=F_coeffs(one,t,t,deriv=tt)
    # F(1,t,t): d/dt = ∂_v + ∂_t
    row={2:K.const(-18),0:K.const(0)-s,1:K.const(0)-s*t}
    for p,v in Fc.items(): row[p]=row.get(p,K())+v*K.const(-3)*s
    rows.append((row,K.const(-1)))          # ... = -1  i.e. -18lam - s a0 - s t a1 - 3 s F = -1
    row2={0:K.const(-1),1:K.const(0)-t+s2v}
    for p,v in Fc.items(): row2[p]=row2.get(p,K())+v*K.const(-3)
    for p,v in Fd.items(): row2[p]=row2.get(p,K())+v*K.const(3)*s2v
    for p,v in Fd2.items(): row2[p]=row2.get(p,K())+v*K.const(3)*s2v
    rows.append((row2,K()))
    log(f"rows: pair {key}")
# triangle: T = lam(1/p+1/q+1/r) - F(u,v,t) = 0 ; ∂T/∂u = lam h'(u) - ∂F/∂u,  h(t)=1/s, h'(t)=1/s^3  (t = 1 - s^2/2)
for (pk,qk,rk) in types:
    ps,qs,rs=CH[pk],CH[qk],CH[rk]; tu,tv,tw=TT[pk],TT[qk],TT[rk]
    Fc=F_coeffs(tu,tv,tw)
    row={2:inv(ps)+inv(qs)+inv(rs)}
    for p,v in Fc.items(): row[p]=K()-v
    rows.append((row,K()))
    for ax,s in zip((uu,vv,tt),(ps,qs,rs)):
        Fd=F_coeffs(tu,tv,tw,deriv=ax)
        row={2:inv(s*s*s)}
        for p,v in Fd.items(): row[p]=K()-v
        rows.append((row,K()))
    log(f"rows: triangle {pk}{qk}{rk}")
log("total rows:",len(rows))
# numeric check of residuals at x0 (should be ~1e-7 or better)
def resid(x):
    out=[]
    for row,rhs in rows:
        tot=-rhs.num(US)
        for p,v in row.items(): tot+=v.num(US)*mpf(x[p].numerator)/x[p].denominator
        out.append(tot)
    return out
r0=resid(x0); log("max |residual| at numerical x0:", mp.nstr(max(abs(v) for v in r0),4))
json.dump(dict(names=names),open(os.path.join(here,'task1_names.json'),'w'))
import pickle; pickle.dump(dict(rows=[({p:v.d for p,v in row.items()},rhs.d) for row,rhs in rows],x0=[str(v) for v in x0],names=names,idx=idx),open(os.path.join(here,'task1_rows_polybasis.pkl'),'wb'))
log("rows saved (task1_rows.pkl). Next: rank-revealing pivot selection and exact solve (task1_solve.py).")
