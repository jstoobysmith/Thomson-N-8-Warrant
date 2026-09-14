from fractions import Fraction as F
from mpmath import mp, mpf, sqrt
mp.dps=40
atoms=[F(-153,200),F(-19,25),F(-27,50),F(-107,200),F(-73,200),F(6,25),F(49,200)]
wts  =[F(9179,2000),F(21963,5000),F(5727,10000),F(653,2000),F(17269,10000),
       F(44701,10000),F(119217,10000)]
assert sum(wts)==28, sum(wts)
print("total mass:", sum(wts), "(exactly 28)")
print("all atoms in [-1,1):", all(-1<=a<1 for a in atoms))
print("all weights > 0    :", all(w>0 for w in wts))

# exact Legendre evaluation by recurrence, exact rational arithmetic
KMAX=100
P=[[F(1)]*len(atoms),[a for a in atoms]]
for k in range(1,KMAX):
    P.append([ (F(2*k+1)*atoms[i]*P[k][i]-F(k)*P[k-1][i])/F(k+1) for i in range(len(atoms))])
worst=None
for k in range(1,KMAX+1):
    m=sum(wts[i]*P[k][i] for i in range(len(atoms)))
    if worst is None or m<worst[1]: worst=(k,m)
    assert m>=-4, (k,float(m))
print(f"\nEXACT check: sum_i w_i P_k(t_i) >= -4 for all k=1..{KMAX}:  VERIFIED")
print(f"   worst case k={worst[0]}:  {float(worst[1]):.8f}  (slack {float(worst[1]+4):.8f})")

# Bernstein tail:  |P_k(cos th)| <= sqrt(2/(pi k sin th))
sint=[sqrt(1-mpf(a.numerator)/a.denominator*(mpf(a.numerator)/a.denominator)) for a in atoms]
smin=min(sint)
tail=lambda K: 28*sqrt(2/(mp.pi*K*smin))
print(f"\n   min_i sin(theta_i) = {mp.nstr(smin,10)}")
print(f"   Bernstein tail for k>{KMAX}: |sum w_i P_k| <= {mp.nstr(tail(KMAX),10)} < 4  -> constraints hold for ALL k")

V=sum(mpf(w.numerator)/w.denominator/sqrt(2-2*(mpf(a.numerator)/a.denominator))
      for a,w in zip(atoms,wts))
print(f"\n   V = sum_i w_i / sqrt(2-2 t_i) = {mp.nstr(V,20)}")
print(f"   E(u*)                          = 19.675287861232762264")
print(f"   V < E(u*):  {V < mpf('19.675287861232762264')}    margin = {mp.nstr(mpf('19.675287861232762264')-V,10)}")
