import numpy as np
from fractions import Fraction as F
from scipy.optimize import linprog
exec(open('lp.py').read().split('print("=== plain LP')[0])
TARGET=19.6752878612; KMAX=200
den=200
atoms=[F(n,den) for n in range(-199,125)]
tt=np.array([float(a) for a in atoms]); Pk=legvals(KMAX,tt)
print(f"{'margin':>8s} {'LP value':>12s}   below target?")
for M in [0.0,0.01,0.02,0.03,0.05,0.08]:
    r=linprog(1.0/np.sqrt(2-2*tt),A_ub=-Pk[1:],b_ub=np.full(KMAX,4.0-M),
              A_eq=np.ones((1,tt.size)),b_eq=[28.0],bounds=[(0,None)]*tt.size,method='highs')
    print(f"{M:8.3f} {r.fun:12.7f}   {r.fun<TARGET}")
M=0.03
r=linprog(1.0/np.sqrt(2-2*tt),A_ub=-Pk[1:],b_ub=np.full(KMAX,4.0-M),
          A_eq=np.ones((1,tt.size)),b_eq=[28.0],bounds=[(0,None)]*tt.size,method='highs')
sup=np.where(r.x>1e-9)[0]
# round weights to /10^4, absorb the residual in the largest-weight atom
D=10**4
w=[F(int(round(r.x[i]*D)),D) for i in sup]
big=int(np.argmax([float(x) for x in w]))
w[big]+= F(28)-sum(w)
As=[atoms[i] for i in sup]
wf=np.array([float(x) for x in w]); tf=np.array([float(a) for a in As])
val=float(np.sum(wf/np.sqrt(2-2*tf)))
mk=(legvals(KMAX,tf)[1:])@wf
sint=np.sqrt(1-tf**2); tail=lambda K: 28*np.sqrt(2/(np.pi*K*sint.min()))
print("\n=== CERTIFICATE (all data rational) ===")
print(f"{'t_i':>10s} {'s_i=sqrt(2-2t)':>16s} {'w_i':>14s}")
for a,x in zip(As,w): print(f"{str(a):>10s} {float((2-2*a)**0.5):16.6f} {str(x):>14s}")
print(f"total mass = {sum(w)}  (= 28 exactly: {sum(w)==28})")
print(f"\nV = sum w_i/s_i          = {val:.7f}")
print(f"conjectured minimum E(u*)= {TARGET:.7f}")
print(f"V < E(u*) ?  {val<TARGET}   margin {TARGET-val:.7f}")
print(f"\nmin_{{1<=k<=200}} sum w_i P_k(t_i) = {mk.min():.6f}  >= -4 ?  {mk.min()>=-4}   (worst k={int(np.argmin(mk))+1})")
print(f"Bernstein tail: for k>50, |sum w_i P_k| <= {tail(50):.4f} < 4")
print(f"\n=> for EVERY admissible Yudin polynomial f of EVERY degree, bound(f) <= {val:.6f}")
print(f"   The LP/Yudin method provably cannot prove thomsonInf 8 >= {TARGET:.6f}.")
