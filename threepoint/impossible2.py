import numpy as np
from fractions import Fraction as F
from scipy.optimize import linprog
exec(open('/private/tmp/claude-502/-Users-js4814-Documents-GitHub-MyComandCenter/0962e486-bbae-4fbd-bb57-0b9929536462/scratchpad/lp.py').read().split('print("=== plain LP')[0])
TARGET=19.6752878612

# PRIMAL of the LP relaxation: a "virtual pair distribution" w on inner products t,
#   total mass 28,  sum_i w_i P_k(t_i) >= -4  for all k>=1,  minimise sum_i w_i / sqrt(2-2t_i).
# Weak duality: ANY feasible w caps EVERY Yudin/LP bound of EVERY degree.
KMAX=200
tg=np.linspace(-0.999,0.62,4000)
Pk=legvals(KMAX,tg)                      # (KMAX+1, m)
A_ub=-Pk[1:]                             # -sum w P_k <= 4
b_ub=np.full(KMAX,4.0)
A_eq=np.ones((1,tg.size)); b_eq=[28.0]
cost=1.0/np.sqrt(2-2*tg)
r=linprog(cost,A_ub=A_ub,b_ub=b_ub,A_eq=A_eq,b_eq=b_eq,bounds=[(0,None)]*tg.size,method='highs')
w=r.x; sup=np.where(w>1e-7)[0]
print("=== optimal feasible 'virtual configuration' (LP primal) ===")
print(f"   value = {r.fun:.7f}   (target {TARGET:.7f})")
for i in sup: print(f"      t={tg[i]:+.5f}  s={np.sqrt(2-2*tg[i]):.5f}  weight={w[i]:.5f}")


# --- explicit RATIONAL certificate on a rational grid, with a safety margin ---
print("\n=== explicit rational certificate ===")
den=200
atoms=[F(n,den) for n in range(-199,125)]          # t in [-0.995, 0.62], denominators 200
tt=np.array([float(a) for a in atoms])
Pk2=legvals(KMAX,tt)
MARGIN=0.15                                        # demand sum w P_k >= -4 + MARGIN
r2=linprog(1.0/np.sqrt(2-2*tt), A_ub=-Pk2[1:], b_ub=np.full(KMAX,4.0-MARGIN),
           A_eq=np.ones((1,tt.size)), b_eq=[28.0], bounds=[(0,None)]*tt.size, method='highs')
print(f"   LP on rational grid (margin {MARGIN}) : value = {r2.fun:.7f}")
sup=np.where(r2.x>1e-9)[0]
wts=[F(r2.x[i]).limit_denominator(10**6) for i in sup]
tot=sum(wts); wts=[x*F(28)/tot for x in wts]
As=[atoms[i] for i in sup]
print(f"   support: {len(As)} atoms")
for a,w in zip(As,wts):
    print(f"      t = {str(a):>9s}   s = sqrt(2-2t) = {float((2-2*a)**0.5):.6f}   w = {str(w)}")
print("   total mass =", sum(wts), " (must be 28)")
wf=np.array([float(x) for x in wts]); tf=np.array([float(a) for a in As])
val=float(np.sum(wf/np.sqrt(2-2*tf)))
print(f"\n   certificate energy V = {val:.7f}")
print(f"   conjectured minimum  = {TARGET:.7f}")
print(f"   V < target ?  {val<TARGET}    margin = {TARGET-val:.7f}")
Pk3=legvals(KMAX,tf); mk=Pk3[1:]@wf
print(f"\n   min_{{1<=k<={KMAX}}} sum_i w_i P_k(t_i) = {mk.min():.6f}  (need >= -4)   worst k={int(np.argmin(mk))+1}")
sint=np.sqrt(1-tf**2)
for K in [50,100,200]:
    t_=28*np.sqrt(2/(np.pi*K*sint.min()))
    print(f"   Bernstein tail k>{K}: |sum w_i P_k| <= {t_:.4f}  {'< 4  OK' if t_<4 else ''}")
print(f"\n   => every Yudin/LP bound of every degree is <= {val:.6f} < {TARGET:.6f}")
