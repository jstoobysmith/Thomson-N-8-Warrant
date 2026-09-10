import numpy as np
from scipy.optimize import linprog
from numpy.polynomial import legendre as L

N = 8
TARGET = 19.6752878612   # conjectured min = E(u*)

def legvals(D, t):
    """matrix M[k,i] = P_k(t_i), k=0..D"""
    t = np.asarray(t, dtype=float)
    M = np.empty((D+1, t.size))
    M[0] = 1.0
    if D >= 1: M[1] = t
    for k in range(1, D):
        M[k+1] = ((2*k+1)*t*M[k] - k*M[k-1])/(k+1)
    return M

def lp_bound(D, intervals, ngrid=40000):
    """max (N^2 c0 - N f(1))/2 s.t. c_k>=0 (k>=1), f(1-s^2/2) <= 1/s on given s-intervals."""
    ss = []
    total = sum(b-a for a,b in intervals)
    for a,b in intervals:
        n = max(200, int(ngrid*(b-a)/total))
        ss.append(np.linspace(a, b, n))
    s = np.concatenate(ss)
    t = 1 - s**2/2
    M = legvals(D, t)                 # (D+1, m)
    A_ub = M.T                        # f(t) <= 1/s
    b_ub = 1.0/s
    c_obj = -(np.full(D+1, -N/2.0))   # minimize -(N^2 c0/2 - N/2 * sum c_k)
    c_obj = np.full(D+1, N/2.0); c_obj[0] -= N*N/2.0   # = -(objective)
    bounds = [(0, None)]*(D+1)
    res = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method='highs')
    if not res.success: return None, None
    return -res.fun, res.x

def gfun(ck, s):
    t = 1 - np.asarray(s)**2/2
    M = legvals(len(ck)-1, t)
    return 1.0/np.asarray(s) - ck @ M

def allowed_set(ck, budget, lo=1e-3, hi=2.0, n=400001):
    s = np.linspace(lo, hi, n)
    g = gfun(ck, s)
    ok = g <= budget
    ivs = []
    i = 0
    while i < n:
        if ok[i]:
            j = i
            while j+1 < n and ok[j+1]: j += 1
            ivs.append((s[i], s[j]))
            i = j+1
        else: i += 1
    return ivs

def intersect(A, B):
    out = []
    for a1,b1 in A:
        for a2,b2 in B:
            lo, hi = max(a1,a2), min(b1,b2)
            if hi > lo: out.append((lo,hi))
    return out

print("=== plain LP bound vs degree (full range s in (0,2]) ===")
for D in [3,4,7,12,16,20,24,30]:
    B, ck = lp_bound(D, [(1e-3, 2.0)])
    print(f"  D={D:3d}  bound={B:.6f}   gap to target={TARGET-B:.6f}")

print()
print("=== bootstrap: restrict s to {g <= budget}, re-solve, repeat ===")
# antiprism reference distances
u = 0.3140893673
r2 = 1-u
aps = sorted([np.sqrt(2-2*u), np.sqrt(2-2*(r2/np.sqrt(2)-u)), np.sqrt(2+2*(2*u-1)*-1*-1),
              np.sqrt(2-2*(2*u-1)), np.sqrt(2+2*(r2/np.sqrt(2)+u))])
aps = sorted(set(round(x,6) for x in [np.sqrt(2-2*u), np.sqrt(2-2*(r2/np.sqrt(2)-u)),
                                      np.sqrt(2-2*(2*u-1)), np.sqrt(2+2*(r2/np.sqrt(2)+u))]))
print("antiprism distances:", aps)

D = 20
allowed = [(1e-3, 2.0)]
for it in range(12):
    B, ck = lp_bound(D, allowed)
    budget = TARGET - B
    new = allowed_set(ck, budget)
    allowed = intersect(allowed, new)
    tot = sum(b-a for a,b in allowed)
    print(f"it {it}: bound={B:.6f} budget={budget:.6f} |allowed|={tot:.4f} "
          f"intervals={[(round(a,4),round(b,4)) for a,b in allowed]}")
    if B > TARGET:
        print("  *** bound exceeds target: contradiction -> theorem proved ***"); break
