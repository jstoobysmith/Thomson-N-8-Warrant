"""[Tri5b] Generate the covering tree exactly as `Thomson/Tri5b/Skip.lean` reads it.

The tree shape is a pre-order bit stream (`1` = split, `0` = leaf); everything else — the split
axis and point, the tangent chords, the S-procedure multiplier — is recomputed by the Lean checker,
so those rules are mirrored here exactly.  Leaves are accepted on a float model with a safety
factor and can be re-verified with the exact integer model (`--exact`)."""
import sys, math, pickle
import tri5b_mirror as M
import tri5b_cubes as CU
from math import isqrt

SCALE = M.SCALE
UHI = 107474839 * 5 * 10 ** 31           # 1 - (9619/10000)^2/2, in fixed point
ROOT = (-SCALE, UHI, -SCALE, UHI, -SCALE, UHI)
CUBE = CU.CUBE                            # CUBE[m][i] = (lo, hi)
SIGMAS = [0, 10**36, 3*10**36, 10**37, 3*10**37, 10**38, 3*10**38, 10**39, 3*10**39,
          10**40, 3*10**40, 10**41, 3*10**41, 10**42]
MG = 10 ** 30                             # certified margin, 1e-10

# ---------- the certificate's tensors ----------
import tri5b_build as B
TENS = None
EPS_EXP = 12                              # the pivot enclosure assumed: 10^-EPS_EXP
def tensors():
    """the tensor of F with the 24 pivot slots widened by the pivot uncertainty"""
    global TENS
    if TENS is None:
        orig = B.HI
        E = 10 ** (40 - EPS_EXP)
        def HIe(k, a, b, E=E, f=orig):
            v = f(k, a, b)
            if (k, a, b) in B.SLOT or (k, b, a) in B.SLOT: return (v[0] - E, v[1] + E)
            return v
        B.HI = HIe
        MTab = B.build_M(); TENS = B.build_F(MTab)
        B.HI = orig
    return TENS
GRAM = {(0,0,0): M.cst(SCALE), (1,1,1): M.cst(2*SCALE),
        (2,0,0): M.cst(-SCALE), (0,2,0): M.cst(-SCALE), (0,0,2): M.cst(-SCALE)}

# ---------- Lean's splitting rule ----------
def widths(b): return (b[1]-b[0], b[3]-b[2], b[5]-b[4])
def splitAxis(b):
    wu, wv, wt = widths(b)
    if wv <= wu and wt <= wu: return 0
    return 1 if wt <= wv else 2
def facesIn(b, ax):
    lo, hi = b[2*ax], b[2*ax+1]
    return sorted({f for m in range(5) for f in CUBE[m][ax] if lo < f < hi})
def splitPoint(b, ax):
    fs = facesIn(b, ax)
    return fs[0] if fs else (b[2*ax] + b[2*ax+1]) // 2
def lower(b, ax, m):
    o = list(b); o[2*ax+1] = m; return tuple(o)
def upper(b, ax, m):
    o = list(b); o[2*ax] = m; return tuple(o)
def ctr(lo, hi): return (lo + hi) // 2
def hal(lo, hi):
    c = ctr(lo, hi); return max(hi - c, c - lo)
def tanChord(c): return isqrt(SCALE * (2 * SCALE - 2 * c))

# ---------- skip tests ----------
def in_cube(b):
    return any(all(CUBE[m][i][0] <= b[2*i] and b[2*i+1] <= CUBE[m][i][1] for i in range(3))
               for m in range(5))
def sorted_out(b):
    return b[3] < b[0] or b[5] < b[2]
def gram_out_exact(b):
    if not (b[0] < b[1] and b[2] < b[3] and b[4] < b[5]): return False
    T = M.tsmul(M.cst(-SCALE), GRAM)
    S = M.tshift(T, ctr(b[0],b[1]), ctr(b[2],b[3]), ctr(b[4],b[5]))
    lo, rad = M.toTM(S, hal(b[0],b[1]), hal(b[2],b[3]), hal(b[4],b[5]))
    return M.loBound(lo, rad) >= 1
def skipOK(b):
    return sorted_out(b) or gram_out_exact(b) or in_cube(b)

# ---------- the leaf test ----------
def leaf_exact(b, sig, F):
    n1, n2, n3 = (tanChord(ctr(b[0],b[1])), tanChord(ctr(b[2],b[3])), tanChord(ctr(b[4],b[5])))
    if not (n1 > 0 and n2 > 0 and n3 > 0): return False
    if not (b[0] < b[1] and b[2] < b[3] and b[4] < b[5]): return False
    LAM = 97932235147 * 10 ** 27
    def tanent(n):
        A = M.iofdiv(SCALE * (3*n*n - 2*SCALE*SCALE), 2*n**3)
        Bc = M.iofdiv(SCALE ** 3, n ** 3)
        return M.imul(M.cst(LAM), A), M.imul(M.cst(LAM), Bc)
    a1, b1 = tanent(n1); a2, b2 = tanent(n2); a3, b3 = tanent(n3)
    T = {(0,0,0): M.iadd(M.iadd(M.imul(M.cst(LAM), M.iofdiv(SCALE*(3*n1*n1-2*SCALE*SCALE), 2*n1**3)),
                                M.imul(M.cst(LAM), M.iofdiv(SCALE*(3*n2*n2-2*SCALE*SCALE), 2*n2**3))),
                         M.imul(M.cst(LAM), M.iofdiv(SCALE*(3*n3*n3-2*SCALE*SCALE), 2*n3**3))),
         (1,0,0): b1, (0,1,0): b2, (0,0,1): b3}
    P = M.tsub(M.tsub(T, F), M.tsmul(M.cst(sig), GRAM))
    S = M.tshift(P, ctr(b[0],b[1]), ctr(b[2],b[3]), ctr(b[4],b[5]))
    lo, rad = M.toTM(S, hal(b[0],b[1]), hal(b[2],b[3]), hal(b[4],b[5]))
    return M.loBound(lo, rad) >= MG
def leafAuto_exact(b, F):
    return any(leaf_exact(b, s, F) for s in SIGMAS)

# ---------- fast float model of the same leaf test (for the search) ----------
import numpy as np
from math import comb
def float_tensor(F):
    A = np.zeros((9,9,9))
    for (i,j,k),v in F.items(): A[i,j,k] = (v[0]+v[1])/2 / SCALE
    return A
def shift_float(A, c):
    out = A.copy()
    for ax in range(3):
        Tm = np.zeros((9,9))
        for i in range(9):
            for j in range(i+1): Tm[j,i] = comb(i,j) * c[ax]**(i-j)
        out = np.tensordot(Tm, out, axes=([1],[ax])); out = np.moveaxis(out,0,ax)
    return out
GF = np.zeros((9,9,9)); GF[0,0,0]=1.0; GF[1,1,1]=2.0; GF[2,0,0]=-1.0; GF[0,2,0]=-1.0; GF[0,0,2]=-1.0
LAMF = 97932235147/10**13
def leaf_float(b, sig, AF):
    c = [ctr(b[0],b[1])/SCALE, ctr(b[2],b[3])/SCALE, ctr(b[4],b[5])/SCALE]
    h = [hal(b[0],b[1])/SCALE, hal(b[2],b[3])/SCALE, hal(b[4],b[5])/SCALE]
    n = [tanChord(ctr(b[2*i],b[2*i+1]))/SCALE for i in range(3)]
    S = shift_float(-AF - sig*GF, c)
    val = S[0,0,0]; g=[0.0]*3; q=[[0.0]*3 for _ in range(3)]; tail=0.0
    for i in range(3):
        idx=[0,0,0]; idx[i]=1; g[i]+=S[tuple(idx)]*h[i]
        idx=[0,0,0]; idx[i]=2; q[i][i]+=S[tuple(idx)]*h[i]*h[i]
    for i in range(3):
        for j in range(i+1,3):
            idx=[0,0,0]; idx[i]=1; idx[j]=1; q[i][j]+=S[tuple(idx)]*h[i]*h[j]
    for i in range(9):
        for j in range(9):
            for k in range(9):
                if i+j+k>=3 and S[i,j,k]!=0.0: tail += abs(S[i,j,k])*h[0]**i*h[1]**j*h[2]**k
    for i in range(3):
        a0 = n[i]
        val += LAMF*(1/a0 - (2-2*c[i]-a0*a0)/(2*a0**3))
        g[i] += LAMF*(2*h[i])/(2*a0**3)
    def loAx(gg,qq):
        if 2*qq <= abs(gg): return qq-abs(gg)
        return -(gg*gg)/(4*qq)
    lb = val - abs(q[0][1]) - abs(q[0][2]) - abs(q[1][2]) - tail
    for i in range(3): lb += loAx(g[i], q[i][i])
    return lb
def leafAuto_float(b, AF, thresh):
    for s in SIGMAS:
        if leaf_float(b, s/SCALE, AF) > thresh: return True
    return False

# ---------- the driver ----------
MAXDEPTH = 60
def build(b, AF, thresh, depth=0, stats=None):
    """returns the pre-order bit list, or raises on failure"""
    if stats is not None: stats['n'] += 1
    if sorted_out(b) or in_cube(b) or gram_out_exact(b):
        if stats is not None: stats['skip'] += 1
        return [0]
    if leafAuto_float(b, AF, thresh):
        if stats is not None: stats['leaf'] += 1
        return [0]
    if depth >= MAXDEPTH:
        raise Exception("depth limit at %s" % (b,))
    ax = splitAxis(b); m = splitPoint(b, ax)
    if not (b[2*ax] < m < b[2*ax+1]): raise Exception("bad split %s %d %d" % (b, ax, m))
    return [1] + build(lower(b,ax,m), AF, thresh, depth+1, stats) \
               + build(upper(b,ax,m), AF, thresh, depth+1, stats)

def leaves_of(b, AF, thresh, depth=0, out=None):
    if out is None: out = []
    if sorted_out(b) or in_cube(b) or gram_out_exact(b): return out
    if leafAuto_float(b, AF, thresh): out.append(b); return out
    ax = splitAxis(b); m = splitPoint(b, ax)
    leaves_of(lower(b,ax,m), AF, thresh, depth+1, out)
    leaves_of(upper(b,ax,m), AF, thresh, depth+1, out)
    return out

def bits_to_nat(bits):
    n = 0
    for i, x in enumerate(bits): n |= x << i
    return n | (1 << len(bits))          # sentinel

if __name__ == "__main__":
    import time
    F = tensors(); AF = float_tensor(F)
    thresh = 2 * MG / SCALE
    st = {'n':0,'skip':0,'leaf':0}
    t = time.time()
    bits = build(ROOT, AF, thresh, stats=st)
    print("nodes %d  skipped %d  checked %d  bits %d  (%.1f s)"
          % (st['n'], st['skip'], st['leaf'], len(bits), time.time()-t))
    n = bits_to_nat(bits)
    print("certificate: %d bits, %d decimal digits" % (len(bits), len(str(n))))
    pickle.dump({'bits': bits, 'nat': n}, open('tri5b_tree.pkl','wb'))
