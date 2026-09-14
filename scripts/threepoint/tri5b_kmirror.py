"""[Tri5b] Bit-for-bit Python mirror of the kernel-layer checker (Thomson/TriangleGlobal/K{Poly,TM,Leaf}.lean).

Every operation reproduces the Lean one exactly, so a covering tree accepted here is accepted by
`decide +kernel`.  `tri5b_kparts.py` replays the tree of `tri5b_tree2.pkl` and emits the pieces."""
import sys, re, pickle
from math import isqrt
SCALE = 10 ** 40
SCALE2 = SCALE * SCALE
SCALE3 = SCALE ** 3
LAM = 97932235147 * 10 ** 27
MG = 10 ** 30
SIGMAS = [0, 10**36, 3*10**36, 10**37, 3*10**37, 10**38, 3*10**38, 10**39, 3*10**39,
          10**40, 3*10**40, 10**41, 3*10**41, 10**42]

def fdiv(a, b): return a // b           # Int.ediv for b > 0
def cdiv(a, b): return -((-a) // b)
# ---- Itv ----
ZERO = (0, 0)
def cst(n): return (n, n)
def iadd(I, J): return (I[0] + J[0], I[1] + J[1])
def ineg(I): return (-I[1], -I[0])
def isub(I, J): return iadd(I, ineg(J))
def mulC(a, I):
    if a >= 0: return (fdiv(a * I[0], SCALE), cdiv(a * I[1], SCALE))
    return (fdiv(a * I[1], SCALE), cdiv(a * I[0], SCALE))
def mulQ(n, d, I): return (fdiv(n * I[0], d), cdiv(n * I[1], d))
def iofdiv(n, d): return (fdiv(n * SCALE, d), cdiv(n * SCALE, d))
def maxabs(I): return max(abs(I[0]), abs(I[1]))
# ---- generic list ops ----
def addC(add, c, l):
    if not l: return [c]
    return [add(c, l[0])] + l[1:]
def mulXA(add, smul, p):
    if not p: return []
    return [smul(p[0])] + addC(add, p[0], mulXA(add, smul, p[1:]))
def shiftL(add, smul, p):
    if not p: return []
    return addC(add, p[0], mulXA(add, smul, shiftL(add, smul, p[1:])))
def scaleGen(mq, h, hp, Sp, p):
    out = []
    for c in p:
        out.append(mq(hp, Sp, c)); hp, Sp = hp * h, Sp * SCALE
    return out
# padded add/sub/neg at the three levels
def addI1(p, q):
    if not p: return q
    if not q: return p
    return [iadd(p[0], q[0])] + addI1(p[1:], q[1:])
def addI2(p, q):
    if not p: return q
    if not q: return p
    return [addI1(p[0], q[0])] + addI2(p[1:], q[1:])
def negI1(p): return [ineg(x) for x in p]
def negI2(p): return [negI1(x) for x in p]
def negI3(p): return [negI2(x) for x in p]
def subI1(p, q):
    if not p: return negI1(q)
    if not q: return p
    return [isub(p[0], q[0])] + subI1(p[1:], q[1:])
def subI2(p, q):
    if not p: return negI2(q)
    if not q: return p
    return [subI1(p[0], q[0])] + subI2(p[1:], q[1:])
def subI3(p, q):
    if not p: return negI3(q)
    if not q: return p
    return [subI2(p[0], q[0])] + subI3(p[1:], q[1:])
def smulI1(a, p): return [mulC(a, x) for x in p]
def smulI2(a, p): return [smulI1(a, x) for x in p]
def smulI3(a, p): return [smulI2(a, x) for x in p]
# shifts and scalings
def shI3(a, T): return [[shiftL(iadd, lambda I: mulC(a, I), r) for r in P] for P in T]
def shI2(a, T): return [shiftL(addI1, lambda r: smulI1(a, r), P) for P in T]
def shI1(a, T): return shiftL(addI2, lambda P: smulI2(a, P), T)
def scI3(h, T): return [[scaleGen(mulQ, h, 1, 1, r) for r in P] for P in T]
def scI2(h, T): return [scaleGen(lambda n, d, r: [mulQ(n, d, I) for I in r], h, 1, 1, P) for P in T]
def scI1(h, T): return scaleGen(lambda n, d, P: [[mulQ(n, d, I) for I in r] for r in P], h, 1, 1, T)
def shsc(a, b, d, h1, h2, h3, T):
    return scI1(h1, scI2(h2, scI3(h3, shI3(d, shI2(b, shI1(a, T))))))
# TM
def radEnt(d, I): return (I[1] - I[0]) if d <= 2 else maxabs(I)
def rad1(d, P): return sum(radEnt(d + i, I) for i, I in enumerate(P))
def rad2(d, P): return sum(rad1(d + i, R) for i, R in enumerate(P))
def rad3(d, P): return sum(rad2(d + i, R) for i, R in enumerate(P))
def getL(L, i, j, k):
    try: return L[i][j][k]
    except IndexError: return ZERO
def loAxis(g, q):
    if 2 * q <= abs(g): return q - abs(g)
    return -((g * g + 4 * q - 1) // (4 * q))
def loBound(U):
    c = getL(U,0,0,0)[0]; g1 = getL(U,1,0,0)[0]; g2 = getL(U,0,1,0)[0]; g3 = getL(U,0,0,1)[0]
    q11 = getL(U,2,0,0)[0]; q12 = getL(U,1,1,0)[0]; q13 = getL(U,1,0,1)[0]
    q22 = getL(U,0,2,0)[0]; q23 = getL(U,0,1,1)[0]; q33 = getL(U,0,0,2)[0]
    return c + loAxis(g1, q11) + loAxis(g2, q22) + loAxis(g3, q33) - abs(q12) - abs(q13) - abs(q23) - rad3(0, U)
def geBound(m, U): return m <= loBound(U)
# sqrt
def sqrtIter(fuel, n, x):
    while fuel > 0:
        y = (x + n // x) // 2
        if x <= y: return x
        x = y; fuel -= 1
    return x
def nsqrt(n):
    if n == 0: return 0
    return sqrtIter(200, n, 2 ** (n.bit_length() - 1 >> 1) * 2)  # 2^(log2 n / 2 + 1)
def tanChordK(c):
    n = SCALE * (2 * SCALE - 2 * c)
    r = nsqrt(max(n, 0))
    assert r == isqrt(max(n, 0)), (c, r, isqrt(max(n,0)))
    return r
def tanA(n): return mulC(LAM, iofdiv(SCALE * (3 * n * n - 2 * SCALE2), 2 * (n * n * n)))
def tanB(n): return mulC(LAM, iofdiv(SCALE3, n * n * n))
def tanL(n1, n2, n3):
    return [[[iadd(iadd(tanA(n1), tanA(n2)), tanA(n3)), tanB(n3)], [tanB(n2)]], [[tanB(n1)]]]
GRAML = [[[cst(1 * SCALE), ZERO, cst(-1 * SCALE)], [], [cst(-1 * SCALE)]],
         [[], [ZERO, cst(2 * SCALE)]],
         [[cst(-1 * SCALE)]]]
# boxes
def ctr(lo, hi): return (lo + hi) // 2
def hal(lo, hi):
    c = ctr(lo, hi); return max(hi - c, c - lo)
def kleafCheck(CL, mg, B):
    ulo, uhi, vlo, vhi, tlo, thi = B
    a, b, d = ctr(ulo, uhi), ctr(vlo, vhi), ctr(tlo, thi)
    h1, h2, h3 = hal(ulo, uhi), hal(vlo, vhi), hal(tlo, thi)
    n1, n2, n3 = tanChordK(a), tanChordK(b), tanChordK(d)
    if not (0 < n1 and 0 < n2 and 0 < n3 and ulo < uhi and vlo < vhi and tlo < thi): return None
    S = shsc(a, b, d, h1, h2, h3, subI3(tanL(n1, n2, n3), CL))
    T = shsc(a, b, d, h1, h2, h3, GRAML)
    for i, s in enumerate(SIGMAS):
        if 0 <= s and geBound(mg, subI3(S, smulI3(s, T))): return i
    return None
def kskipOK(CUBE, B):
    ulo, uhi, vlo, vhi, tlo, thi = B
    if vhi < ulo or thi < vlo: return True
    if ulo < uhi and vlo < vhi and tlo < thi:
        U = shsc(ctr(ulo,uhi), ctr(vlo,vhi), ctr(tlo,thi), hal(ulo,uhi), hal(vlo,vhi), hal(tlo,thi), smulI3(-SCALE, GRAML))
        if geBound(1, U): return True
    return any(all(CUBE[m][i][0] <= B[2*i] and B[2*i+1] <= CUBE[m][i][1] for i in range(3)) for m in range(5))
# ---- the tensor of F, from CFTable.lean ----
def load_CF(path=None):
    """the tensor of F, from the nested list `CFtab3` of Thomson/TriangleLocal/CFData.lean"""
    import os
    if path is None:
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'Thomson', 'TriLocalCert', 'CFData.lean')
    src = open(path).read()
    body = re.search(r'def CFtab3 : List \(List \(List Itv\)\) :=\n(.*?)\n\ndef CFt', src, re.S).group(1)
    pairs = [(int(a), int(b)) for a, b in re.findall(r'⟨(-?\d+), (-?\d+)⟩', body)]
    assert len(pairs) == 729
    return [[[pairs[81*i+9*j+k] for k in range(9)] for j in range(9)] for i in range(9)]
# ---- splitting rule (Skip.lean) ----
def splitAxis(b):
    wu, wv, wt = b[1]-b[0], b[3]-b[2], b[5]-b[4]
    if wv <= wu and wt <= wu: return 0
    return 1 if wt <= wv else 2
def facesIn(CUBE, b, ax):
    lo, hi = b[2*ax], b[2*ax+1]
    return sorted({f for m in range(5) for f in CUBE[m][ax] if lo < f < hi})
def splitPoint(CUBE, b, ax):
    fs = facesIn(CUBE, b, ax)
    return fs[0] if fs else (b[2*ax] + b[2*ax+1]) // 2
def lower(b, ax, m):
    o = list(b); o[2*ax+1] = m; return tuple(o)
def upper(b, ax, m):
    o = list(b); o[2*ax] = m; return tuple(o)
