"""[Tri5b] Exact Python mirror of the Lean fixed-point interval arithmetic
(`Thomson/TriangleGlobal/{Interval,TM,Tensor,Engine,Leaf,Cover}.lean`).  Every operation here reproduces
the Lean one bit for bit, so a certificate generated with this module is accepted by the Lean
checker without any tolerance."""
SCALE = 10 ** 40

def fdiv(a, b):            # Lean's `Int./` : floor division (b > 0)
    return a // b

def cdiv(a, b):
    return -((-a) // b)

# ---------- Itv ----------
def iadd(x, y): return (x[0] + y[0], x[1] + y[1])
def ineg(x):    return (-x[1], -x[0])
def isub(x, y): return iadd(x, ineg(y))
def imul(x, y):
    a, b, c, d = x[0]*y[0], x[0]*y[1], x[1]*y[0], x[1]*y[1]
    return (fdiv(min(a, b, c, d), SCALE), cdiv(max(a, b, c, d), SCALE))
def cst(n):     return (n, n)
IZERO = (0, 0)
IONE = (SCALE, SCALE)
def inpow(x, n):
    r = IONE
    for _ in range(n): r = imul(x, r)
    return r
def ihorner(cs, x):
    r = IZERO
    for c in reversed(cs): r = iadd(cst(c), imul(x, r))
    return r
def isum(l):
    r = IZERO
    for v in l: r = iadd(r, v)
    return r
def iofdiv(n, d):
    return (fdiv(n * SCALE, d), cdiv(n * SCALE, d))

# ---------- tensors: dict (i,j,k) -> Itv, with 0 <= i,j,k <= 8 ----------
N = 9
def tzero(): return {}
def tget(T, i, j, k): return T.get((i, j, k), IZERO)
def tadd(A, B):
    o = dict(A)
    for key, v in B.items(): o[key] = iadd(o.get(key, IZERO), v)
    return o
def tsub(A, B):
    o = dict(A)
    for key, v in B.items(): o[key] = isub(o.get(key, IZERO), v)
    return o
def tsmul(s, A):
    return {key: imul(s, v) for key, v in A.items()}

from math import comb
def sh_axis(T, ax, a):
    """Lean's Ish1/Ish2/Ish3: shift one axis by a/SCALE."""
    out = {}
    apow = [IONE]
    for _ in range(N): apow.append(imul(cst(a), apow[-1]))
    for key, v in T.items():
        i = key[ax]
        for j in range(i + 1):
            nk = list(key); nk[ax] = j
            nk = tuple(nk)
            term = imul(imul(v, cst(comb(i, j) * SCALE)), apow[i - j])
            out[nk] = iadd(out.get(nk, IZERO), term)
    return out
def tshift(T, a, b, d):
    return sh_axis(sh_axis(sh_axis(T, 0, a), 1, b), 2, d)

# ---------- TM extraction (Engine.toTM) ----------
def maxabs(I): return max(abs(I[0]), abs(I[1]))
def coefIT(T, h1, h2, h3, i, j, k):
    v = tget(T, i, j, k)
    v = imul(v, inpow(cst(h1), i))
    v = imul(v, inpow(cst(h2), j))
    v = imul(v, inpow(cst(h3), k))
    return v
def toTM(T, h1, h2, h3):
    lo = {}
    rad = 0
    for i in range(N):
        for j in range(N):
            for k in range(N):
                c = coefIT(T, h1, h2, h3, i, j, k)
                if i + j + k <= 2:
                    lo[(i, j, k)] = c[0]
                    rad += c[1] - c[0]
                else:
                    rad += maxabs(c)
    return lo, rad
def loAxis(g, q):
    if 2 * q <= abs(g): return q - abs(g)
    return -((g * g + 4 * q - 1) // (4 * q))
def loBound(lo, rad):
    g = lambda i, j, k: lo.get((i, j, k), 0)
    return (g(0,0,0) + loAxis(g(1,0,0), g(2,0,0)) + loAxis(g(0,1,0), g(0,2,0))
            + loAxis(g(0,0,1), g(0,0,2))
            - abs(g(1,1,0)) - abs(g(1,0,1)) - abs(g(0,1,1)) - rad)


# ---------- the certificate's tensors ----------
def qtensors(qcoef_lines):
    """QIT k as dict, from the generated coefficient list"""
    Q = [dict() for _ in range(6)]
    for l in qcoef_lines:
        k, i, j, c = l
        Q[k][(i, j, c[0])] = None
    return Q

def perm(T, f):
    return {f(key): v for key, v in T.items()}

def mup(T, ax, n):
    """multiply by x_ax^n (index shift)"""
    out = {}
    for key, v in T.items():
        nk = list(key); nk[ax] += n
        if nk[ax] > 8: raise Exception("degree overflow")
        out[tuple(nk)] = v
    return out

def termIT(QI, k, i, j):
    """uⁱvʲQ_k(u,v,t) + uⁱtʲQ_k(u,t,v) + vⁱtʲQ_k(v,t,u), as in Leaf/Bridge"""
    A = mup(mup(QI[k], 1, j), 0, i)
    B = mup(mup(perm(QI[k], lambda K: (K[0], K[2], K[1])), 2, j), 0, i)
    C = mup(mup(perm(QI[k], lambda K: (K[2], K[0], K[1])), 2, j), 1, i)
    return tadd(tadd(A, B), C)
