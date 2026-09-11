"""[Task 4] Exact Python mirror of `Thomson/Pair/*.lean`: the interval coefficients of
`Phi(w) = alpha^2 - (2 - 2w) R(w)^2` (with `pairP pivots s = alpha - s R(1 - s^2/2)`) and the eight
chord sweeps that certify `Phi >= 0` on `[-1, 337/625]`.

Every operation reproduces the Lean one bit for bit (fixed point, scale 10^40, `Int` floor
division), so the data emitted here is accepted by the Lean checker without tolerance.

Usage (from the repository root):  python3 threepoint/pair_gen.py
"""
import re, os, sys
from fractions import Fraction as Fr

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "threepoint"))
import tri5b_leandata as L

S = 10 ** 40
EPS = 10 ** 28          # Thomson.Tri5b.EPS: the pivot enclosure 10^-12


def cdiv(a, b):
    return -((-a) // b)


# ---------- Itv (Thomson/Tri5b/Interval.lean) ----------
def add(x, y): return (x[0] + y[0], x[1] + y[1])
def neg(x): return (-x[1], -x[0])
def sub(x, y): return add(x, neg(y))
def mul(x, y):
    a, b, c, d = x[0] * y[0], x[0] * y[1], x[1] * y[0], x[1] * y[1]
    return (min(min(a, b), min(c, d)) // S, cdiv(max(max(a, b), max(c, d)), S))
def cst(n): return (n, n)
ZERO = (0, 0)
ONE = (S, S)
def horner(cs, x):          # Itv.horner: integer coefficients
    r = ZERO
    for c in reversed(cs):
        r = add(cst(c), mul(x, r))
    return r
def sumL(l):                # Itv.sumL = foldr add zero
    r = ZERO
    for v in reversed(l):
        r = add(v, r)
    return r
def ofDiv(n, d): return ((n * S) // d, -((-(n * S)) // d))


# ---------- coefficient lists (Thomson/Pair/Poly.lean) ----------
def ladd(p, q):
    if not p: return list(q)
    if not q: return list(p)
    return [add(p[0], q[0])] + ladd(p[1:], q[1:])
def lsmul(c, p): return [mul(c, a) for a in p]
def lmul(p, q):
    if not p: return []
    return ladd(lsmul(p[0], q), [ZERO] + lmul(p[1:], q))
def lev(p, x):              # Horner with interval coefficients
    r = ZERO
    for c in reversed(p):
        r = add(c, mul(x, r))
    return r
def nsmul(n, a): return (n * a[0], n * a[1])
def lder(p):
    return [nsmul(i + 1, c) for i, c in enumerate(p[1:])]
def lalt(p): return [c if i % 2 == 0 else neg(c) for i, c in enumerate(p)]
def laddAt(n, c, l):
    if n == 0:
        return [c] if not l else [add(l[0], c)] + l[1:]
    return ([ZERO] if not l else [l[0]]) + laddAt(n - 1, c, l[1:])


# ---------- the certificate's data ----------
SRC = open(os.path.join(ROOT, "Thomson/Tri5b/CertIntervals.lean")).read()

def parse_BC():
    body = SRC[SRC.index("def BC"):SRC.index("def BI")]
    out = {}
    for m in re.finditer(r"\|\s*(\d+),\s*(\d+),\s*(\d+)\s*=>\s*\[(.*?)\]", body):
        k, i, a = int(m.group(1)), int(m.group(2)), int(m.group(3))
        nums = [int(x) for x in re.findall(r"-?\d+", m.group(4).replace(": ℤ", ""))]
        out[(k, i, a)] = nums
    return out

BC = parse_BC()
UI = (3140893678892018673812332619607600000000, 3140893678892018673812332619607900000000)

def BI(k, i, a): return horner(BC.get((k, i, a), []), UI)

HFIX = L.Hfix_entries(Fr)
PIV = L.pivotsNum(Fr)
SLOT = L.SLOT

def HIe(k, a, b):
    hq = HFIX[k][a][b] * S
    assert hq.denominator == 1
    hi = int(hq)
    cnt = 0
    for j, sl in enumerate(SLOT):
        if sl == (k, a, b) or sl == (k, b, a):
            q = PIV[j] * S
            assert q.denominator == 1
            hi += int(q)
            cnt += 1
    return (hi - cnt * EPS, hi + cnt * EPS)

a0, a1, lam = L.a_consts(Fr)
ALPHA = 1 - 18 * lam


def fx(q):
    v = q * S
    assert v.denominator == 1, q
    return int(v)


def build():
    n = lambda k: 9 - k
    Bt = [[[BI(k, i, a) for a in range(n(k))] for i in range(n(k))] for k in range(6)]
    Ht = [[[HIe(k, a, b) for b in range(n(k))] for a in range(n(k))] for k in range(6)]
    # Thomson.Tri5b.MI: M_k[i][j] = sum_a sum_b (B[i][a] H[a][b]) B[j][b]
    Mt = [[[sumL([sumL([mul(mul(Bt[k][i][a], Ht[k][a][b]), Bt[k][j][b]) for b in range(n(k))])
                  for a in range(n(k))])
            for j in range(n(k))] for i in range(n(k))] for k in range(6)]
    return Bt, Ht, Mt


def dlist(Mt):
    """`Dcomp`: the coefficients of F(1, w, w)."""
    om = [ONE, ZERO, cst(-S)]
    tot = []
    for k in range(6):
        mu = []
        for i in reversed(range(9 - k)):          # foldr over finRange: last element first
            for j in reversed(range(9 - k)):
                mu = laddAt(i + j, Mt[k][i][j], mu)
        w = [ONE]
        for _ in range(k):
            w = lmul(om, w)
        tot = ladd(lmul(mu, w), tot)             # foldr over k
    rho = []
    for i in reversed(range(9)):
        for j in reversed(range(9)):
            rho = laddAt(i, Mt[0][i][j], laddAt(j, Mt[0][i][j], rho))
    return lsmul(ofDiv(1, 3), ladd(tot, rho))


def rlist(D):
    return ladd([cst(fx(a0)), cst(fx(a1))], lsmul(cst(3 * S), D))


def philist(R):
    return ladd([cst(fx(ALPHA * ALPHA))], lsmul(cst(-S), lmul([cst(2 * S), cst(-2 * S)], lmul(R, R))))


# ---------- the sweep checker (Thomson/Pair/Sweep.lean) ----------
def absHi(I): return max(I[1], -I[0])

def cellLo(F2, F3, F4, c, h, hh):
    v2 = lev(F2, cst(c))
    a3 = absHi(lev(F3, cst(c)))
    k4 = absHi(lev(F4, (c - h, c + h)))
    return v2[0] - mul(cst(a3), cst(h))[1] - mul(cst(k4), cst(hh))[1]

def run(F2, F3, F4, g, p, d, cells):
    for (g2, c, h, hh) in cells:
        l = cellLo(F2, F3, F4, c, h, hh)
        t = g2 - g
        lt = (l * t) // S
        p2 = p + (d * t) // S + ((lt * t) // S) // 2
        d2 = d + lt
        ok = (c - h <= g and g2 <= c + h and g < g2 and 0 <= h and h * h <= 2 * S * hh
              and 0 <= p and (0 <= d or l <= 0) and 0 <= p2)
        if not ok:
            return None, (g, p, d, l)
        g, p, d = g2, p2, d2
    return g, (g, p, d)

def sweep_ok(F2, F3, F4, xl, xh, cells, gend):
    g1, c, h, hh = cells[0]
    l = cellLo(F2, F3, F4, c, h, hh)
    t = g1 - xh
    ok = c - h <= xl and g1 <= c + h and xh <= g1 and 0 <= h and h * h <= 2 * S * hh and 0 <= l
    if not ok:
        return False, ("start", l)
    lt = (l * t) // S
    p1 = ((lt * t) // S) // 2
    d1 = lt
    g, info = run(F2, F3, F4, g1, p1, d1, cells[1:])
    return g == gend, info


def mkcell(g, g2):
    """cell [c - h, c + h] containing [g, g2]; c, h integers, hh >= h^2/(2S)"""
    s = g + g2
    c = s // 2
    h = max(g2 - c, c - g)
    hh = cdiv(h * h, 2 * S)
    return (g2, c, h, hh)


def design(F2, F3, F4, xl, xh, gend, tol, hmax):
    """Greedy grid from the chord to `gend`: step as long as the cell loss stays below `tol`."""
    cells = []
    g = xh
    first = True
    while g < gend:
        t = hmax
        while True:
            g2 = min(gend, g + t) if not first else min(gend, xh + t)
            lo = xl if first else g
            cell = mkcell(lo, g2)
            _, c, h, hh = cell
            v2 = lev(F2, cst(c))[0]
            l = cellLo(F2, F3, F4, c, h, hh)
            if v2 - l <= tol or t < 10 ** 26:
                break
            t = t // 2
        # round g2 to a multiple of 10^20 for readability
        cells.append(cell)
        g = cell[0]
        first = False
    return cells


def chord_w():
    """w-values of the chords as intervals (32 digits: uStar_lo/hi, sqrt2_bounds_45)."""
    ul, uh = Fr(7852234197230046684530831549019, 25 * 10 ** 30), Fr(31408936788920186738123326196079, 10 ** 32)
    sl = Fr(90509667991878083123308078349420677028459, 64 * 10 ** 39)
    sh = Fr(353553390593273762200422181052424519642417969, 25 * 10 ** 43)
    A = (ul, uh)
    D = (2 * ul - 1, 2 * uh - 1)
    # N = -u + sqrt2 (1-u)/2 : decreasing in u, increasing in sqrt2
    N = (-uh + sl * (1 - uh) / 2, -ul + sh * (1 - ul) / 2)
    F = (-uh - sh * (1 - ul) / 2, -ul - sl * (1 - uh) / 2)
    def fl(q): return (q.numerator * S) // q.denominator
    def ce(q): return -((-q.numerator * S) // q.denominator)
    return {X: (fl(v[0]), ce(v[1])) for X, v in zip("ADNF", [A, D, N, F])}


def design2(F2, F3, F4, xl, xh, gend, tol, rel, hmax):
    """Greedy grid from the chord to `gend`: halve the step until the loss `f''(c) - cellLo` of
    the cell is below `max(tol, rel |f''(c)|)`."""
    cells = []
    g = xh
    first = True
    while g < gend:
        t = hmax
        while True:
            g2 = min(gend, g + t)
            cell = mkcell(xl if first else g, g2)
            _, c, h, hh = cell
            v2 = lev(F2, cst(c))[0]
            l = cellLo(F2, F3, F4, c, h, hh)
            if v2 - l <= max(tol, int(rel * abs(v2))) or t < 10 ** 26:
                break
            t //= 2
        cells.append(cell)
        g = cell[0]
        first = False
    return cells


# ---------- emitting Lean ----------
HDR = "-- GENERATED by threepoint/pair_gen.py; do not edit\n"

def itv(I): return "⟨%d, %d⟩" % I
def ilist(L): return "[" + ",\n    ".join(itv(I) for I in L) + "]"

M1, M2, M3 = -6024 * 10 ** 36, -235 * 10 ** 36, 2508 * 10 ** 36   # meeting points -0.6024, -0.0235, 0.2508
WMIN, WMAX = -S, 5392 * 10 ** 36                                     # w = 1 - s^2/2 at s = 2, 24/25
PLAN = [  # name, chord, side, end (in w)
    ("Fl", "F", -1, WMIN), ("Fr", "F", 1, M1), ("Dl", "D", -1, M1), ("Dr", "D", 1, M2),
    ("Nl", "N", -1, M2), ("Nr", "N", 1, M3), ("Al", "A", -1, M3), ("Ar", "A", 1, WMAX)]

TABLES = HDR + """import Thomson.Pair.Coeff

/-! # Task 4, step 5: the tables — GENERATED

The coefficients of `F(1, w, w)` for the true certificate (the pivot slots widened by `10⁻¹²`,
`Thomson.Tri5b.MIedata`), and the coefficient lists of `Φ''`, `Φ'''`, `Φ''''` and of the same
for `Φ(−w)`, which the sweeps read.  Each table is checked against its definition by
`decide +kernel`. -/

namespace Thomson.Pair

open Thomson.Tri5b

/-- The coefficients of `F(1, w, w)`, enclosed. -/
def IDtab : List Itv :=
  {D}

set_option maxRecDepth 100000 in
theorem IDtab_eq : IDtab = ID MIedata := by decide +kernel

def F2tab : List Itv :=
  {F2}

def F3tab : List Itv :=
  {F3}

def F4tab : List Itv :=
  {F4}

def G2tab : List Itv :=
  {G2}

def G3tab : List Itv :=
  {G3}

def G4tab : List Itv :=
  {G4}

set_option maxRecDepth 100000 in
theorem tabs_eq : F2tab = lder (lder (IPhi (IR IDtab))) ∧ F3tab = lder F2tab ∧
    F4tab = lder F3tab ∧ G2tab = lder (lder (lalt (IPhi (IR IDtab)))) ∧ G3tab = lder G2tab ∧
    G4tab = lder G3tab := by
  decide +kernel

end Thomson.Pair
"""

SWEEP = HDR + """import Thomson.Pair.Tables
import Thomson.Pair.Sweep

/-! # Task 4: the sweep `{name}` — GENERATED

From the chord `{X}` {dir}: {n} cells. -/

namespace Thomson.Pair

set_option maxHeartbeats 4000000 in
def cells{name} : List (ℤ × ℤ × ℤ × ℤ) := [
    {cells}]

set_option maxRecDepth 1000000 in
theorem sweep{name} :
    sweepOK {T}2tab {T}3tab {T}4tab ({a}) ({b}) ({e}) cells{name} = true := by
  decide +kernel

end Thomson.Pair
"""


def emit(outdir, tol=10 ** 37, rel=0.05, hmax=2 * 10 ** 38):
    Bt, Ht, Mt = build()
    D = dlist(Mt)
    Phi = philist(rlist(D))
    F2 = lder(lder(Phi)); F3 = lder(F2); F4 = lder(F3)
    G2 = lder(lder(lalt(Phi))); G3 = lder(G2); G4 = lder(G3)
    W = chord_w()
    open(os.path.join(outdir, "Tables.lean"), "w").write(TABLES.format(
        D=ilist(D), F2=ilist(F2), F3=ilist(F3), F4=ilist(F4), G2=ilist(G2), G3=ilist(G3),
        G4=ilist(G4)))
    summary = []
    for name, X, side, end in PLAN:
        xl, xh = W[X]
        if side > 0:
            T2, T3, T4, a, b, e, T = F2, F3, F4, xl, xh, end, "F"
        else:
            T2, T3, T4, a, b, e, T = G2, G3, G4, -xh, -xl, -end, "G"
        cells = design2(T2, T3, T4, a, b, e, tol, rel, hmax)
        ok, info = sweep_ok(T2, T3, T4, a, b, cells, e)
        assert ok, (name, info)
        summary.append((name, len(cells)))
        dirn = "to the right" if side > 0 else "to the left (as `Φ(−w)` to the right)"
        open(os.path.join(outdir, "Sweep%s.lean" % name), "w").write(SWEEP.format(
            name=name, X=X, dir=dirn, n=len(cells), T=T, a=a, b=b, e=e,
            cells=",\n    ".join("(%d, %d, %d, %d)" % c for c in cells)))
    return summary, W


if __name__ == "__main__":
    summary, W = emit(os.path.join(ROOT, "Thomson", "Pair"))
    print(summary, "total", sum(n for _, n in summary))
    for X, (a, b) in W.items():
        print(X, a, b)
