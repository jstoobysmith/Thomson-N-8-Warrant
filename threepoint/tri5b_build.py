"""[Tri5b] Build the certificate's interval data exactly as Lean does, and check it."""
import pickle, sys
import tri5b_mirror as M
S = M.SCALE
SC = '/private/tmp/claude-501/-Users-josephsmith-LocalGithub-ThompsonEight/bc112d7d-d8ba-4adc-8543-ce78e03179c9/scratchpad/'

# --- Q tensors (from the generated coefficient table) ---
QI = [dict() for _ in range(6)]
for line in open(SC + 'qcoef.txt'):
    lhs, rhs = line.strip().lstrip('| ').split('=>')
    k, i, j, l = [int(x) for x in lhs.split(',')]
    QI[k][(i, j, l)] = M.cst(int(rhs) * S)

# --- B and H tables ---
bent = pickle.load(open(SC + 'bent.pkl', 'rb'))
hdat = pickle.load(open(SC + 'hdata.pkl', 'rb'))
USTARI = (3140893678892018673812332619607600000000, 3140893678892018673812332619607900000000)
BC = {k: v[0] for k, v in bent.items()}
def BI(k, i, a):  return M.ihorner(BC.get((k, i, a), []), USTARI)
HQ = {}
for (k, a, b), (v, lit) in hdat['H'].items():
    HQ[(k, a, b)] = v
    if a != b: HQ[(k, b, a)] = v
PIVQ = [v for v, _ in hdat['piv']]
SLOT = [(0,0,2),(0,0,6),(0,0,7),(0,1,3),(0,2,4),(0,3,6),(0,5,7),(1,0,0),(1,0,1),(1,0,2),(1,2,3),
        (2,0,0),(2,0,1),(2,1,2),(2,3,5),(3,0,0),(3,0,1),(3,0,3),(3,1,2),(4,0,0),(4,0,1),(4,0,2),
        (5,0,0),(5,0,1)]
def HI(k, a, b):
    tot = M.cst(HQ.get((k, a, b), 0))
    for j in range(24):
        e = M.IONE if (SLOT[j] == (k, a, b) or SLOT[j] == (k, b, a)) else M.IZERO
        tot = M.iadd(tot, M.imul(e, M.cst(PIVQ[j])))
    return tot
def MIent(k, i, j):
    n = 9 - k
    tot = M.IZERO
    for a in range(n):
        inner = M.IZERO
        for b in range(n):
            inner = M.iadd(inner, M.imul(M.imul(BI(k, i, a), HI(k, a, b)), BI(k, j, b)))
        tot = M.iadd(tot, inner)
    return tot
def build_M():
    return {(k, i, j): MIent(k, i, j) for k in range(6) for i in range(9 - k) for j in range(9 - k)}
def build_F(MTab):
    tot = {}
    for k in range(6):
        n = 9 - k
        for i in range(n):
            for j in range(n):
                T = M.termIT(QI, k, i, j)
                c = MTab[(k, i, j)]
                for key, v in T.items():
                    tot[key] = M.iadd(tot.get(key, M.IZERO), M.imul(c, v))
    third = M.iofdiv(1, 3)
    return {key: M.imul(third, v) for key, v in tot.items()}
if __name__ == "__main__":
    MTab = build_M(); print("M entries:", len(MTab))
    F = build_F(MTab); print("F tensor entries:", len(F))
    w = max(v[1] - v[0] for v in F.values()); print("max interval width in F: %.3e" % (w / S))
    import tri5b_eval as tri, random
    random.seed(1)
    for _ in range(4):
        u, v, t = [random.uniform(-1, 0.5) for _ in range(3)]
        lo = sum(F[key][0] / S * u**key[0] * v**key[1] * t**key[2] for key in F)
        hi = sum(F[key][1] / S * u**key[0] * v**key[1] * t**key[2] for key in F)
        ref = tri.Fh(tri.HPIV, u, v, t)
        print("   F in [%.14f, %.14f]  ref %.14f  ok=%s" % (lo, hi, ref, lo - 1e-12 <= ref <= hi + 1e-12))
    pickle.dump({'M': MTab, 'F': F}, open(SC + 'tensors.pkl', 'wb'))
