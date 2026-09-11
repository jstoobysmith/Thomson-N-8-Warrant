"""[Task 5a] Exact Python mirror of `Thomson/TriLocalCert/*.lean`: the per-type data (enclosures of the
second and third ray derivatives on ten directions, their polarizations, the shifted majorant `M`)
and the quadtree patch coverings of the six faces of the cube `|delta_i| <= 1/500`.

Every operation reproduces the Lean one bit for bit (fixed point at 10^-40, `Int` floor division).
Usage (from the repository root):  python3 threepoint/trilocal_gen.py
"""
import os, sys, pickle
from math import comb

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "threepoint"))
from pair_gen import (S, add, neg, sub, mul, cst, ZERO, ONE, sumL, ofDiv, ladd, lsmul, lmul, lev,
                      lder, cdiv)

RHO = 2 * 10 ** 37
LAMQ = 97932235147 * 10 ** 27

# ---------- the tensor of F (Thomson.TriLocalCert.CFData: CFt) ----------
_cf = pickle.load(open(os.path.join(ROOT, "threepoint", "cfarr.pkl"), "rb"))
CF = [[[tuple(_cf[81 * i + 9 * j + k]) for k in range(9)] for j in range(9)] for i in range(9)]

# ---------- the touching types (Thomson.TriLocalCert.Touch: Tt) ----------
TA = (11712477381927344687859652885067900000000, 11712477381927344687859652885068300000000)
TD = (16563944362509771876618635911157400000000, 16563944362509771876618635911157800000000)
TN = (12876935261433174061741833895703400000000, 12876935261433174061741833895703900000000)
TF = (18968929475026778646313590239647800000000, 18968929475026778646313590239648200000000)
TT = [(TF, TF, TA), (TF, TD, TN), (TF, TN, TA), (TD, TA, TA), (TN, TN, TA)]


def aHi(I): return max(I[1], -I[0])


# ---------- Tri5b.Engine: Ish1 / Ishift ----------
def npow(I, n):
    r = ONE
    for _ in range(n):
        r = mul(I, r)
    return r

def ish_axis(C, ax, a):
    out = [[[ZERO] * 9 for _ in range(9)] for _ in range(9)]
    pw = [npow(cst(a), n) for n in range(9)]
    for x in range(9):
        for y in range(9):
            for z in range(9):
                idx = [x, y, z]
                j = idx[ax]
                terms = []
                for i in range(9):
                    if j <= i:
                        src = list(idx); src[ax] = i
                        v = C[src[0]][src[1]][src[2]]
                        terms.append(mul(mul(v, cst(comb(i, j) * S)), pw[i - j]))
                    else:
                        terms.append(ZERO)
                out[x][y][z] = sumL(terms)
    return out

def ishift(C, a, b, d):
    return ish_axis(ish_axis(ish_axis(C, 0, a), 1, b), 2, d)


# ---------- Enclose.lean: jets ----------
def gD(J, n): return J[n] if n < len(J) else ZERO
def jadd(J, K): return [add(gD(J, n), gD(K, n)) for n in range(4)]
def jmul(J, K): return [sumL([mul(gD(J, i), gD(K, n - i)) for i in range(n + 1)]) for n in range(4)]
def jsmul(c, J): return [mul(c, gD(J, n)) for n in range(4)]
def jpow(U, n):
    r = [ONE]
    for _ in range(n):
        r = jmul(U, r)
    return r

def JFL(C, U, V, W):
    pu = [jpow(U, i) for i in range(9)]; pv = [jpow(V, i) for i in range(9)]; pw = [jpow(W, i) for i in range(9)]
    acc = []
    for i in reversed(range(9)):
        accj = []
        for j in reversed(range(9)):
            acck = []
            for k in reversed(range(9)):
                acck = jadd(jsmul(C[i][j][k], pw[k]), acck)
            accj = jadd(jmul(pv[j], acck), accj)
        acc = jadd(jmul(pu[i], accj), acc)
    return acc

def JuL(A, D): return jadd([ONE], jsmul(ofDiv(-1, 2), jmul([A, D], [A, D])))

def JgL(C, lam, T0, T1, T2, D0, D1, D2):
    return jadd(jsmul(lam, jadd(jadd(jmul([T1, D1], [T2, D2]), jmul([T0, D0], [T2, D2])),
                                jmul([T0, D0], [T1, D1]))),
                jsmul(cst(-S), jmul(jmul(jmul([T0, D0], [T1, D1]), [T2, D2]),
                                    JFL(C, JuL(T0, D0), JuL(T1, D1), JuL(T2, D2)))))


# ---------- Polar.lean ----------
DIRZ = [(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0), (1, 0, 1), (0, 1, 1), (1, -1, 0), (1, 0, -1),
        (0, 1, -1), (1, 1, 1)]
HALF = ofDiv(1, 2); SIXTH = ofDiv(1, 6)

def HpolI(q):
    H = [[None] * 3 for _ in range(3)]
    H[0][0], H[1][1], H[2][2] = q[0], q[1], q[2]
    for (i, j, k) in [(0, 1, 3), (0, 2, 4), (1, 2, 5)]:
        v = mul(sub(sub(q[k], q[i]), q[j]), HALF)
        H[i][j] = v; H[j][i] = v
    return H

def pol6(sgn, x, y, z):
    return mul(sub(sub(x, y) if sgn else add(x, y), mul(cst(2 * S), z)), SIXTH)

def SvalsI(k):
    s = [k[0], k[1], k[2], pol6(True, k[3], k[6], k[1]), pol6(False, k[3], k[6], k[0]),
         pol6(True, k[4], k[7], k[2]), pol6(False, k[4], k[7], k[0]),
         pol6(True, k[5], k[8], k[2]), pol6(False, k[5], k[8], k[1])]
    inner = add(add(add(add(add(s[3], s[4]), s[5]), s[6]), s[7]), s[8])
    s.append(mul(sub(sub(k[9], add(add(k[0], k[1]), k[2])), mul(cst(3 * S), inner)), SIXTH))
    return s

def msIdx(a, b, c):
    L = [a, b, c]; n0 = L.count(0); n1 = L.count(1)
    if n0 == 3: return 0
    if n1 == 3: return 1
    table = {(0, 0): 2, (2, 1): 3, (1, 2): 4, (2, 0): 5, (1, 0): 6, (0, 2): 7, (0, 1): 8}
    return table.get((n0, n1), 9)


# ---------- Compute.lean ----------
def EuI(T, a): return sub(sub(ONE, mul(mul(T, T), HALF)), cst(a))

def lFL(C, U, V, W):
    def lpow(X, n):
        r = [ONE]
        for _ in range(n):
            r = lmul(X, r)
        return r
    pu = [lpow(U, i) for i in range(9)]; pv = [lpow(V, i) for i in range(9)]; pw = [lpow(W, i) for i in range(9)]
    acc = []
    for i in reversed(range(9)):
        accj = []
        for j in reversed(range(9)):
            acck = []
            for k in reversed(range(9)):
                acck = ladd(lsmul(C[i][j][k], pw[k]), acck)
            accj = ladd(lmul(pv[j], acck), accj)
        acc = ladd(lmul(pu[i], accj), acc)
    return acc

def IPgLs(CB, Lam, A0, A1, A2, E0, E1, E2):
    one = ONE
    return ladd(lsmul(Lam, ladd(ladd(lmul([A1, one], [A2, one]), lmul([A0, one], [A2, one])),
                                lmul([A0, one], [A1, one]))),
                lsmul(one, lmul(lmul(lmul([A0, one], [A1, one]), [A2, one]),
                                lFL(CB, [E0, A0, HALF], [E1, A1, HALF], [E2, A2, HALF]))))

def computeD(CSm, T0, T1, T2, a, b, c):
    q, k = [], []
    for d in DIRZ:
        J = JgL(CF, cst(LAMQ), T0, T1, T2, cst(d[0] * S), cst(d[1] * S), cst(d[2] * S))
        q.append(mul(cst(2 * S), gD(J, 2)))
        k.append(mul(cst(6 * S), gD(J, 3)))
    H = HpolI(q)
    Sv = SvalsI(k)
    C = [[[Sv[msIdx(x, y, z)] for z in range(3)] for y in range(3)] for x in range(3)]
    CB = [[[cst(aHi(CSm[i][j][kk])) for kk in range(9)] for j in range(9)] for i in range(9)]
    P = IPgLs(CB, cst(LAMQ), cst(aHi(T0)), cst(aHi(T1)), cst(aHi(T2)),
              cst(aHi(EuI(T0, a))), cst(aHi(EuI(T1, b))), cst(aHi(EuI(T2, c))))
    M = lev(lder(lder(lder(lder(P)))), cst(RHO))
    return H, C, M


# ---------- Patch.lean ----------
def boxG(D, e0, r):
    H, C, M = D
    E = [(e0[a] - r[a], e0[a] + r[a]) for a in range(3)]
    d = [(-r[a], r[a]) for a in range(3)]
    Q = ZERO
    for a in range(3):
        for b in range(3):
            t = add(add(mul(H[a][b], mul(cst(e0[a]), cst(e0[b]))),
                        mul(H[a][b], add(mul(cst(e0[a]), d[b]), mul(d[a], cst(e0[b]))))),
                    mul(H[a][b], mul(d[a], d[b])))
            Q = add(Q, t)
    K = ZERO
    for a in range(3):
        for b in range(3):
            for c in range(3):
                K = add(K, mul(C[a][b][c], mul(mul(E[a], E[b]), E[c])))
    n2 = add(add(mul(E[0], E[0]), mul(E[1], E[1])), mul(E[2], E[2]))
    return sub(sub(mul(Q, HALF), mul(cst(aHi(K)), SIXTH)), mul(mul(M, mul(n2, n2)), ofDiv(1, 24)))

def fst(f): return 1 if f == 0 else 0

def faceVec(f, s, x, y):
    return [s if a == f else (x if a == fst(f) else y) for a in range(3)]

def qt(D, f, s, x0, y0, h, bits, depth):
    if boxG(D, faceVec(f, s, x0, y0), faceVec(f, 0, h, h))[0] >= 0:
        bits.append(False)
        return depth + 1
    assert h % 2 == 0 and depth < 40
    bits.append(True)
    k = h // 2
    dmax = 0
    for (dx, dy) in [(-1, -1), (-1, 1), (1, -1), (1, 1)]:
        dmax = max(dmax, qt(D, f, s, x0 + dx * k, y0 + dy * k, k, bits, depth + 1))
    return dmax


# ---------- emitting Lean ----------
HDR = "-- GENERATED by threepoint/trilocal_gen.py; do not edit\n"
def itv(I): return "⟨%d, %d⟩" % I
def l1(L): return "[" + ", ".join(itv(I) for I in L) + "]"
def l2(L): return "[" + ",\n    ".join(l1(r) for r in L) + "]"
def l3(L): return "[" + ",\n   ".join(l2(r) for r in L) + "]"

TYPE = HDR + """import Thomson.TriLocalCert.Compute
import Thomson.TriLocalCert.Touch
import Thomson.TriLocalCert.CFData

/-! # Task 5a: the data of touching type `{m}` — GENERATED

The tensor of `F` shifted to the grid point `({a}, {b}, {c}) · 10⁻⁴⁰` next to `(u₀, v₀, t₀)`, and the
interval data (`H`, `C` from ten ray jets, `M` from the shifted majorant), each checked against its
definition by `decide +kernel`.  `M ≈ {M:.1f}`. -/

namespace Thomson.TriLocalCert

open Thomson.Tri5b

def sa{m} : ℤ := {a}
def sb{m} : ℤ := {b}
def sc{m} : ℤ := {c}

set_option maxHeartbeats 4000000 in
def CS{m}tab : List (List (List Itv)) :=
  {CS}

def CS{m} : IT := fun i j k => ((CS{m}tab.getD i []).getD j []).getD k Itv.zero

set_option maxRecDepth 100000 in
theorem CS{m}_eq : ∀ i j k, CS{m} i j k = Ishift CFt sa{m} sb{m} sc{m} i j k := by decide +kernel

set_option maxHeartbeats 4000000 in
def D{m} : Data where
  H := {H}
  C := {C}
  M := {MI}

set_option maxRecDepth 100000 in
theorem D{m}_eq : D{m} = computeD CFt CS{m} (Tt {m}).1 (Tt {m}).2.1 (Tt {m}).2.2 sa{m} sb{m} sc{m} := by
  decide +kernel

end Thomson.TriLocalCert
"""

FACE = HDR + """import Thomson.TriLocalCert.Type{m}

/-! # Task 5a: type `{m}`, face `e_{f} = {sgn}ρ` — GENERATED ({n} patches) -/

namespace Thomson.TriLocalCert

set_option maxHeartbeats 4000000 in
def bits{m}_{f}{s} : List Bool := [{bits}]

set_option maxRecDepth 1000000 in
theorem face{m}_{f}{s} : faceOK D{m} {f} {bool} {depth} bits{m}_{f}{s} = true := by decide +kernel

end Thomson.TriLocalCert
"""

GLUE = HDR + """{imports}
import Thomson.TriLocalCert.Final
import Thomson.ThreePoint.Cert.TriLocalFinal
import Thomson.ThreePoint.Cert.TriLocalPolarBridge

/-! # Task 5a, assembled — GENERATED

The five checked touching types (`type_certificate`), through Task 5a's calculus
(`Thomson.ThreePoint.Cert.triP_local_of_bracket_all`): for any pivots within `10⁻¹²` of
`pivotsNum` at which `triP` has its second-order zeros (`triP_tight`), `triP ≥ 0` on the five cubes
of radius `1/500`.  `decide +kernel` only. -/

namespace Thomson.TriLocalCert

open Thomson Thomson.Tri5b Set

{types}

/-- The `M` of each type. -/
noncomputable def Mt : Fin 5 → ℝ
{mdefs}

/-- **Task 5a.** -/
theorem triP_local_cert {{p : Fin 24 → ℝ}} (hclose : ∀ j, |p j - pivotsNum j| ≤ 1 / 10 ^ 12)
    (hval : ∀ m : Fin 5, triP p (touchType m).1 (touchType m).2.1 (touchType m).2.2 = 0)
    (hder : ∀ m : Fin 5, ∀ c : Fin 3, deriv (triD p m c) 0 = 0) :
    ∀ m : Fin 5, ∀ a b c : ℝ, |a - (touchType m).1| ≤ 1 / 500 →
      |b - (touchType m).2.1| ≤ 1 / 500 → |c - (touchType m).2.2| ≤ 1 / 500 →
      0 ≤ triP p a b c := by
  have cert : ∀ m : Fin 5,
      (∀ δ : Fin 3 → ℝ, (∀ i, |δ i| ≤ 1 / 500) →
        0 ≤ bracket (Hpol (Q2 p (touchType m))) (Cpol (K3 p (touchType m))) (Mt m) δ) ∧
      (∀ δ : Fin 3 → ℝ, (∀ i, |δ i| ≤ 1 / 500) → ∀ x ∈ Icc (0 : ℝ) 1,
        |deriv (deriv (deriv (deriv (rayR p (touchType m) δ)))) x| ≤ Mt m * N2 δ ^ 2) := by
    intro m
    fin_cases m
{cases}
  refine ThreePoint.Cert.triP_local_of_bracket_all p Mt hval hder (fun m δ hδ => ?_)
    (fun m δ hδ x hx => ?_)
  · have h := (cert m).1 δ hδ
    have e := ThreePoint.Cert.bracket_H_eq_pol p (touchType m) (Mt m) δ
    change 0 ≤ bracket (ThreePoint.Cert.H p (touchType m)) (ThreePoint.Cert.C p (touchType m))
      (Mt m) δ
    rw [e]
    exact h
  · exact (cert m).2 δ hδ x hx

end Thomson.TriLocalCert
"""

CFDATA = HDR + """import Thomson.Tri5b.CertIntervals

/-! # Task 5a: the tensor of `F`, tabulated — GENERATED

Task 5b's interval tensor of `F` for the true certificate (`Thomson.Tri5b.CFedata`: the pivot slots
widened by `10⁻¹²`), as a literal table, checked against its definition by `decide +kernel` (not the
`native_decide` of `Thomson.Tri5b.CFTable`). -/

namespace Thomson.TriLocalCert

open Thomson Thomson.Tri5b

set_option maxHeartbeats 4000000 in
def CFtab3 : List (List (List Itv)) :=
  {tab}

def CFt : IT := fun i j k => ((CFtab3.getD i []).getD j []).getD k Itv.zero

set_option maxRecDepth 100000 in
theorem CFt_eq : ∀ i j k, CFt i j k = CFedata i j k := by decide +kernel

theorem ITMem_CFt {{p : Fin 24 → ℝ}} (hclose : ∀ j, |p j - pivotsNum j| ≤ 1 / 10 ^ 12) :
    ITMem CFt (cF (Mmat (Hp p))) := by
  have hc : ∀ j, |p j - pivotsNum j| ≤ (EPS : ℝ) / SCALE := by
    intro j; rw [show (EPS : ℝ) / SCALE = 1 / 10 ^ 12 by norm_num [EPS, SCALE]]; exact hclose j
  intro i j k
  rw [CFt_eq]
  exact ITMem_CFedata hc i j k

end Thomson.TriLocalCert
"""

def emit(outdir):
    open(os.path.join(outdir, "CFData.lean"), "w").write(CFDATA.format(tab=l3(CF)))
    tot = 0
    glue_types, glue_m, glue_cases, imports = [], [], [], []
    for m, (T0, T1, T2) in enumerate(TT):
        mid = lambda T: (T[0] + T[1]) // 2
        a, b, c = [S - (mid(T) * mid(T)) // (2 * S) for T in (T0, T1, T2)]
        CSm = ishift(CF, a, b, c)
        H, C, M = computeD(CSm, T0, T1, T2, a, b, c)
        open(os.path.join(outdir, "Type%d.lean" % m), "w").write(TYPE.format(
            m=m, a=a, b=b, c=c, M=M[1] / S, CS=l3(CSm), H=l2(H), C=l3(C), MI=itv(M)))
        depths = {}
        for f in range(3):
            for sg in (True, False):
                bits = []
                depth = qt((H, C, M), f, RHO if sg else -RHO, 0, 0, RHO, bits, 0)
                depths[(f, sg)] = depth + 1
                imports.append("import Thomson.TriLocalCert.Face%d_%d%s" % (m, f, "p" if sg else "n"))
                n = bits.count(False)
                tot += n
                open(os.path.join(outdir, "Face%d_%d%s.lean" % (m, f, "p" if sg else "n")), "w").write(
                    FACE.format(m=m, f=f, s="p" if sg else "n", sgn="+" if sg else "−", n=n,
                                bits=", ".join("true" if x else "false" for x in bits),
                                bool="true" if sg else "false", depth=depth + 1))
        dm = "\n".join("  | %d, %s => %d" % (f, "true" if sg else "false", depths[(f, sg)])
                       for f in range(3) for sg in (True, False))
        bm = "\n".join("  | %d, %s => bits%d_%d%s" % (f, "true" if sg else "false", m, f, "p" if sg else "n")
                       for f in range(3) for sg in (True, False))
        faces = " | ".join("exact face%d_%d%s" % (m, f, s2) for f in range(3) for s2 in ("p", "n"))
        glue_types.append(f"""def depth{m} : Fin 3 → Bool → ℕ
{dm}

def bitsOf{m} : Fin 3 → Bool → List Bool
{bm}

theorem typeCert{m} {{p : Fin 24 → ℝ}} (hclose : ∀ j, |p j - pivotsNum j| ≤ 1 / 10 ^ 12) :=
  type_certificate hclose {m} CS{m}_eq D{m}_eq (by decide) depth{m} bitsOf{m}
    (fun f σ => by fin_cases f <;> cases σ <;> first | {faces})
""")
        glue_m.append("  | %d => Mreal CS%d (Tt %d).1 (Tt %d).2.1 (Tt %d).2.2 sa%d sb%d sc%d" % (m, m, m, m, m, m, m, m))
        glue_cases.append("    · exact typeCert%d hclose" % m)
        print("type", m, "M", M[1] / S)
    open(os.path.join(outdir, "Glue.lean"), "w").write(GLUE.format(
        imports="\n".join(imports), types="\n".join(glue_types), mdefs="\n".join(glue_m),
        cases="\n".join(glue_cases)))
    print("total patches", tot)


if __name__ == "__main__":
    emit(os.path.join(ROOT, "Thomson", "TriLocalCert"))
