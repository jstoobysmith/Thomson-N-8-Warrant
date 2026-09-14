"""[Tri5b] Exact fixed-point data for the five local cubes (the `CubeData` of Skip.lean)."""
from mpmath import mp, mpf, sqrt, floor, ceil
from fractions import Fraction as Fr
mp.dps = 80
SCALE = 10 ** 40
RHO = Fr(1, 500)
ULO = Fr(7852234197230046684530831549019, 25000000000000000000000000000000)
UHI = Fr(31408936788920186738123326196079, 100000000000000000000000000000000)
S2LO = Fr(90509667991878083123308078349420677028459, 64000000000000000000000000000000000000000)
S2HI = Fr(353553390593273762200422181052424519642417969, 250000000000000000000000000000000000000000000)

def sqrt_bounds(qlo, qhi, D=10 ** 32):
    lo = Fr(int(floor(sqrt(mpf(qlo.numerator) / qlo.denominator) * D)), D)
    hi = Fr(int(ceil(sqrt(mpf(qhi.numerator) / qhi.denominator) * D)), D)
    assert lo ** 2 <= qlo and hi ** 2 >= qhi
    return lo, hi

SQ = {'A': (2 * (1 - UHI), 2 * (1 - ULO)),
      'D': (4 * (1 - UHI), 4 * (1 - ULO)),
      'N': (2 + 2 * ULO - S2HI * (1 - ULO), 2 + 2 * UHI - S2LO * (1 - UHI)),
      'F': (2 + 2 * ULO + S2LO * (1 - UHI), 2 + 2 * UHI + S2HI * (1 - ULO))}
CH = {k: sqrt_bounds(*v) for k, v in SQ.items()}

# touching types, in the order of `touchType` (chords, decreasing)
TYPES = [('F', 'F', 'A'), ('F', 'D', 'N'), ('F', 'N', 'A'), ('D', 'A', 'A'), ('N', 'N', 'A')]

def cube_lo(ch):
    """ceil(SCALE * (1 - (tlo+rho)^2/2)) — inside the true image, from below"""
    tlo, _ = CH[ch]
    v = (1 - (tlo + RHO) ** 2 / 2) * SCALE
    return -((-v.numerator) // v.denominator)          # ceiling
def cube_hi(ch):
    """floor(SCALE * (1 - (thi-rho)^2/2))"""
    _, thi = CH[ch]
    v = (1 - (thi - RHO) ** 2 / 2) * SCALE
    return v.numerator // v.denominator                # floor

CUBE = [[(cube_lo(c), cube_hi(c)) for c in tp] for tp in TYPES]

if __name__ == "__main__":
    for k, (lo, hi) in CH.items():
        print("chord %s ∈ [%s, %s]  (%.16f)" % (k, lo, hi, float(lo)))
    for m, tp in enumerate(TYPES):
        print("cube %d (%s):" % (m, "".join(tp)),
              [(lo / SCALE, hi / SCALE) for lo, hi in [(float(a), float(b)) for a, b in CUBE[m]]])
