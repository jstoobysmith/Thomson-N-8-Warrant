# Uniqueness (UniquenessPlan.md, step U5): enumerate the edge colourings of K8 by the four
# antiprism chords A, D, N, F in which every triangle has colour multiset among the five antiprism
# types FFA, FDN, FNA, DAA, NNA.  Depth-first over the edges (i, j), i < j, ordered by j then i, so
# that every triangle is checked as soon as its last edge is placed.
#
#   python3 plans/unique_enum.py          full search:      224 922 nodes, 5040 leaves
#   python3 plans/unique_enum.py sorted   vertex-0 sorted:    1 878 nodes,    8 leaves
#
# Every leaf is either a relabelling of the antiprism pattern (`canon` finds the relabelling) or
# contains an "aligned" quadruple i j k l with ij = kl = A and ik = il = jk = jl = N — the pattern
# the 4×4 Gram determinant (1 − tA)²((1 + tA)² − 4 tN²) ≠ 0 rules out in ℝ³ (step U6).
import itertools, sys
A, D, N, F = 0, 1, 2, 3
allowed = {tuple(sorted(t)) for t in [(F,F,A), (F,D,N), (F,N,A), (D,A,A), (N,N,A)]}
sortedV0 = len(sys.argv) > 1 and sys.argv[1] == 'sorted'
edges = [(i, j) for j in range(8) for i in range(j)]
col = {}; nodes = 0; leaves = []

def ok_new(i, j):
    if sortedV0 and i == 0 and j >= 2 and col[(0, j)] < col[(0, j - 1)]:
        return False
    for l in range(i):  # (l, i) and (l, j) are already placed
        if tuple(sorted((col[(i, j)], col[(l, i)], col[(l, j)]))) not in allowed:
            return False
    return True

def dfs(k):
    global nodes
    nodes += 1
    if k == len(edges):
        leaves.append(dict(col)); return
    i, j = edges[k]
    for c in range(4):
        col[(i, j)] = c
        if ok_new(i, j):
            dfs(k + 1)
        del col[(i, j)]

def ap(i, j):
    """The antiprism pattern: top square 0..3 and bottom square 4..7, both cyclic; the near
    cross neighbours of v_i are w_i and w_{i+1}."""
    if i > j: i, j = j, i
    if j < 4 or i >= 4:
        return A if (j - i) % 4 in (1, 3) else D
    return N if ((j - 4) - i) % 4 in (0, 1) else F

def canon(c):
    """The relabelling sigma with c(sigma a, sigma b) = ap(a, b), built from vertex 0's
    neighbourhood; None if the colouring is not a relabelled antiprism."""
    cc = lambda i, j: c[(min(i, j), max(i, j))]
    An = [k for k in range(1, 8) if cc(0, k) == A]; Dn = [k for k in range(1, 8) if cc(0, k) == D]
    if len(An) != 2 or len(Dn) != 1: return None
    v1, (v2, v4), v3 = 0, An, Dn[0]
    w2 = [k for k in range(8) if k not in (v1, v2, v3, v4) and cc(v1, k) == N and cc(v2, k) == N]
    if len(w2) != 1: return None
    w2 = w2[0]
    w1 = [k for k in range(8) if k not in (v1, v2, v3, v4, w2) and cc(v1, k) == N]
    if len(w1) != 1: return None
    w1 = w1[0]
    rest = [k for k in range(8) if k not in (v1, v2, v3, v4, w1, w2)]
    w3 = [k for k in rest if cc(w1, k) == D]; w4 = [k for k in rest if cc(w2, k) == D]
    if len(w3) != 1 or len(w4) != 1: return None
    sigma = [v1, v2, v3, v4, w1, w2, w3[0], w4[0]]
    ok = all(cc(sigma[a], sigma[b]) == ap(a, b) for a in range(8) for b in range(a + 1, 8))
    return sigma if ok else None

def aligned(c):
    cc = lambda i, j: c[(min(i, j), max(i, j))]
    return any(cc(i, j) == A and cc(k, l) == A and cc(i, k) == N and cc(i, l) == N
               and cc(j, k) == N and cc(j, l) == N
               for i, j, k, l in itertools.permutations(range(8), 4))

dfs(0)
n_ap = sum(1 for c in leaves if canon(c) is not None)
n_al = sum(1 for c in leaves if canon(c) is None and aligned(c))
n_bad = len(leaves) - n_ap - n_al
degs = {tuple(sum(1 for k in range(8) if k != v and c[(min(v, k), max(v, k))] == x)
              for x in range(4)) for c in leaves for v in range(8)}
print(f"nodes {nodes}, leaves {len(leaves)}: antiprism relabellings {n_ap}, "
      f"aligned {n_al}, unexplained {n_bad}; vertex degree patterns (A,D,N,F) = {degs}")
assert n_bad == 0
