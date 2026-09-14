"""[Tri5b] Generate the covering tree, accepting a leaf only on the EXACT integer model.

`tri5b_tree.py` accepted leaves on a float model with a safety factor of two; that model ignores
the widths of the certificate's interval data (the pivot slots are widened by 10^-12), so leaves
whose float bound sat just above the threshold fail the integer test that Lean performs — the very
first leaf of the old tree does.  Here the float model is only a filter that proposes the
S-procedure multiplier; every accepted leaf is confirmed by `leaf_exact`, the mirror of
`Thomson.Tri5b.leafCheck`.  Subtrees below depth `SPLIT_DEPTH` are built in parallel."""
import sys, time, pickle
import tri5b_tree as T

SCALE, MG, SIGMAS = T.SCALE, T.MG, T.SIGMAS
SPLIT_DEPTH = 9
MAXDEPTH = 70

_F = None
_AF = None
def _init():
    global _F, _AF
    if _F is None:
        _F = T.tensors(); _AF = T.float_tensor(_F)

def accept(b):
    """the leaf test Lean performs: the float model proposes a multiplier, the exact model rules"""
    for s in SIGMAS:
        if T.leaf_float(b, s / SCALE, _AF) > MG / SCALE and T.leaf_exact(b, s, _F):
            return True
    return False

def build(b, depth=0, stats=None):
    if stats is not None: stats[0] += 1
    if T.sorted_out(b) or T.in_cube(b) or T.gram_out_exact(b):
        if stats is not None: stats[1] += 1
        return [0]
    if accept(b):
        if stats is not None: stats[2] += 1
        return [0]
    if depth >= MAXDEPTH:
        raise Exception("depth limit at %s" % (b,))
    ax = T.splitAxis(b); m = T.splitPoint(b, ax)
    if not (b[2*ax] < m < b[2*ax+1]): raise Exception("bad split %s %d %d" % (b, ax, m))
    return [1] + build(T.lower(b, ax, m), depth+1, stats) + build(T.upper(b, ax, m), depth+1, stats)

def _worker(b):
    _init()
    st = [0, 0, 0]
    return build(b, 0, st), st

def frontier_build(b, depth, front):
    """the tree down to `SPLIT_DEPTH`; deeper subtrees become placeholders"""
    if T.sorted_out(b) or T.in_cube(b) or T.gram_out_exact(b): return [0]
    if accept(b): return [0]
    if depth >= SPLIT_DEPTH:
        front.append(b); return [('P', len(front) - 1)]
    ax = T.splitAxis(b); m = T.splitPoint(b, ax)
    return ([1] + frontier_build(T.lower(b, ax, m), depth+1, front)
                + frontier_build(T.upper(b, ax, m), depth+1, front))

if __name__ == "__main__":
    import multiprocessing as mp
    t0 = time.time()
    _init()
    front = []
    top = frontier_build(T.ROOT, 0, front)
    print("frontier %d boxes at depth %d (%.1f s)" % (len(front), SPLIT_DEPTH, time.time()-t0))
    sys.stdout.flush()
    with mp.Pool(processes=mp.cpu_count()) as pool:
        res = pool.map(_worker, front, chunksize=1)
    subs = [r[0] for r in res]
    st = [sum(r[1][i] for r in res) for i in range(3)]
    bits = []
    for x in top:
        if isinstance(x, tuple): bits.extend(subs[x[1]])
        else: bits.append(x)
    print("nodes %d  skipped %d  checked %d  bits %d  (%.1f s)"
          % (st[0], st[1], st[2], len(bits), time.time()-t0))
    n = T.bits_to_nat(bits)
    print("certificate: %d bits, %d decimal digits" % (len(bits), len(str(n))))
    pickle.dump({'bits': bits, 'nat': n}, open('tri5b_tree2.pkl', 'wb'))
