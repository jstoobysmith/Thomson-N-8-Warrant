"""[Tri5b] Parse Thomson/ThreePoint/CertData.lean into python data, exactly as Lean sees it."""
import re, os
from fractions import Fraction as Fr

ROOT = "/Users/josephsmith/LocalGithub/ThompsonEight"
SRC = open(os.path.join(ROOT, "Thomson/ThreePoint/CertData.lean")).read()

def _clean(expr):
    expr = expr.replace(" : ℝ", "").replace("ℝ", "")
    expr = expr.replace("^", "**")
    return expr

def _parse_match_table(name):
    """returns dict[(i,j,k)] -> python expression string in variable u"""
    m = re.search(r"def %s[^\n]*\n((?:\s*\|[^\n]*\n)+)" % name, SRC)
    body = m.group(1)
    out = {}
    for line in body.strip().split("\n"):
        line = line.strip()
        mm = re.match(r"\|\s*([^=]+?)\s*=>\s*(.*)$", line)
        key, val = mm.group(1), mm.group(2)
        if "_" in key: continue
        ks = tuple(int(x.strip()) for x in key.split(","))
        out[ks] = _clean(val).replace("uStar", "u")
    return out

BPOLY = _parse_match_table("Bpoly")
HFIXT = _parse_match_table("HfixTable")

def _parse_vec(name):
    m = re.search(r"def %s[^\n]*?:=\s*!\[(.*?)\]\s*\n" % name, SRC, re.S)
    body = m.group(1)
    items = []
    depth = 0; cur = ""
    for ch in body:
        if ch == "(": depth += 1
        if ch == ")": depth -= 1
        if ch == "," and depth == 0:
            items.append(cur); cur = ""
        else:
            cur += ch
    items.append(cur)
    return [i.strip() for i in items if i.strip()]

SLOT = [tuple(int(x) for x in re.findall(r"\d+", s)) for s in _parse_vec("slot")]
PIVNUM_STR = [_clean(s) for s in _parse_vec("pivotsNum")]

def a_consts(F=Fr):
    def g(name):
        m = re.search(r"def %s : ℝ := \((.*?) : ℝ\)" % name, SRC)
        n, d = m.group(1).split("/")
        return F(int(n), int(d))
    return g("a0Fix"), g("a1Fix"), g("lamFix")

def rat(s, F):
    """evaluate a rational literal string like (944368722101/1000000000000)"""
    s = s.strip().strip("()")
    if "/" in s:
        n, d = s.split("/")
        return F(int(n.strip().strip("()"))) / F(int(d.strip().strip("()")))
    return F(int(s))

def pivotsNum(F=Fr):
    return [rat(s, F) for s in PIVNUM_STR]

def evalpoly(expr, u, F):
    """evaluate a parsed expression with numeric type of u; ints -> F"""
    # tokens: numbers like 4743/10000 ; use a safe eval with Fraction division
    def repl(m):
        return "(F(%s)/F(%s))" % (m.group(1), m.group(2))
    e = re.sub(r"(\d+)/(\d+)", repl, expr)
    e = re.sub(r"(?<![\w.)])(\d+)(?![\w./])", r"F(\1)", e)
    return eval(e, {"F": F, "u": u})

def B_entries(u, F):
    """B[k][i][a] for k in 0..5, size 9-k"""
    out = []
    for k in range(6):
        n = 9 - k
        M = [[F(0)] * n for _ in range(n)]
        for (kk, i, a), expr in BPOLY.items():
            if kk == k:
                M[i][a] = evalpoly(expr, u, F)
        out.append(M)
    return out

def Hfix_entries(F):
    out = []
    for k in range(6):
        n = 9 - k
        M = [[F(0)] * n for _ in range(n)]
        for (kk, a, b), expr in HFIXT.items():
            if kk == k:
                v = rat(expr.replace("(", "").replace(")", ""), F)
                M[a][b] = v; M[b][a] = v
        out.append(M)
    return out
