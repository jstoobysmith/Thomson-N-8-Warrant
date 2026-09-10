from mpmath import mp, mpf, sqrt, cos, sin, pi, findroot, matrix
mp.dps=30
TARGET=mpf('19.6752878612327622644065181715')

def E(P):
    t=mpf(0)
    for i in range(len(P)):
        for j in range(i+1,len(P)):
            t+=1/sqrt(sum((P[i][k]-P[j][k])**2 for k in range(3)))
    return t
def ring(n,h,off=mpf(0)):
    r=sqrt(1-h*h)
    return [[r*cos(2*pi*k/n+off), r*sin(2*pi*k/n+off), h] for k in range(n)]
def minimise(f,x0):
    x=[mpf(v) for v in x0]; n=len(x)
    for _ in range(400):
        e=mpf(10)**-12
        g=[]; 
        for i in range(n):
            xp=x[:]; xp[i]+=e; xm=x[:]; xm[i]-=e
            g.append((f(xp)-f(xm))/(2*e))
        Hm=matrix(n,n)
        for i in range(n):
            for j in range(n):
                xpp=x[:]; xpp[i]+=e; xpp[j]+=e
                xpm=x[:]; xpm[i]+=e; xpm[j]-=e
                xmp=x[:]; xmp[i]-=e; xmp[j]+=e
                xmm=x[:]; xmm[i]-=e; xmm[j]-=e
                Hm[i,j]=(f(xpp)-f(xpm)-f(xmp)+f(xmm))/(4*e*e)
        try: step=mp.lu_solve(Hm, matrix(g))
        except Exception: break
        x=[x[i]-step[i] for i in range(n)]
        if max(abs(step[i]) for i in range(n))<mpf(10)**-20: break
    return x, f(x)

print(f"{'family (closed form)':44s} {'optimised energy':>26s}  {'excess over E(u*)':>20s}")
res={}

# D4d square antiprism (reference)
f=lambda p: E(ring(4,p[0])+ring(4,-p[0],pi/4))
x,e=minimise(f,[mpf('0.5604')]); res['square antiprism  D4d  (4+4)']=e

# asymmetric antiprism: two different heights, twist 45 deg
f=lambda p: E(ring(4,p[0])+ring(4,-p[1],pi/4))
x2,e2=minimise(f,[mpf('0.55'),mpf('0.57')]); res['antiprism, unequal heights (4+4)']=e2
asym=(x2[0],x2[1])

# D3d: two poles + two staggered triangles  (1+3+3+1)
f=lambda p: E([[mpf(0),mpf(0),mpf(1)],[mpf(0),mpf(0),mpf(-1)]]+ring(3,p[0])+ring(3,-p[0],pi/3))
x,e=minimise(f,[mpf('0.4')]); res['bicapped antiprism D3d (1+3+3+1)']=e

# D3h: eclipsed
f=lambda p: E([[mpf(0),mpf(0),mpf(1)],[mpf(0),mpf(0),mpf(-1)]]+ring(3,p[0])+ring(3,-p[0]))
x,e=minimise(f,[mpf('0.4')]); res['bicapped prism    D3h (1+3+3+1)']=e

# 1+4+3 : pole + square + triangle
f=lambda p: E([[mpf(0),mpf(0),mpf(1)]]+ring(4,p[0])+ring(3,-p[1],mpf(0)))
x,e=minimise(f,[mpf('0.4'),mpf('0.6')]); res['capped  (1+4+3)']=e

# 1+3+4 with relative twist
f=lambda p: E([[mpf(0),mpf(0),mpf(1)]]+ring(3,p[0])+ring(4,-p[1],p[2]))
x,e=minimise(f,[mpf('0.45'),mpf('0.55'),mpf('0.3')]); res['capped, twisted (1+3+4)']=e

# 1+6+1 hexagonal bipyramid
res['hexagonal bipyramid (1+6+1)']=E([[mpf(0),mpf(0),mpf(1)],[mpf(0),mpf(0),mpf(-1)]]+ring(6,mpf(0)))

# 2+4+2  : two poles-ish pairs
f=lambda p: E(ring(2,p[0])+ring(4,p[1],pi/4)+ring(2,-p[2],pi/2))
x,e=minimise(f,[mpf('0.8'),mpf('0.0'),mpf('0.8')]); res['(2+4+2) stacked']=e

# square prism (cube family), twist 0
f=lambda p: E(ring(4,p[0])+ring(4,-p[0]))
x,e=minimise(f,[mpf('0.577')]); res['square prism / cube D4h (4+4)']=e

for k,v in res.items():
    mark='  *** BEATS E(u*) ***' if v<TARGET-mpf(10)**-18 else ''
    print(f"{k:44s} {mp.nstr(v,22):>26s}  {mp.nstr(v-TARGET,10):>20s}{mark}")
print()
print("unequal-height antiprism optimum: h1 =", mp.nstr(asym[0],20), " h2 =", mp.nstr(asym[1],20))
print("   -> h1 - h2 =", mp.nstr(asym[0]-asym[1],10), " (equal heights forced)")
