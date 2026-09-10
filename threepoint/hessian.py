from mpmath import mp, mpf, sqrt, cos, sin, matrix, eig, findroot, mpmathify
mp.dps = 40

def apE(u):
    s2=sqrt(2)
    return (4*s2+2)/sqrt(1-u)+8/sqrt((2-s2)+(2+s2)*u)+8/sqrt((2+s2)+(2-s2)*u)
d=mpf(10)**-30
ustar=findroot(lambda u:(apE(u+d)-apE(u-d))/(2*d), mpf('0.3140893672'))
print("u*     =", mp.nstr(ustar,30))
print("E(u*)  =", mp.nstr(apE(ustar),30))
h=sqrt(ustar); r=sqrt(1-ustar); s=r/sqrt(2)
P0=[[r,0,h],[0,r,h],[-r,0,h],[0,-r,h],[s,s,-h],[-s,s,-h],[-s,-s,-h],[s,-s,-h]]
P0=[[mpf(x) for x in p] for p in P0]

# tangent frames at each point
def frame(p):
    ax=[mpf(0),mpf(0),mpf(1)]
    if abs(p[2])>mpf('0.9'): ax=[mpf(1),mpf(0),mpf(0)]
    e1=[ax[1]*p[2]-ax[2]*p[1], ax[2]*p[0]-ax[0]*p[2], ax[0]*p[1]-ax[1]*p[0]]
    n=sqrt(sum(x*x for x in e1)); e1=[x/n for x in e1]
    e2=[p[1]*e1[2]-p[2]*e1[1], p[2]*e1[0]-p[0]*e1[2], p[0]*e1[1]-p[1]*e1[0]]
    return e1,e2
FR=[frame(p) for p in P0]

def config(v):
    """v: 16 tangent coords -> 8 points on the sphere (exponential-free: move then normalise)"""
    out=[]
    for i,p in enumerate(P0):
        e1,e2=FR[i]; a=v[2*i]; b=v[2*i+1]
        q=[p[k]+a*e1[k]+b*e2[k] for k in range(3)]
        n=sqrt(sum(x*x for x in q))
        out.append([x/n for x in q])
    return out
def energy(v):
    X=config(v); tot=mpf(0)
    for i in range(8):
        for j in range(i+1,8):
            tot+=1/sqrt(sum((X[i][k]-X[j][k])**2 for k in range(3)))
    return tot
z=[mpf(0)]*16
E0=energy(z)
print("E at base point (check) =", mp.nstr(E0,30))

eps=mpf(10)**-8
H=matrix(16,16)
for i in range(16):
    for j in range(i,16):
        vpp=z[:]; vpp[i]+=eps; vpp[j]+=eps
        vpm=z[:]; vpm[i]+=eps; vpm[j]-=eps
        vmp=z[:]; vmp[i]-=eps; vmp[j]+=eps
        vmm=z[:]; vmm[i]-=eps; vmm[j]-=eps
        val=(energy(vpp)-energy(vpm)-energy(vmp)+energy(vmm))/(4*eps*eps)
        H[i,j]=val; H[j,i]=val
ev=mp.eigsy(H, eigvals_only=True)
ev=sorted([mp.mpf(x) for x in ev])
print("\n=== Hessian of the energy at the square antiprism (16 tangent directions) ===")
for k,x in enumerate(ev):
    tag=""
    if abs(x)<mpf('1e-6'): tag="   <- zero mode (rotation)"
    print(f"   lambda_{k+1:2d} = {mp.nstr(x,12):>18s}{tag}")
nz=[x for x in ev if abs(x)>=mpf('1e-6')]
print(f"\n   zero modes: {16-len(nz)} (expected 3: the rotations of SO(3))")
print(f"   smallest nonzero eigenvalue: {mp.nstr(min(nz),12)}")
print(f"   all nonzero eigenvalues positive: {all(x>0 for x in nz)}")
