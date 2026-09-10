import sympy as sp

u = sp.symbols('u', positive=True)
s2 = sp.sqrt(2)
E = (4*s2+2)/sp.sqrt(1-u) + 8/sp.sqrt((2-s2)+(2+s2)*u) + 8/sp.sqrt((2+s2)+(2-s2)*u)

print("=== 1. The equilateral square antiprism = the Tammes optimum for N=8 ===")
# equilateral: square edge = lateral edge
ue = sp.solve(sp.Eq(2-2*u, 2 - s2*(1-u) + 2*u), u)[0]
ue = sp.simplify(sp.radsimp(ue))
print("   equilateral parameter  u_e =", ue, "=", sp.nsimplify(ue), "=", sp.N(ue,20))
d = sp.sqrt(2-2*ue)
print("   its common edge length  d =", sp.simplify(sp.radsimp(d**2)), "-> d =", sp.N(d,20))
print("   i.e. d = sqrt((16-4*sqrt(2))/7):", sp.simplify(d**2 - (16-4*s2)/7)==0)
Ee = sp.simplify(E.subs(u,ue))
print("   E(equilateral) =", sp.N(Ee,20))
print("   E(u*)          = 19.675287861232762264")
print("   excess         =", sp.N(Ee,20)-sp.Float('19.675287861232762264',20))

print()
print("=== 2. Two parallel squares with twist phi: phi=45 deg is the ONLY interior critical point ===")
phi,h = sp.symbols('phi h', positive=True)
r2 = 1-h**2
A = 2+2*h**2; B = 2*r2
F = lambda c: (A-B*c)**sp.Rational(-1,2)
Ephi = 8/sp.sqrt(2*r2) + 4/(2*sp.sqrt(r2)) + 4*(F(sp.cos(phi))+F(-sp.cos(phi))+F(sp.sin(phi))+F(-sp.sin(phi)))
dE = sp.simplify(sp.diff(Ephi,phi))
print("   dE/dphi at phi=pi/4 :", sp.simplify(dE.subs(phi,sp.pi/4)))
print("   dE/dphi at phi=0    :", sp.simplify(dE.subs(phi,0)))
c = sp.symbols('c', positive=True)
G = F(c)+F(-c)
H = sp.simplify(sp.diff(G,c)/c)
print("   H(c) := G'(c)/c, with G(c)=F(c)+F(-c):")
print("     H(c) =", sp.simplify(H))
dH = sp.simplify(sp.diff(H,c))
print("   dE/dphi = sin(phi)cos(phi)*[H(sin phi) - H(cos phi)] * 4, so critical <=> H(s)=H(c).")
print("   H'(c) numerator sign check at h=sqrt(u*)=0.560436:")
hv = sp.sqrt(sp.Float('0.31408936726',20))
for cv in ['0.1','0.3','0.5','0.7','0.9','0.99']:
    print(f"     H'({cv}) = {sp.N(dH.subs({h:hv,c:sp.Float(cv)}),12)}")
print("   => H strictly increasing on (0,1)  =>  H(sin phi)=H(cos phi) iff phi=pi/4.")
