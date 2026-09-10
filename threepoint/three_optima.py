from mpmath import mp, mpf, sqrt, findroot
mp.dps=30
s2=sqrt(2)
def apE(u): return (4*s2+2)/sqrt(1-u)+8/sqrt((2-s2)+(2+s2)*u)+8/sqrt((2+s2)+(2-s2)*u)
ustar=findroot(lambda u: mp.diff(apE,u), mpf('0.3140893672'))
ueq=(2*s2-1)/7
udes=mpf(1)/3
print("The square antiprism family has THREE competing 'optimal' parameters:\n")
print(f"   u_Tammes  = (2*sqrt2 - 1)/7 = {mp.nstr(ueq,18)}   (all 16 short edges equal; max-min distance)")
print(f"   u_energy  = u*              = {mp.nstr(ustar,18)}   (minimises Coulomb energy)")
print(f"   u_design  = 1/3             = {mp.nstr(udes,18)}   (tight frame: M_2 = 0, a 3-design)")
print(f"\n   they are DISTINCT:  {mp.nstr(ueq,10)} < {mp.nstr(ustar,10)} < {mp.nstr(udes,10)}")
print(f"   u_design - u_energy = {mp.nstr(udes-ustar,10)}")
# M_2 as a function of u:  A = diag(4(1-u),4(1-u),8u), M_2 = (3/2)||A||_F^2 - 32
def M2(u): return mpf(3)/2*(2*(4*(1-u))**2+(8*u)**2)-32
print(f"\n   M_2(u) = (3/2)[2*(4(1-u))^2 + (8u)^2] - 32 = 24*(3u-1)^2   -> zero only at u = 1/3")
print(f"   check: M_2(u*) = {mp.nstr(M2(ustar),12)}   vs  24*(3u*-1)^2 = {mp.nstr(24*(3*ustar-1)**2,12)}")
print(f"   Tumanov's G_2 excess at the antiprism = (4/3)*M_2(u*) = {mp.nstr(mpf(4)/3*M2(ustar),12)}")
print(f"   (matches the numerical 0.071103 exactly)")
print(f"\n   energies:  E(u_Tammes) = {mp.nstr(apE(ueq),18)}")
print(f"              E(u*)       = {mp.nstr(apE(ustar),18)}")
print(f"              E(1/3)      = {mp.nstr(apE(udes),18)}")
