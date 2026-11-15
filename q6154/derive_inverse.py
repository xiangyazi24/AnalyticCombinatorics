#!/usr/bin/env python3
import sympy as sp
u,v,t=sp.symbols('u v t')
x,y,z,w=sp.symbols('x y z w')
R=v**4-u**3*v**3+(u-u**3-2*u**4)*v**2-(u**3+u**4+2*u**5)*v+u**7
Q=-x*z-x*w+y**2+y*z+z*w
C=x**2*w+x*y*z-x*y*w-x*z*w+y*z*w+z**2*w-z*w**2
# Natural projective normalization forced by the forward formulas.
d=v-u**2
subs={x:u*v,z:u**2,y:t+d,w:t}
q=sp.factor(Q.subs(subs))
c=sp.factor(C.subs(subs))
print('Qsub=',q)
print('Csub=',c)
# Reduce C modulo Q as a polynomial in t.
rem=sp.rem(sp.Poly(c,t),sp.Poly(q,t)).as_expr()
print('Crem=',sp.factor(rem))
sol=sp.solve(sp.Eq(rem,0),t)
print('solutions=',[sp.factor(s) for s in sol])
for s in sol:
    nums=[]; dens=[]
    for e in [u*v,s+d,u**2,s]:
        e=sp.factor(e)
        n,de=sp.fraction(e)
        nums.append(n);dens.append(de)
    common=sp.lcm(dens)
    coords=[sp.factor(e*common) for e in [u*v,s+d,u**2,s]]
    print('common=',sp.factor(common))
    print('coords=',coords)
    qq=sp.factor(Q.subs(dict(zip([x,y,z,w],coords))))
    cc=sp.factor(C.subs(dict(zip([x,y,z,w],coords))))
    print('Qcoords=',qq)
    print('Ccoords=',cc)
    # Divide by R where possible.
    print('Q/R=',sp.factor(qq/R) if qq else 0)
    print('C/R=',sp.factor(cc/R) if cc else 0)
    A=sp.factor(coords[1]+coords[2]-coords[3])
    Un=sp.factor(coords[0]); Ud=A
    Vn=sp.factor(coords[0]**2); Vd=sp.factor(coords[2]*A)
    print('Ucomp num-u*den=',sp.factor(Un-u*Ud))
    print('Vcomp num-v*den=',sp.factor(Vn-v*Vd))
