#!/usr/bin/env python3
import sympy as sp
x,y,z,w,u,v=sp.symbols('x y z w u v')
A=y+z-w
Q=-x*z-x*w+y**2+y*z+z*w
C=x**2*w+x*y*z-x*y*w-x*z*w+y*z*w+z**2*w-z*w**2
R=v**4-u**3*v**3+(u-u**3-2*u**4)*v**2-(u**3+u**4+2*u**5)*v+u**7
D=u**2+u+v
Xi=u*v*D
Yi=u*(u**2*v-u**2+v)
Zi=u**2*D
Wi=u**4+u**3*v-v**2
print('Q inverse =',sp.factor(Q.subs({x:Xi,y:Yi,z:Zi,w:Wi})))
print('C inverse =',sp.factor(C.subs({x:Xi,y:Yi,z:Zi,w:Wi})))
# Cleared reverse-composition projective coordinates after removing a common x^3.
B=z*x+z*A+x*A
PX=x*B
PY=z*(x**2-z*A+A**2)
PZ=z*B
PW=x*(z**2+x*z-A**2)
G=sp.groebner([Q,C],y,w,x,z,order='grevlex')
for name,F in [('PY-yB',sp.expand(PY-y*B)),('PW-wB',sp.expand(PW-w*B))]:
    quot,rem=G.reduce(F)
    print(name,'remainder=',sp.factor(rem))
    print(name,'quotients=',[sp.factor(q) for q in quot])
# characteristic 2 relation and derivatives
R2=sp.Poly(R,u,v, modulus=2)
print('R2=',R2.as_expr())
print('R2 factor=',sp.factor_list(R2.as_expr(), modulus=2))
print('dR2du=',sp.diff(R2.as_expr(),u))
print('dR2dv=',sp.diff(R2.as_expr(),v))
# Check the exact forward composition identities over Z.
Apr=sp.factor(Yi+Zi-Wi)
print('A inverse=',Apr)
print('X-uA=',sp.factor(Xi-u*Apr))
print('X2-vZA=',sp.factor(Xi**2-v*Zi*Apr))
