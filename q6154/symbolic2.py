#!/usr/bin/env python3
import sympy as sp
x,y,z,w=sp.symbols('x y z w')
A=y+z-w
B=z*x+z*A+x*A
Q=-x*z-x*w+y**2+y*z+z*w
C=x**2*w+x*y*z-x*y*w-x*z*w+y*z*w+z**2*w-z*w**2
I=sp.expand(z*(x**2-z*A+A**2)-y*B)
a,b,c,d,e=sp.symbols('a b c d e')
L=a*x+b*y+c*z+d*w
P=sp.Poly(sp.expand(I-(L*Q+e*C)),x,y,z,w)
sol=sp.solve(list(P.coeffs()),[a,b,c,d,e], dict=True)
print('I=',sp.factor(I))
print('solutions=',sol)
for s in sol:
    print('identity remainder=',sp.expand(I-(L*Q+e*C)).subs(s))
