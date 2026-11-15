#!/usr/bin/env python3
from phase2_diag import tate_data,tate_normal_form,sutherland
from check_sutherland import plane
x,y,a4,a6=tate_data()
s,b,c=tate_normal_form(x,y,a4)
xs,ys=sutherland(b,c)
f=plane(xs,ys)
print('b',b.val(),b.lead(),'c',c.val(),c.lead(),flush=True)
print('xs',xs.val(),xs.lead(),'ys',ys.val(),ys.lead(),flush=True)
print('PLANE_RESIDUAL',f.val(),f.lead(),flush=True)
print('PLANE_NONZERO',[(i,f.coeff(i)) for i in range(-20,31) if f.coeff(i)],flush=True)
