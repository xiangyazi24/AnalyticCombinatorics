#!/usr/bin/env python3
from __future__ import annotations
from fractions import Fraction
from itertools import combinations_with_replacement
from math import gcd
from functools import reduce
import json
import sympy as sp
from phase2_diag import LS,tate_data,tate_normal_form,sutherland,canonical

N=100

def q_units():
    def addE(d,g,e):
        d[g%25]=d.get(g%25,0)+e;d[(-g)%25]=d.get((-g)%25,0)+e
    def mul(a,m,e):
        if e>=0:
            for _ in range(e):
                for n in range(N,m-1,-1):a[n]-=a[n-m]
        else:
            for _ in range(-e):
                for n in range(m,N+1):a[n]+=a[n-m]
    def build(exps,shift):
        a=[0]*(N+1);a[0]=1
        for m in range(1,N+1):
            e=exps.get(m%25,0)
            if e:mul(a,m,e)
        return LS({i+shift:c for i,c in enumerate(a[:N+1-shift]) if c})
    eu={};ev={}
    for g in (1,7):addE(eu,g,1)
    for g in (2,11):addE(eu,g,-1)
    for g in (1,7,3,4):addE(ev,g,1)
    for g in (2,11):addE(ev,g,-2)
    return build(eu,1),build(ev,2)

def norm_coords():
    X,Y,a4,a6=tate_data();s,b,c=tate_normal_form(X,Y,a4);sx,sy=sutherland(b,c)
    raw=canonical(sx,sy)
    v=min(t.val() for t in raw);idx=next(i for i,t in enumerate(raw) if t.val()==v);lead=raw[idx].coeff(v)
    scale=LS.qpow(-v,Fraction(1,1)/lead)
    return [scale*t for t in raw]

def monomials(coords,d):
    out=[];names=[]
    for inds in combinations_with_replacement(range(4),d):
        t=LS.c(1); ex=[0]*4
        for i in inds:t=t*coords[i];ex[i]+=1
        out.append(t)
        nm=''.join('xyzw'[i]+(f'^{ex[i]}' if ex[i]>1 else '') for i in range(4) if ex[i]) or '1'
        names.append(nm)
    return names,out

def primitive(vec):
    den=1
    for z in vec:den=sp.ilcm(den,int(sp.denom(z)))
    a=[int(z*den) for z in vec];g=reduce(gcd,(abs(x) for x in a if x),0);a=[x//g for x in a]
    q=next((x for x in reversed(a) if x),1)
    if q<0:a=[-x for x in a]
    return a

def fit(f,coords,d):
    names,M=monomials(coords,d);cols=M+[f*m for m in M]
    rows=[[c.coeff(q) for c in cols] for q in range(0,N+1)]
    ns=sp.Matrix(rows).nullspace()
    ans=[]
    for v in ns:
        a=primitive(v)
        # equation sum a_i M_i + sum a_{m+i} f M_i=0,
        # so f = numerator/denominator with numerator=-first, denominator=second.
        m=len(M); num=[-x for x in a[:m]];den=a[m:]
        ans.append({'raw':a,'numerator':num,'denominator':den})
    return {'degree':d,'names':names,'nullity':len(ns),'solutions':ans}

def main():
    coords=norm_coords();U,V=q_units();out={}
    for label,f in [('U',U),('V',V)]:
        out[label]=[]
        for d in (1,2,3):
            z=fit(f,coords,d);out[label].append(z)
            print(label,'degree',d,'nullity',z['nullity'],flush=True)
            if z['nullity']:
                print(json.dumps(z,indent=2),flush=True)
                if label=='U' or d>=2:break
    open('q6154/forward-fit.json','w').write(json.dumps(out,indent=2))

if __name__=='__main__':main()
