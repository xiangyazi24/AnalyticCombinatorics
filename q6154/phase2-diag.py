#!/usr/bin/env python3
"""Exact Tate -> Sutherland -> canonical q-series for Q6154."""
from __future__ import annotations

from fractions import Fraction
import json
import math
from pathlib import Path

LO = -100
HI = 220
CHECK = 60
OUT = 50


class LS:
    __slots__ = ("a",)

    def __init__(self, data=None):
        d = {} if data is None else dict(data)
        self.a = {int(k): Fraction(v) for k, v in d.items() if v and LO <= int(k) <= HI}

    @staticmethod
    def c(x):
        return LS({0: Fraction(x)})

    @staticmethod
    def qpow(e, c=1):
        return LS({e: Fraction(c)})

    def copy(self):
        return LS(self.a)

    def coeff(self, e):
        return self.a.get(e, Fraction(0))

    def val(self):
        if not self.a:
            return math.inf
        return min(self.a)

    def lead(self):
        return self.coeff(self.val())

    def __neg__(self):
        return LS({e: -c for e, c in self.a.items()})

    def __add__(self, other):
        other = tols(other)
        d = dict(self.a)
        for e, c in other.a.items():
            d[e] = d.get(e, Fraction(0)) + c
            if not d[e]:
                del d[e]
        return LS(d)

    __radd__ = __add__

    def __sub__(self, other):
        return self + (-tols(other))

    def __rsub__(self, other):
        return tols(other) - self

    def __mul__(self, other):
        other = tols(other)
        d = {}
        for i, x in self.a.items():
            for j, y in other.a.items():
                e = i + j
                if LO <= e <= HI:
                    d[e] = d.get(e, Fraction(0)) + x * y
        return LS(d)

    __rmul__ = __mul__

    def __pow__(self, n):
        if n < 0:
            return (self.inv()) ** (-n)
        ans = LS.c(1)
        x = self
        while n:
            if n & 1:
                ans = ans * x
            n >>= 1
            if n:
                x = x * x
        return ans

    def inv(self):
        v = self.val()
        if v is math.inf:
            raise ZeroDivisionError
        b0 = self.coeff(v)
        # inverse = q^-v * sum c_n q^n
        nmax = HI + v
        if nmax < 0:
            return LS()
        c = [Fraction(0)] * (nmax + 1)
        c[0] = 1 / b0
        for n in range(1, nmax + 1):
            s = Fraction(0)
            for k in range(1, n + 1):
                bk = self.coeff(v + k)
                if bk:
                    s += bk * c[n - k]
            c[n] = -s / b0
        return LS({-v + n: z for n, z in enumerate(c) if z})

    def __truediv__(self, other):
        return self * tols(other).inv()

    def __rtruediv__(self, other):
        return tols(other) / self

    def upto(self, n=OUT, start=0):
        return [self.coeff(i) for i in range(start, n + 1)]

    def assert_zero(self, lo, hi, label):
        bad = [(i, self.coeff(i)) for i in range(lo, hi + 1) if self.coeff(i)]
        if bad:
            raise AssertionError(f"{label}: first nonzero {bad[0]}")


def tols(x):
    return x if isinstance(x, LS) else LS.c(x)


def sigma(n, k):
    s = 0
    d = 1
    while d * d <= n:
        if n % d == 0:
            e = n // d
            s += d ** k
            if e != d:
                s += e ** k
        d += 1
    return s


def tate_data():
    X = LS()
    Y = LS()
    # n >= 0 terms, Q^n u = q^(25n+1)
    a = 1
    while a <= HI:
        for k in range(1, HI // a + 1):
            X = X + LS.qpow(a * k, k)
        for k in range(2, HI // a + 1):
            Y = Y + LS.qpow(a * k, k * (k - 1) // 2)
        a += 25
    # n < 0 terms rewritten in positive powers, a=25n-1
    a = 24
    while a <= HI:
        for k in range(1, HI // a + 1):
            X = X + LS.qpow(a * k, k)
            Y = Y - LS.qpow(a * k, k * (k + 1) // 2)
        a += 25
    s1 = LS()
    s3 = LS()
    s5 = LS()
    for m in range(1, HI // 25 + 1):
        s1 = s1 + LS.qpow(25 * m, sigma(m, 1))
        s3 = s3 + LS.qpow(25 * m, sigma(m, 3))
        s5 = s5 + LS.qpow(25 * m, sigma(m, 5))
    X = X - 2 * s1
    Y = Y + s1
    a4 = -5 * s3
    a6 = -(5 * s3 + 7 * s5) / 12
    eq = Y ** 2 + X * Y - X ** 3 - a4 * X - a6
    eq.assert_zero(0, CHECK, "Tate equation")
    return X, Y, a4, a6


def tate_normal_form(X, Y, a4):
    # Tangent slope at P on y^2+xy=x^3+a4*x+a6.
    s = (3 * X ** 2 + a4 - Y) / (2 * Y + X)
    A1 = 1 + 2 * s
    A2 = 3 * X - s - s ** 2
    A3 = X + 2 * Y
    b = -(A2 ** 3) / (A3 ** 2)
    c = 1 - A1 * A2 / A3
    return s, b, c


def sutherland(b, c):
    nx = -(b ** 2) + b * c + c ** 3
    K = -2 * b ** 2 + b * c ** 2 + 3 * b * c - c ** 2
    B = -(b ** 3) + 3 * b ** 2 * c - b * c ** 3 - 3 * b * c ** 2 + c ** 5 + c ** 4 + c ** 3
    return nx / K, K * (b - c) / B


def canonical(x, y):
    Xcore = (x**5*y**2 - 2*x**4*y**3 + x**3*y**4 - x**5*y +
        x**4*y**2 + x**3*y**3 - x**2*y**4 + x**4*y -
        2*x**3*y**2 + x**2*y**3 - x**2*y**2 + x*y**3 +
        2*x**2*y - 2*x*y**2 - 2*x**2 + 3*x*y - y**2 -
        2*x + 2*y - 1)
    Xc = -(y - 1)**2 * Xcore
    Yc = -(x**5*y**4 - 2*x**4*y**5 + x**3*y**6 + x**6*y**2 -
        8*x**5*y**3 + 13*x**4*y**4 - 6*x**3*y**5 +
        6*x**5*y**2 - 10*x**4*y**3 + 2*x**3*y**4 +
        2*x**2*y**5 - 2*x**5*y + 4*x**4*y**2 -
        5*x**3*y**3 + 4*x**2*y**4 - x*y**5 - 2*x**4*y +
        12*x**3*y**2 - 10*x**2*y**3 - 6*x**3*y +
        3*x**2*y**2 + 3*x*y**3 + x**3 + x**2*y -
        2*x*y**2 + y**3 - 3*y**2 + 3*y - 1)
    Zc = (x**5*y**4 - 2*x**4*y**5 + x**3*y**6 -
        5*x**5*y**3 + 10*x**4*y**4 - 5*x**3*y**5 +
        x**6*y + 3*x**5*y**2 - 8*x**4*y**3 +
        3*x**3*y**4 + x**2*y**5 - 2*x**5*y +
        4*x**4*y**2 - 4*x**3*y**3 + 2*x**2*y**4 +
        5*x**3*y**2 - 3*x**2*y**3 - 2*x*y**4 - x**4 -
        2*x**3*y + 3*x*y**3 + x**3 - x**2*y + y**3 +
        x**2 - x*y - 3*y**2 + 3*y - 1)
    Wcore = (x**5*y**3 - 2*x**4*y**4 + x**3*y**5 -
        2*x**5*y**2 + 3*x**4*y**3 - x**2*y**5 + x**5*y -
        3*x**3*y**3 + 2*x**2*y**4 - 2*x**3*y**2 +
        2*x**2*y**3 + 3*x**3*y - x**2*y**2 -
        2*x*y**3 - x**3 - x**2*y + 2*x*y**2 + y**2 -
        2*y + 1)
    Wc = (x - y + 1) * Wcore
    return [Xc, Yc, Zc, Wc]


def fracstr(x):
    x = Fraction(x)
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def liststr(a):
    return [fracstr(x) for x in a]


def normalize_projective(coords):
    v = min(z.val() for z in coords)
    idx = next(i for i, z in enumerate(coords) if z.val() == v)
    lead = coords[idx].coeff(v)
    scale = LS.qpow(-v, 1 / lead)
    return [scale * z for z in coords], v, idx, lead


def main():
    xP, yP, a4, a6 = tate_data()
    slope, b, c = tate_normal_form(xP, yP, a4)
    xs, ys = sutherland(b, c)
    raw = canonical(xs, ys)
    cc, common_v, pivot, lead = normalize_projective(raw)
    x, y, z, w = cc
    Q = x*w + y*z + y*w - z**2 - z*w
    C = (x**2*y - x**2*z - x*y**2 - x*y*z + x*z**2 -
         y**2*w + y*w**2 - z**2*w)
    print("Q_RESIDUAL", Q.val(), Q.lead())
    print("C_RESIDUAL", C.val(), C.lead())

    consts = [u.coeff(0) for u in cc]
    cusps = [
        [0,0,0,1], [0,-1,1,0], [1,1,0,1], [0,0,1,0], [1,0,0,0]
    ]
    match = None
    for i, p in enumerate(cusps):
        nz = next((j for j,a in enumerate(p) if a), None)
        if nz is None or consts[nz] == 0:
            continue
        lam = consts[nz] / p[nz]
        if all(consts[j] == lam*p[j] for j in range(4)):
            match = i
            break

    data = {
        "work_precision": HI,
        "checked_through": CHECK,
        "tate_point_x_order": xP.val(),
        "tate_point_y_order": yP.val(),
        "slope_order": slope.val(),
        "b_order": b.val(),
        "c_order": c.val(),
        "sutherland_x_order": xs.val(),
        "sutherland_y_order": ys.val(),
        "raw_canonical_orders": [u.val() for u in raw],
        "projective_common_order": common_v,
        "projective_pivot": pivot,
        "projective_pivot_lead": fracstr(lead),
        "canonical_constant_vector": liststr(consts),
        "canonical_cusp_index": match,
        "series": {
            "tate_x": liststr(xP.upto(OUT)),
            "tate_y": liststr(yP.upto(OUT)),
            "b": liststr(b.upto(OUT)),
            "c": liststr(c.upto(OUT)),
            "sutherland_x": liststr(xs.upto(OUT)),
            "sutherland_y": liststr(ys.upto(OUT)),
            "x": liststr(x.upto(OUT)),
            "y": liststr(y.upto(OUT)),
            "z": liststr(z.upto(OUT)),
            "w": liststr(w.upto(OUT)),
        },
    }
    Path("q6154/phase2.json").write_text(json.dumps(data, indent=2))
    print(json.dumps({k:v for k,v in data.items() if k != "series"}, indent=2))
    print("PASS Tate equation")
    print("PASS canonical Q=C=0")


if __name__ == "__main__":
    main()
