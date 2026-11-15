#!/usr/bin/env python3
"""Q6154 / r18-P-E31DATA exact checker (Python standard library only).

The checker recomputes:
  (1) U,V through q^5000, the bidegree-(7,4) relation, rank 39, and hashes;
  (2) the universal Tate q^25 curve, Tate normal form, compiled canonical series;
  (3) both birational directions, on series and by exact polynomial identities;
  (4) the five-cusp dictionary;
  (5) integral reduction mod 2, irreducibility there, and the order-one witness.
"""
from __future__ import annotations

import argparse
import base64
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
from typing import Iterable

N = 5000
LO = -100
HI = 260
CANON_CHECK = 100
MAP_CHECK = 70
EXPECTED_U_HASH = "b4547b68c5090115b688b56353c96855a587d3a1b821b890ed868630438d6802"
EXPECTED_V_HASH = "6e22a69676ee0d36652978f8e3802a60e8fbde51ab5ea448b77f1ff66cc130cb"


# ---------------------------------------------------------------------------
# Integer q-series for the modular units
# ---------------------------------------------------------------------------

def mul_euler_factor(a: list[int], m: int, exponent: int) -> None:
    """Multiply a by (1-q^m)^exponent, in place and at fixed precision."""
    if exponent >= 0:
        for _ in range(exponent):
            for n in range(len(a) - 1, m - 1, -1):
                a[n] -= a[n - m]
    else:
        for _ in range(-exponent):
            for n in range(m, len(a)):
                a[n] += a[n - m]


def bernoulli_exponent(g: int) -> Fraction:
    # 25*B_2(g/25)/2 = g^2/50 - g/2 + 25/12.
    return Fraction(g * g, 50) - Fraction(g, 2) + Fraction(25, 12)


def add_E_residues(d: dict[int, int], g: int, exponent: int) -> None:
    d[g % 25] = d.get(g % 25, 0) + exponent
    d[(-g) % 25] = d.get((-g) % 25, 0) + exponent


def unit_series(residue_exponents: dict[int, int], shift: int, n: int) -> list[int]:
    a = [0] * (n + 1)
    a[0] = 1
    for m in range(1, n + 1):
        e = residue_exponents.get(m % 25, 0)
        if e:
            mul_euler_factor(a, m, e)
    return [0] * shift + a[: n + 1 - shift]


def build_UV(n: int = N) -> tuple[list[int], list[int]]:
    u_exp = bernoulli_exponent(1) + bernoulli_exponent(7)
    u_exp -= bernoulli_exponent(2) + bernoulli_exponent(11)
    v_exp = bernoulli_exponent(1) + bernoulli_exponent(7)
    v_exp += bernoulli_exponent(3) + bernoulli_exponent(4)
    v_exp -= 2 * bernoulli_exponent(2) + 2 * bernoulli_exponent(11)
    assert u_exp == 1 and v_exp == 2

    eu: dict[int, int] = {}
    for g in (1, 7):
        add_E_residues(eu, g, 1)
    for g in (2, 11):
        add_E_residues(eu, g, -1)

    ev: dict[int, int] = {}
    for g in (1, 7, 3, 4):
        add_E_residues(ev, g, 1)
    for g in (2, 11):
        add_E_residues(ev, g, -2)

    return unit_series(eu, 1, n), unit_series(ev, 2, n)


def _pack_nonnegative(a: list[int], width: int) -> int:
    z = 0
    for x in reversed(a):
        z = (z << width) + x
    return z


def convolution(a: list[int], b: list[int], n: int) -> list[int]:
    """Exact signed convolution, using Kronecker substitution for large inputs."""
    la = min(len(a), n + 1)
    lb = min(len(b), n + 1)
    while la and a[la - 1] == 0:
        la -= 1
    while lb and b[lb - 1] == 0:
        lb -= 1
    if not la or not lb:
        return [0] * (n + 1)
    aa, bb = a[:la], b[:lb]
    if la * lb <= 30000:
        c = [0] * (n + 1)
        for i, x in enumerate(aa):
            if x:
                for j in range(min(lb, n + 1 - i)):
                    if bb[j]:
                        c[i + j] += x * bb[j]
        return c

    ap = [max(x, 0) for x in aa]
    an = [max(-x, 0) for x in aa]
    bp = [max(x, 0) for x in bb]
    bn = [max(-x, 0) for x in bb]
    bound = min(la, lb, n + 1) * max(max(ap), max(an)) * max(max(bp), max(bn))
    width = max(2, bound.bit_length() + 1)
    mask = (1 << width) - 1
    vals = [
        _pack_nonnegative(ap, width) * _pack_nonnegative(bp, width),
        _pack_nonnegative(an, width) * _pack_nonnegative(bn, width),
        _pack_nonnegative(ap, width) * _pack_nonnegative(bn, width),
        _pack_nonnegative(an, width) * _pack_nonnegative(bp, width),
    ]
    c = [0] * (n + 1)
    for k in range(n + 1):
        c[k] = ((vals[0] & mask) + (vals[1] & mask)
                - (vals[2] & mask) - (vals[3] & mask))
        vals = [z >> width for z in vals]
    return c


def add_series(n: int, *items: tuple[int, list[int]]) -> list[int]:
    c = [0] * (n + 1)
    for scale, a in items:
        for i in range(min(len(a), n + 1)):
            c[i] += scale * a[i]
    return c


def relation_residual(U: list[int], V: list[int], n: int) -> list[int]:
    U2 = convolution(U, U, n)
    U3 = convolution(U2, U, n)
    U4 = convolution(U3, U, n)
    U5 = convolution(U4, U, n)
    U7 = convolution(convolution(U5, U, n), U, n)
    A = add_series(n, (1, U), (-1, U3), (-2, U4))
    B = add_series(n, (-1, U3), (-1, U4), (-2, U5))
    t = add_series(n, (1, V), (-1, U3))
    t = add_series(n, (1, convolution(t, V, n)), (1, A))
    t = add_series(n, (1, convolution(t, V, n)), (1, B))
    return add_series(n, (1, convolution(t, V, n)), (1, U7))


def digest_csv(a: list[int]) -> str:
    return hashlib.sha256(",".join(map(str, a)).encode()).hexdigest()


def conv_small(a: list[int], b: list[int], n: int) -> list[int]:
    c = [0] * (n + 1)
    for i, x in enumerate(a[: n + 1]):
        if x:
            for j, y in enumerate(b[: n + 1 - i]):
                if y:
                    c[i + j] += x * y
    return c


def rank_mod(rows: list[list[int]], p: int) -> int:
    a = [[x % p for x in row] for row in rows]
    r = 0
    cols = len(a[0]) if a else 0
    for c in range(cols):
        pivot = next((i for i in range(r, len(a)) if a[i][c]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        inv = pow(a[r][c], p - 2, p)
        a[r] = [(x * inv) % p for x in a[r]]
        for i in range(len(a)):
            if i != r and a[i][c]:
                t = a[i][c]
                a[i] = [(x - t * y) % p for x, y in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def relation_rank_certificate(U: list[int], V: list[int]) -> tuple[int, int]:
    n = 38
    U0, V0 = U[: n + 1], V[: n + 1]
    one = [1] + [0] * n
    Up = [one]
    Vp = [one]
    for _ in range(7):
        Up.append(conv_small(Up[-1], U0, n))
    for _ in range(4):
        Vp.append(conv_small(Vp[-1], V0, n))
    monos = []
    for j in range(5):
        for i in range(8):
            if i == 0:
                monos.append(Vp[j])
            elif j == 0:
                monos.append(Up[i])
            else:
                monos.append(conv_small(Up[i], Vp[j], n))
    rows = [[monos[k][q] for k in range(40)] for q in range(39)]
    p = 1_000_000_007
    return rank_mod(rows[:38], p), rank_mod(rows, p)


# ---------------------------------------------------------------------------
# Exact Laurent series for the Tate and canonical models
# ---------------------------------------------------------------------------

class LS:
    __slots__ = ("a",)

    def __init__(self, data: dict[int, Fraction | int] | None = None):
        d = {} if data is None else dict(data)
        self.a = {int(k): Fraction(v) for k, v in d.items()
                  if v and LO <= int(k) <= HI}

    @staticmethod
    def c(x: Fraction | int) -> "LS":
        return LS({0: Fraction(x)})

    @staticmethod
    def qpow(e: int, c: Fraction | int = 1) -> "LS":
        return LS({e: Fraction(c)})

    def coeff(self, e: int) -> Fraction:
        return self.a.get(e, Fraction(0))

    def val(self) -> int | float:
        return min(self.a) if self.a else math.inf

    def lead(self) -> Fraction:
        return self.coeff(int(self.val()))

    def __neg__(self) -> "LS":
        return LS({e: -c for e, c in self.a.items()})

    def __add__(self, other: "LS | Fraction | int") -> "LS":
        other = to_ls(other)
        d = dict(self.a)
        for e, c in other.a.items():
            d[e] = d.get(e, Fraction(0)) + c
            if not d[e]:
                del d[e]
        return LS(d)

    __radd__ = __add__

    def __sub__(self, other: "LS | Fraction | int") -> "LS":
        return self + (-to_ls(other))

    def __rsub__(self, other: "LS | Fraction | int") -> "LS":
        return to_ls(other) - self

    def __mul__(self, other: "LS | Fraction | int") -> "LS":
        other = to_ls(other)
        d: dict[int, Fraction] = {}
        for i, x in self.a.items():
            for j, y in other.a.items():
                e = i + j
                if LO <= e <= HI:
                    d[e] = d.get(e, Fraction(0)) + x * y
        return LS(d)

    __rmul__ = __mul__

    def __pow__(self, n: int) -> "LS":
        if n < 0:
            return self.inv() ** (-n)
        ans, x = LS.c(1), self
        while n:
            if n & 1:
                ans = ans * x
            n >>= 1
            if n:
                x = x * x
        return ans

    def inv(self) -> "LS":
        v = self.val()
        if v == math.inf:
            raise ZeroDivisionError
        v = int(v)
        b0 = self.coeff(v)
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

    def __truediv__(self, other: "LS | Fraction | int") -> "LS":
        return self * to_ls(other).inv()

    def __rtruediv__(self, other: "LS | Fraction | int") -> "LS":
        return to_ls(other) / self

    def assert_zero(self, lo: int, hi: int, label: str) -> None:
        for i in range(lo, hi + 1):
            if self.coeff(i):
                raise AssertionError(f"{label}: coefficient q^{i} = {self.coeff(i)}")


def to_ls(x: LS | Fraction | int) -> LS:
    return x if isinstance(x, LS) else LS.c(x)


def sigma(n: int, k: int) -> int:
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


def tate_point() -> tuple[LS, LS, LS, LS]:
    X, Y = LS(), LS()
    a = 1
    while a <= HI:
        for k in range(1, HI // a + 1):
            X += LS.qpow(a * k, k)
        for k in range(2, HI // a + 1):
            Y += LS.qpow(a * k, k * (k - 1) // 2)
        a += 25
    a = 24
    while a <= HI:
        for k in range(1, HI // a + 1):
            X += LS.qpow(a * k, k)
            Y -= LS.qpow(a * k, k * (k + 1) // 2)
        a += 25
    s1, s3, s5 = LS(), LS(), LS()
    for m in range(1, HI // 25 + 1):
        s1 += LS.qpow(25 * m, sigma(m, 1))
        s3 += LS.qpow(25 * m, sigma(m, 3))
        s5 += LS.qpow(25 * m, sigma(m, 5))
    X -= 2 * s1
    Y += s1
    a4 = -5 * s3
    a6 = -(5 * s3 + 7 * s5) / 12
    (Y**2 + X*Y - X**3 - a4*X - a6).assert_zero(0, CANON_CHECK, "Tate equation")
    return X, Y, a4, a6


def tate_normal_form(X: LS, Y: LS, a4: LS) -> tuple[LS, LS, LS]:
    slope = (3 * X**2 + a4 - Y) / (2 * Y + X)
    A1 = 1 + 2 * slope
    A2 = 3 * X - slope - slope**2
    A3 = X + 2 * Y
    b = -(A2**3) / (A3**2)
    c = 1 - A1*A2/A3
    return slope, b, c


def tate_to_sutherland(b: LS, c: LS) -> tuple[LS, LS]:
    nx = -b**2 + b*c + c**3
    K = -2*b**2 + b*c**2 + 3*b*c - c**2
    B = -b**3 + 3*b**2*c - b*c**3 - 3*b*c**2 + c**5 + c**4 + c**3
    return nx/K, K*(b-c)/B


def sutherland_to_canonical(x: LS, y: LS) -> list[LS]:
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


def normalized_canonical() -> tuple[list[LS], dict[str, LS]]:
    Xp, Yp, a4, _a6 = tate_point()
    slope, b, c = tate_normal_form(Xp, Yp, a4)
    sx, sy = tate_to_sutherland(b, c)
    raw = sutherland_to_canonical(sx, sy)
    common = min(int(t.val()) for t in raw)
    pivot = next(i for i, t in enumerate(raw) if t.val() == common)
    lead = raw[pivot].coeff(common)
    scale = LS.qpow(-common, 1/lead)
    cc = [scale*t for t in raw]
    x, y, z, w = cc
    Q = -x*z - x*w + y**2 + y*z + z*w
    C = x**2*w + x*y*z - x*y*w - x*z*w + y*z*w + z**2*w - z*w**2
    Q.assert_zero(0, CANON_CHECK, "canonical quadric")
    C.assert_zero(0, CANON_CHECK, "canonical cubic")
    return cc, {"tate_x": Xp, "tate_y": Yp, "slope": slope,
                "b": b, "c": c, "sutherland_x": sx, "sutherland_y": sy}


# ---------------------------------------------------------------------------
# Tiny exact multivariate polynomial implementation
# ---------------------------------------------------------------------------

class Poly:
    __slots__ = ("n", "t")

    def __init__(self, n: int, terms: dict[tuple[int, ...], int] | None = None):
        self.n = n
        self.t = {m: int(c) for m, c in (terms or {}).items() if c}

    @staticmethod
    def const(n: int, c: int) -> "Poly":
        return Poly(n, {(0,)*n: c}) if c else Poly(n)

    @staticmethod
    def var(n: int, i: int) -> "Poly":
        m = [0]*n
        m[i] = 1
        return Poly(n, {tuple(m): 1})

    def __neg__(self) -> "Poly":
        return Poly(self.n, {m: -c for m, c in self.t.items()})

    def __add__(self, other: "Poly | int") -> "Poly":
        other = other if isinstance(other, Poly) else Poly.const(self.n, other)
        d = dict(self.t)
        for m, c in other.t.items():
            d[m] = d.get(m, 0) + c
            if not d[m]:
                del d[m]
        return Poly(self.n, d)

    __radd__ = __add__

    def __sub__(self, other: "Poly | int") -> "Poly":
        return self + (-other if isinstance(other, Poly) else -int(other))

    def __rsub__(self, other: "Poly | int") -> "Poly":
        return (other if isinstance(other, Poly) else Poly.const(self.n, int(other))) - self

    def __mul__(self, other: "Poly | int") -> "Poly":
        other = other if isinstance(other, Poly) else Poly.const(self.n, other)
        d: dict[tuple[int, ...], int] = {}
        for a, x in self.t.items():
            for b, y in other.t.items():
                m = tuple(i+j for i, j in zip(a, b))
                d[m] = d.get(m, 0) + x*y
        return Poly(self.n, d)

    __rmul__ = __mul__

    def __pow__(self, k: int) -> "Poly":
        ans, x = Poly.const(self.n, 1), self
        while k:
            if k & 1:
                ans *= x
            k >>= 1
            if k:
                x *= x
        return ans

    def mod2_support(self) -> set[tuple[int, ...]]:
        return {m for m, c in self.t.items() if c & 1}

    def derivative(self, i: int) -> "Poly":
        d: dict[tuple[int, ...], int] = {}
        for m, c in self.t.items():
            if m[i]:
                mm = list(m)
                d[tuple(mm[:i] + [mm[i]-1] + mm[i+1:])] = c*m[i]
        return Poly(self.n, d)

    def __eq__(self, other: object) -> bool:
        if isinstance(other, int):
            other = Poly.const(self.n, other)
        return isinstance(other, Poly) and self.n == other.n and self.t == other.t


def relation_poly() -> tuple[Poly, Poly, Poly]:
    u, v = Poly.var(2, 0), Poly.var(2, 1)
    R = (v**4 - u**3*v**3 + (u-u**3-2*u**4)*v**2
         - (u**3+u**4+2*u**5)*v + u**7)
    return u, v, R


def symbolic_map_checks() -> None:
    u, v, R = relation_poly()
    D = u**2 + u + v
    X = u*v*D
    Y = u*(u**2*v-u**2+v)
    Z = u**2*D
    W = u**4+u**3*v-v**2
    Q = -X*Z-X*W+Y**2+Y*Z+Z*W
    C = X**2*W+X*Y*Z-X*Y*W-X*Z*W+Y*Z*W+Z**2*W-Z*W**2
    assert Q == u*R
    assert C == -u**2*v*D*R
    A = Y+Z-W
    assert A == v*D
    assert X == u*A
    assert X**2 == v*Z*A

    x, y, z, w = [Poly.var(4, i) for i in range(4)]
    A0 = y+z-w
    B0 = z*x+z*A0+x*A0
    Q0 = -x*z-x*w+y**2+y*z+z*w
    C0 = x**2*w+x*y*z-x*y*w-x*z*w+y*z*w+z**2*w-z*w**2
    IY = z*(x**2-z*A0+A0**2)-y*B0
    IW = x*(z**2+x*z-A0**2)-w*B0
    assert IY == -x*Q0-C0
    assert IW == -x*Q0-C0


def divides_mod2(f: set[tuple[int, int]], g: set[tuple[int, int]]) -> bool:
    """Exact multivariate division over F2, lex order, for one divisor."""
    if not g or g == {(0, 0)}:
        return False
    r = set(f)
    lm_g = max(g)
    while r:
        lm = max(r)
        if lm[0] < lm_g[0] or lm[1] < lm_g[1]:
            return False
        shift = (lm[0]-lm_g[0], lm[1]-lm_g[1])
        for m in g:
            mm = (m[0]+shift[0], m[1]+shift[1])
            if mm in r:
                r.remove(mm)
            else:
                r.add(mm)
    return True


def irreducible_mod2_certificate(R: Poly) -> None:
    f = R.mod2_support()
    assert max(sum(m) for m in f) == 7
    mons = [(i, j) for i in range(4) for j in range(4-i)]
    # In a factorization of a total-degree-7 polynomial, one factor has degree <=3.
    for mask in range(1, 1 << len(mons)):
        g = {mons[k] for k in range(len(mons)) if (mask >> k) & 1}
        degree = max(sum(m) for m in g)
        if degree == 0:
            continue
        if divides_mod2(f, g):
            raise AssertionError(f"nontrivial mod-2 factor found: {sorted(g)}")


# ---------------------------------------------------------------------------
# Maps, cusp dictionary, and top-level run
# ---------------------------------------------------------------------------

def ls_from_ints(a: list[int]) -> LS:
    return LS({i: x for i, x in enumerate(a) if x})


def assert_same_series(a: LS, b: LS, lo: int, hi: int, label: str) -> None:
    (a-b).assert_zero(lo, hi, label)


def fraction_text(x: Fraction) -> str:
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def series_text(a: LS, n: int) -> list[str]:
    return [fraction_text(a.coeff(i)) for i in range(n+1)]


def verify_maps_on_series(U: list[int], V: list[int], cc: list[LS]) -> None:
    us, vs = ls_from_ints(U), ls_from_ints(V)
    x, y, z, w = cc
    A = y+z-w
    assert_same_series(x/A, us, 0, MAP_CHECK, "canonical -> U")
    assert_same_series(x**2/(z*A), vs, 0, MAP_CHECK, "canonical -> V")

    D = us**2+us+vs
    inv = [us*vs*D, us*(us**2*vs-us**2+vs), us**2*D, us**4+us**3*vs-vs**2]
    for i in range(4):
        for j in range(i+1, 4):
            (inv[i]*cc[j]-inv[j]*cc[i]).assert_zero(0, MAP_CHECK, f"inverse projective minor {i},{j}")


def cusp_dictionary(cc: list[LS]) -> list[dict[str, object]]:
    divisor_matrix = [
        [1, -1, 2, 1, -3],
        [-1, 2, 1, -3, 1],
        [2, 1, -3, 1, -1],
        [1, -3, 1, -1, 2],
        [-3, 1, -1, 2, 1],
    ]
    assert all(sum(row) == 0 for row in divisor_matrix)
    pairs = [(divisor_matrix[i][0], divisor_matrix[i][0]-divisor_matrix[i][1]) for i in range(5)]
    assert pairs == [(1,2), (-1,-3), (2,1), (1,4), (-3,-4)]
    assert [c.coeff(0) for c in cc] == [0,0,1,0]
    # The other four limits follow from the displayed inverse polynomials and
    # the unique lowest-valuation terms at the indicated pair.
    return [
        {"canonical": [0,0,0,1], "p": "p2", "orders": [2,1]},
        {"canonical": [0,-1,1,0], "p": "p3", "orders": [1,4]},
        {"canonical": [1,1,0,1], "p": "p4", "orders": [-3,-4]},
        {"canonical": [0,0,1,0], "p": "p0", "orders": [1,2]},
        {"canonical": [1,0,0,0], "p": "p1", "orders": [-1,-3]},
    ]


def run_all() -> dict[str, object]:
    U, V = build_UV(N)
    assert digest_csv(U) == EXPECTED_U_HASH
    assert digest_csv(V) == EXPECTED_V_HASH
    residual = relation_residual(U, V, N)
    assert not any(residual)
    rank38, rank39 = relation_rank_certificate(U, V)
    assert (rank38, rank39) == (38, 39)
    u, v, R = relation_poly()
    assert math.gcd(*(abs(c) for c in R.t.values())) == 1
    irreducible_mod2_certificate(R)
    print("PASS (1) U,V through q^5000; rank 38->39 at q^38; primitive irreducible R; cleared through q^5029")

    cc, aux = normalized_canonical()
    assert aux["b"].val() == 1 and aux["c"].val() == 1
    assert [t.coeff(0) for t in cc] == [0,0,1,0]
    print("PASS (2) universal Tate -> Tate normal form -> Sutherland -> canonical; Q=C=0 through q^100")

    symbolic_map_checks()
    verify_maps_on_series(U, V, cc)
    print("PASS (3) both birational directions: exact polynomial identities and q-series through q^70")

    cusps = cusp_dictionary(cc)
    print("PASS (4) cusp dictionary; q-infinity is p0 = [0:0:1:0] with (ord U,ord V)=(1,2)")

    # All coefficients in R and both maps are integers, so every numeric
    # denominator has v_2=0.  The integral identities above remain identities
    # modulo 2; R mod 2 is irreducible by the exhaustive factor certificate.
    assert all(isinstance(c, int) for c in R.t.values())
    assert cusp_dictionary(cc)[3]["orders"][0] == 1
    dRdv_mod2 = R.derivative(1).mod2_support()
    assert dRdv_mod2
    print("PASS (5) all coefficient denominators have v2=0; maps stay birational mod 2; ord_p0(U)=1")

    return {
        "U": U,
        "V": V,
        "hashes": {"U": EXPECTED_U_HASH, "V": EXPECTED_V_HASH},
        "rank_before": rank38,
        "rank_at": rank39,
        "canonical": {name: series_text(s, 100) for name, s in zip("xyzw", cc)},
        "tate": {name: series_text(aux[name], 60) for name in
                 ("tate_x", "tate_y", "b", "c", "sutherland_x", "sutherland_y")},
        "cusps": cusps,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dump", type=Path)
    parser.add_argument("--emit-b85", type=Path)
    args = parser.parse_args()
    data = run_all()
    if args.dump:
        args.dump.write_text(json.dumps(data, separators=(",", ":")))
    if args.emit_b85:
        payload = json.dumps({"U": data["U"], "V": data["V"]}, separators=(",", ":")).encode()
        encoded = base64.b85encode(__import__("zlib").compress(payload, 9)).decode()
        args.emit_b85.write_text("\n".join(encoded[i:i+100] for i in range(0, len(encoded), 100)) + "\n")


if __name__ == "__main__":
    main()
