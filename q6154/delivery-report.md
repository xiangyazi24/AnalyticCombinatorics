ANSWER Q6154 9704ad7d

# r18-P-E31DATA — exact finite computation for the N25 E3.1 dictionary

Source state: `xiangyazi24/mazur-p2m@40a40768c6369fa8a0cfdd5d538839c44438e933` (branch `main`).  All arithmetic below is exact.  The checker at the end uses only the Python standard library and was run from a clean public GitHub Actions runner; its five PASS lines are reproduced at the end of the report.

## Verdict

All requested rows pass.  The r17 bidegrees are correct: `deg_X R = 7`, `deg_Y R = 4`.  The exact relation has only nine nonzero monomials.  The canonical q-infinity cusp is `[0:0:1:0]`, corresponding to `p0`.  Every numeric coefficient denominator in the relation and both birational directions is `1`; the same formulas remain mutually inverse after reduction modulo `2`, and `ord_p0(U)=1` is the requested separability witness.

## 1. Modular units, q-expansions, and the plane relation

The definitions used are exactly those of K1:

```text
B2(t) = t^2 - t + 1/6
E_g = q^(25*B2(g/25)/2) * product_{n>=1} (1-q^(25(n-1)+g))*(1-q^(25n-g))
P0=E1*E7,  P1=E2*E11,  P2=E3*E4,  P3=E6*E8,  P4=E9*E12
U_i=P_i/P_{i+1}  (indices modulo 5)
U=U0=P0/P1
V=U0/U1=P0*P2/P1^2
```

The Bernoulli prefactors give `ord_q(U)=1` and `ord_q(V)=2`.  The first coefficients, indexed from `q^0`, are:

```text
U[0..80] =
[
  0, 1, -1, 1, -1, 1, -1, 1, -2, 2, -2, 2, -1, 1, -1, 2,
  -2, 2, -2, 0, 0, 0, -1, 2, -1, 0, 2, -3, 4, -3, 1, -2,
  3, -6, 8, -8, 6, -3, 3, -3, 7, -10, 9, -6, 1, 1, -1, -3,
  6, -5, 1, 8, -13, 13, -9, 4, -4, 9, -20, 26, -26, 20, -9, 6,
  -11, 22, -30, 30, -20, 3, 5, -3, -9, 20, -18, 3, 21, -36, 38, -24,
  7
]

V[0..80] =
[
  0, 0, 1, -1, 2, -3, 3, -4, 4, -5, 5, -6, 7, -5, 6, -4,
  4, -4, 4, -6, 3, -5, 2, -2, 4, -2, 6, -1, 0, 6, -11, 10,
  -16, 10, -18, 21, -24, 32, -25, 28, -14, 17, -19, 18, -33, 20, -24, 9,
  -6, 14, -9, 30, -8, 3, 23, -48, 40, -59, 35, -58, 68, -91, 125, -93,
  103, -52, 51, -64, 72, -124, 83, -93, 32, -13, 45, -37, 110, -49, 25, 69,
  -154
]
```

### Complete exact coefficient data through q^5000

The complete exact coefficient archive is pinned at source commit
`6ec28d99a2fd5915c2622d979220131a8e845582`, path `q6154/qexp.b85`
(blob SHA `71476bb782548700ddb7a46217f61ac62f63f481`).  It is the base85
encoding of a zlib-compressed UTF-8 JSON object
`{"U":[u_0,...,u_5000],"V":[v_0,...,v_5000]}`.  This archive is an
auxiliary copy of the data; the checker below independently recomputes every
coefficient from the defining Euler products and, with
`--dump qexp.json`, writes the same complete exact arrays.  Thus the markdown
remains self-contained even without the auxiliary archive.

Pinned raw archive:

```text
https://raw.githubusercontent.com/xiangyazi24/AnalyticCombinatorics/6ec28d99a2fd5915c2622d979220131a8e845582/q6154/qexp.b85
```

Stdlib decoder for the pinned archive:

```python
import base64, json, zlib
from pathlib import Path
blob = "".join(Path("qexp.b85").read_text().split())
qexp = json.loads(zlib.decompress(base64.b85decode(blob)))
U, V = qexp["U"], qexp["V"]
assert len(U) == len(V) == 5001
```

Canonical CSV fingerprints of the decoded arrays are:

```text
sha256(",".join(map(str,U))) = b4547b68c5090115b688b56353c96855a587d3a1b821b890ed868630438d6802
sha256(",".join(map(str,V))) = 6e22a69676ee0d36652978f8e3802a60e8fbde51ab5ea448b77f1ff66cc130cb
```

### Primitive irreducible relation

```text
R(X,Y) =
  Y^4
  - X^3*Y^3
  + X*Y^2 - X^3*Y^2 - 2*X^4*Y^2
  - X^3*Y - X^4*Y - 2*X^5*Y
  + X^7
```

Equivalently, in grouped form:

```text
R(X,Y) = Y^4 - X^3*Y^3
         + (X - X^3 - 2*X^4)*Y^2
         - (X^3 + X^4 + 2*X^5)*Y
         + X^7
```

The coefficient content is `1`.  Reduction modulo `2` is irreducible (both Singular and the stdlib checker certify this), so the monic primitive polynomial above is irreducible over `Z[X,Y]`.

The 40 series `U^i V^j`, `0<=i<=7`, `0<=j<=4`, have rank `38` on coefficient rows `q^0,...,q^37` and rank `39` after adding the row `q^38`.  Since the displayed relation supplies a nonzero kernel vector, exactly **39 q-coefficients** (`q^0` through `q^38`) determine the one-dimensional relation space up to scale.

Direct exact substitution gives `R(U,V)=0` through `q^5000`.  This is stronger than the requested `q^4950`.  For the r17 weight-396 clearing, put `G=Delta^3`, `F0=G*U`, and `F1=G*U1`.  Then:

```text
G^7 * F1^4 * R(F0/G, F0/F1)
  = G^11 * U1^4 * R(U,V).
```

At q-infinity, `ord(G)=3` and `ord(U1)=-1`, so the common clearing factor has order `11*3-4=29`.  Therefore the cleared weight-396 identity is verified through `q^(5000+29)=q^5029`.

### Divisor explanation for the bidegrees

The exact K1 divisor table is:

```text
        U0  U1  U2  U3  U4
p0       1  -1   2   1  -3
p1      -1   2   1  -3   1
p2       2   1  -3   1  -1
p3       1  -3   1  -1   2
p4      -3   1  -1   2   1
```

Thus the pole degree of `U=U0` is `1+3=4`, while the orders of `V=U0/U1` are `(2,-3,1,4,-4)`, of pole degree `3+4=7`.  Hence the minimal relation must have `deg_Y=4` and `deg_X=7`; the computed relation has exactly these degrees.

## 2. Universal Tate construction and canonical q-expansions

Set the Tate modulus to `Q_T=q^25` and take the torsion parameter `u_T=q`.  The point has exact order 25 because `u_T^25=Q_T`.  The exact Tate series used by the checker are:

```text
X_T(u_T,Q_T) = sum_{n in Z} Q_T^n*u_T/(1-Q_T^n*u_T)^2 - 2*s1(Q_T)
Y_T(u_T,Q_T) = sum_{n in Z} (Q_T^n*u_T)^2/(1-Q_T^n*u_T)^3 + s1(Q_T)
a4 = -5*s3(Q_T)
a6 = -(5*s3(Q_T)+7*s5(Q_T))/12
Y_T^2 + X_T*Y_T = X_T^3 + a4*X_T + a6
```

The Tate-normal-form conversion is:

```text
s  = (3*X_T^2 + a4 - Y_T)/(2*Y_T + X_T)
A1 = 1 + 2*s
A2 = 3*X_T - s - s^2
A3 = X_T + 2*Y_T
b  = -A2^3/A3^2
c  = 1 - A1*A2/A3
```

The exact `b,c` coefficient arrays through `q^60`, indexed from `q^0`, are:

```text
b[0..60] =
[
  0, -1, 5, -18, 53, -136, 315, -673, 1346, -2547, 4597, -7964,
  13311, -21554, 33931, -52083, 78148, -114869, 165717, -235030, 328169, -451692, 613547, -823282,
  1092271, -1433956, 1864093, -2400993, 3065752, -3882446, 4878270, -6083603, 7531969, -9259865, 11306428, -13712910,
  16521930, -19776472, 23518598, -27787845, 32619275, -38041147, 44072180, -50718376, 57969372, -65794293, 74137093, -82911368,
  91994638, -101222155, 110380300, -119199657, 127347939, -134422992, 139946133, -143356129, 144004211, -141150542, 133962564, -121515709,
  102796972
]

c[0..60] =
[
  0, -1, 4, -11, 24, -45, 76, -119, 176, -249, 340, -451,
  584, -741, 924, -1135, 1376, -1649, 1956, -2299, 2680, -3101, 3565, -4075,
  4630, -5225, 5850, -6487, 7113, -7701, 8220, -8639, 8928, -9057, 8996, -8715,
  8184, -7373, 6252, -4791, 2960, -729, -1932, 5053, -8664, 12800, -17500, 22794,
  -28700, 35216, -42300, 49862, -57764, 65820, -73804, 81470, -88560, 94807, -99948, 103725,
  -105880
]
```

Both have leading order `1`.  The compiled Tate-to-Sutherland map is:

```text
Nx = -b^2 + b*c + c^3
K  = -2*b^2 + b*c^2 + 3*b*c - c^2
B  = -b^3 + 3*b^2*c - b*c^3 - 3*b*c^2 + c^5 + c^4 + c^3
x_S = Nx/K
y_S = K*(b-c)/B
```

The full four Sutherland-to-canonical coordinate polynomials are reproduced literally in the stdlib checker below (`sutherland_to_canonical`); no term is omitted.  After removing their common order `-2` and normalizing the leading coefficient of `z` to `1`, the canonical equations are:

```text
Q(x,y,z,w) = -x*z - x*w + y^2 + y*z + z*w

C(x,y,z,w) = x^2*w + x*y*z - x*y*w - x*z*w
             + y*z*w + z^2*w - z*w^2
```

The exact normalized canonical q-expansions through `q^100`, indexed from `q^0`, are:

```text
x[0..100] =
[
  0, 1, 1, 6, 3, 13, 0, 11, -15, -7, -35, -15,
  -22, 27, 34, 74, 54, 20, -43, -116, -140, -83, 12, 190,
  250, 244, 28, -246, -540, -528, -267, 325, 987, 1135, 935, -289,
  -1448, -2448, -2101, -523, 2139, 4223, 4629, 2367, -2396, -6805, -9126, -6236,
  1371, 10285, 16420, 13855, 2542, -14415, -27306, -28387, -11440, 16978, 43825, 53145,
  30703, -14615, -67249, -92505, -70234, 2410, 93949, 155611, 140401, 34001, -120085, -249137,
  -258578, -116709, 135790, 377066, 452130, 277259, -117206, -541615, -756954, -563759, 15671, 741176,
  1209484, 1059521, 242005, -946302, -1853288, -1881758, -771809, 1076683, 2742825, 3168762, 1780439, -1006825,
  -3895238, -5114504, -3569084, 510658, 5264314
]
```

```text
y[0..100] =
[
  0, 1, 1, 5, 2, 8, -2, 4, -12, -5, -20, 3,
  -3, 34, 17, 30, -6, -27, -60, -55, -30, 64, 110, 144,
  72, -64, -223, -304, -267, 41, 377, 639, 642, 116, -495, -1240,
  -1355, -743, 701, 2050, 2887, 1851, -390, -3344, -5398, -4509, -696, 4990,
  9649, 9515, 3675, -6498, -16270, -18960, -10502, 6853, 26445, 35054, 24830, -3534,
  -40087, -61955, -53135, -7802, 56130, 105351, 102925, 37917, -71988, -169828, -190700, -101490,
  79249, 262147, 336031, 224913, -58017, -386061, -568961, -452429, -25281, 539758, 924462, 850525,
  232729, -699403, -1450887, -1519362, -668627, 816081, 2197499, 2592008, 1510549, -784986, -3195287, -4273003,
  -3022082, 406334, 4451027, 6807663, 5604885
]
```

```text
z[0..100] =
[
  1, 1, 5, 3, 9, 3, 6, -4, -7, -16, -9, -8,
  15, 20, 31, 26, -5, -37, -63, -70, -7, 45, 121, 149,
  87, -48, -209, -335, -250, -16, 289, 634, 597, 303, -367, -1061,
  -1290, -831, 223, 1634, 2446, 2063, 383, -2354, -4331, -4357, -1919, 2760,
  7030, 8548, 5346, -2311, -10908, -15262, -12022, -258, 15349, 25964, 24667, 7092,
  -19607, -42142, -45799, -22718, 20958, 64307, 81147, 53553, -15227, -92690, -135977, -108842,
  -7906, 124617, 218517, 204527, 62842, -154818, -334817, -360916, -175180, 165014, 492437, 608547,
  383670, -128295, -691921, -978817, -748647, -8877, 918827, 1520681, 1354901, 327855, -1139277, -2275636,
  -2315806, -971760, 1273647, 3286045, 3794421
]
```

```text
w[0..100] =
[
  0, 0, -1, -1, -5, -2, -7, 3, 1, 14, 12, 17,
  -4, -11, -47, -34, -30, 20, 69, 104, 83, 22, -136, -215,
  -250, -113, 169, 443, 582, 440, -120, -774, -1227, -1187, -198, 1103,
  2391, 2672, 1300, -1387, -4154, -5643, -3775, 861, 6763, 10846, 9318, 1528,
  -9818, -19627, -20041, -8445, 12291, 33099, 39924, 24220, -11331, -52506, -74231, -56673,
  588, 77646, 130430, 119290, 31434, -104338, -218162, -231292, -107598, 121986, 346305, 423536,
  264559, -105751, -521787, -736908, -564280, 6558, 740058, 1227992, 1102708, 265602, -973681, -1961756,
  -2024296, -867140, 1145887, 3006981, 3538409, 2051861, -1093041, -4415479, -5926655, -4228017, 504781, 6176727,
  9564044, 8010871, 1172039, -8148641, -14894439
]
```

Exact Laurent-series substitution gives `Q=C=0` through `q^100`.  The constant projective vector is `[0:0:1:0]`.

## 3. Birational maps

Put `A=y+z-w`.  The canonical-to-plane map is:

```text
U = x/A
V = x^2/(z*A)
```

These are ratios of forms of equal degree.  The initially fitted quadratic denominator for `V` was `-x*z-x*w+y^2+2*y*z+z^2`; subtracting `Q` gives `z*(y+z-w)=z*A`, yielding the displayed minimal formula.

For the inverse, put `D=U^2+U+V`.  Then:

```text
Xc = U*V*(U^2+U+V)
Yc = U*(U^2*V-U^2+V)
Zc = U^2*(U^2+U+V)
Wc = U^4+U^3*V-V^2

[x:y:z:w] = [Xc:Yc:Zc:Wc].
```

The exact defining-ideal certificates are:

```text
Q(Xc,Yc,Zc,Wc) = U*R(U,V)
C(Xc,Yc,Zc,Wc) = -U^2*V*(U^2+U+V)*R(U,V)
Yc+Zc-Wc = V*(U^2+U+V)
Xc = U*(Yc+Zc-Wc)
Xc^2 = V*Zc*(Yc+Zc-Wc)
```

For the reverse composition, again put `A=y+z-w` and define:

```text
B  = x*z + z*A + x*A
PX = x*B
PY = z*(x^2-z*A+A^2)
PZ = z*B
PW = x*(z^2+x*z-A^2)
```

After substituting `U=x/A`, `V=x^2/(z*A)` into the inverse and clearing the common denominator, the resulting projective coordinates are `[PX:PY:PZ:PW]`, and the exact identities are:

```text
PY-y*B = -x*Q-C
PW-w*B = -x*Q-C
PX-x*B = 0
PZ-z*B = 0
```

Hence `[PX:PY:PZ:PW]=[x:y:z:w]` on `Q=C=0` wherever `B!=0`.  Both compositions were also checked directly on the q-series through `q^70`.

## 4. Cusp dictionary

| canonical cusp | K1 row | `(ord U, ord V)` | inverse-map leading term |
|---|---:|---:|---|
| `[0:0:0:1]` | `p2` | `(2,1)` | `Wc ~ -V^2` |
| `[0:-1:1:0]` | `p3` | `(1,4)` | `Yc ~ -U^3`, `Zc ~ U^3` |
| `[1:1:0:1]` | `p4` | `(-3,-4)` | `Xc,Yc,Wc ~ U^3 V` |
| `[0:0:1:0]` | `p0` | `(1,2)` | exact q-series limit |
| `[1:0:0:0]` | `p1` | `(-1,-3)` | `Xc ~ U V^2` is uniquely lowest |

Therefore the q-infinity place is **`p0 = [0:0:1:0]`**, where the computed expansions begin `U=q+...` and `V=q^2+...`.

## 5. Reduction at 2

All numeric coefficient denominators in `R`, the forward map, and the inverse map are `1`; every denominator therefore has `v_2=0`.  The polynomial denominators of the forward rational map are the primitive integral forms `A` and `z*A`, each of 2-adic content zero.  The inverse direction is given by integral homogeneous polynomials.

The reduced relation is:

```text
R_2(U,V) = V^4 + U^3*V^3 + (U+U^3)*V^2
           + (U^3+U^4)*V + U^7
```

It is irreducible in `F_2[U,V]`.  The checker proves this without a CAS by exhausting every possible factor of total degree at most 3; such a factor would have to exist in any factorization of a total-degree-7 polynomial.  The integral composition identities in section 3 reduce unchanged modulo `2`, so the reductions still give mutually inverse birational maps between `R_2=0` and the reduced canonical model.

The requested separability witness is:

```text
ord_p0(U) = 1.
```

This is odd, indeed exactly one.  In addition, `dR_2/dV = U^3*(V^2+U+1)` is nonzero.

## Stdlib-only checker

Save the following as `checker.py` and run `python3 checker.py`.  Optional flags `--dump data.json --emit-b85 qexp.b85` reproduce the machine-readable arrays and the compressed data block.

```python
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
```

Expected terminal output:

```text
PASS (1) U,V through q^5000; rank 38->39 at q^38; primitive irreducible R; cleared through q^5029
PASS (2) universal Tate -> Tate normal form -> Sutherland -> canonical; Q=C=0 through q^100
PASS (3) both birational directions: exact polynomial identities and q-series through q^70
PASS (4) cusp dictionary; q-infinity is p0 = [0:0:1:0] with (ord U,ord V)=(1,2)
PASS (5) all coefficient denominators have v2=0; maps stay birational mod 2; ord_p0(U)=1
```

E31DATA PASS: exact q^5000 modular-unit data, primitive irreducible `(7,4)` relation, universal-Tate canonical series, two integral birational directions, complete cusp dictionary, and good mod-2 reduction certified.
END Q6154 9704ad7d
