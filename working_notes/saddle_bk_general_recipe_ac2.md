[intro]
I’ll align the sign convention with the existing saddle files first, then give the reusable operator formula and the two validations.

[answer]
Let

\[
D:=r\frac{d}{dr}.
\]

For

\[
f(z)=\exp(g(z)),\qquad a(r):=Dg(r)=r g'(r),
\]

the saddle equation is

\[
a(r)=r g'(r)=n.
\]

Near \(\theta=0\),

\[
g(re^{i\theta})-n\log(re^{i\theta})
=
g(r)-n\log r+\sum_{k\ge2}\frac{D^k g(r)}{k!}(i\theta)^k.
\]

The linear term cancels because \(Dg(r)=n\). Therefore, with your convention

\[
\phi(\theta)=\phi(0)-\frac{b}{2}\theta^2+\sum_{k\ge3}\frac{b_k}{k!}(i\theta)^k,
\]

the universal formula is simply

\[
\boxed{b=b_2=D^2g(r),\qquad b_k=D^kg(r)\quad(k\ge3).}
\]

This sign convention matches the current saddle core: `saddleThirdPoly` uses the second-order polynomial plus the \(+i b_5\) quintic, \(-b_6\) sextic, and the corresponding third correction. fileciteturn28file0 g(r)=\sum_{j=1}^k {k\brace j} r^j g^{(j)}(r),
\]

where \({k\brace j}\) are Stirling numbers of the second kind:

\[
\boxed{
b_2
=
r g'(r)+r^2g''(r)
}
\]

\[
\boxed{
b_3
=
r g'(r)+3r^2g''(r)+r^3g^{(3)}(r)
}
\]

\[
\boxed{
b_4
=
r g'(r)+7r^2g''(r)+6r^3g^{(3)}(r)+r^4g^{(4)}(r)
}
\]

\[
\boxed{
b_5
=
r g'(r)+15r^2g''(r)+25r^3g^{(3)}(r)+10r^4g^{(4)}(r)+r^5g^{(5)}(r)
}
\]

\[
\boxed{
b_6
=
r g'(r)+31r^2g''(r)+90r^3g^{(3)}(r)+65r^4g^{(4)}(r)+15r^5g^{(5)}(r)+r^6g^{(6)}(r)
}
\]

Lean-transcribable style:

```lean id="w30k9w"
def saddleB2 (g1 g2 r : ℝ) : ℝ :=
  r * g1 + r^2 * g2

def saddleB3 (g1 g2 g3 r : ℝ) : ℝ :=
  r * g1 + 3 * r^2 * g2 + r^3 * g3

def saddleB4 (g1 g2 g3 g4 r : ℝ) : ℝ :=
  r * g1 + 7 * r^2 * g2 + 6 * r^3 * g3 + r^4 * g4

def saddleB5 (g1 g2 g3 g4 g5 r : ℝ) : ℝ :=
  r * g1 + 15 * r^2 * g2 + 25 * r^3 * g3
    + 10 * r^4 * g4 + r^5 * g5

def saddleB6 (g1 g2 g3 g4 g5 g6 r : ℝ) : ℝ :=
  r * g1 + 31 * r^2 * g2 + 90 * r^3 * g3
    + 65 * r^4 * g4 + 15 * r^5 * g5 + r^6 * g6
```

Here `gj` means \(g^{(j)}(r)\).

## Validation: involutions, \(g(z)=z+z^2/2\)

For

\[
g(z)=z+\frac{z^2}{2},
\]

we have

\[
g'(r)=1+r,\qquad g''(r)=1,\qquad g^{(j)}(r)=0\quad(j\ge3).
\]

Therefore

\[
D^kg(r)=D^k r + \frac12D^k r^2
=
r+\frac12 2^k r^2
=
\boxed{r+2^{k-1}r^2}.
\]

So for every \(k\ge2\),

\[
\boxed{b_k=r+2^{k-1}r^2.}
\]

In particular:

\[
b_2=r+2r^2,\quad
b_3=r+4r^2,\quad
b_4=r+8r^2,\quad
b_5=r+16r^2,\quad
b_6=r+32r^2.
\]

This is exactly the known involution formula.

## Bell numbers: \(g(z)=e^z-1\)

For

\[
g(z)=e^z-1,
\]

all positive derivatives are

\[
g^{(j)}(r)=e^r.
\]

Thus

\[
b_k=e^r\sum_{j=1}^k {k\brace j}r^j.
\]

With saddle equation

\[
r e^r=n,
\]

the explicit formulas are:

\[
\boxed{
b_2=e^r(r+r^2)=n(1+r)
}
\]

\[
\boxed{
b_3=e^r(r+3r^2+r^3)=n(1+3r+r^2)
}
\]

\[
\boxed{
b_4=e^r(r+7r^2+6r^3+r^4)
=n(1+7r+6r^2+r^3)
}
\]

\[
\boxed{
b_5=e^r(r+15r^2+25r^3+10r^4+r^5)
=n(1+15r+25r^2+10r^3+r^4)
}
\]

\[
\boxed{
b_6=e^r(r+31r^2+90r^3+65r^4+15r^5+r^6)
=n(1+31r+90r^2+65r^3+15r^4+r^5)
}
\]

For Lean, the most reusable abstraction is:

```lean id="fbnpha"
-- conceptual
b_k r = (D^[k] g) r
where D h r = r * deriv h r
```

and for concrete instances avoid Stirling infrastructure by proving the five explicit formulas above as instance lemmas.
