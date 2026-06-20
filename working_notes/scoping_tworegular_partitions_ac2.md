I’ll align the sign convention with the existing saddle files first, then give the reusable operator formula and the two validations.

Let


$$D:=r\frac{d}{dr}.$$


For


$$f(z)=\exp(g(z)),\qquad a(r):=Dg(r)=r g'(r),$$


the saddle equation is


$$a(r)=r g'(r)=n.$$


Near $\theta=0$,


$$g(re^{i\theta})-n\log(re^{i\theta})
=
g(r)-n\log r+\sum_{k\ge2}\frac{D^k g(r)}{k!}(i\theta)^k.$$


The linear term cancels because $Dg(r)=n$. Therefore, with your convention


$$\phi(\theta)=\phi(0)-\frac{b}{2}\theta^2+\sum_{k\ge3}\frac{b_k}{k!}(i\theta)^k,$$


the universal formula is simply


$$\boxed{b=b_2=D^2g(r),\qquad b_k=D^kg(r)\quad(k\ge3).}$$


This sign convention matches the current saddle core: saddleThirdPoly uses the second-order polynomial plus the $+i b_5$ quintic, $-b_6$ sextic, and the corresponding third correction.
Explicit formulas through $b_6$
Using


$$D^k g(r)=\sum_{j=1}^k {k\brace j} r^j g^{(j)}(r),$$


where ${k\brace j}$ are Stirling numbers of the second kind:


$$\boxed{
b_2
=
r g'(r)+r^2g''(r)
}$$




$$\boxed{
b_3
=
r g'(r)+3r^2g''(r)+r^3g^{(3)}(r)
}$$




$$\boxed{
b_4
=
r g'(r)+7r^2g''(r)+6r^3g^{(3)}(r)+r^4g^{(4)}(r)
}$$




$$\boxed{
b_5
=
r g'(r)+15r^2g''(r)+25r^3g^{(3)}(r)+10r^4g^{(4)}(r)+r^5g^{(5)}(r)
}$$




$$\boxed{
b_6
=
r g'(r)+31r^2g''(r)+90r^3g^{(3)}(r)+65r^4g^{(4)}(r)+15r^5g^{(5)}(r)+r^6g^{(6)}(r)
}$$


Lean-transcribable style:
leandef saddleB2 (g1 g2 r : ℝ) : ℝ :=  r * g1 + r^2 * g2def saddleB3 (g1 g2 g3 r : ℝ) : ℝ :=  r * g1 + 3 * r^2 * g2 + r^3 * g3def saddleB4 (g1 g2 g3 g4 r : ℝ) : ℝ :=  r * g1 + 7 * r^2 * g2 + 6 * r^3 * g3 + r^4 * g4def saddleB5 (g1 g2 g3 g4 g5 r : ℝ) : ℝ :=  r * g1 + 15 * r^2 * g2 + 25 * r^3 * g3    + 10 * r^4 * g4 + r^5 * g5def saddleB6 (g1 g2 g3 g4 g5 g6 r : ℝ) : ℝ :=  r * g1 + 31 * r^2 * g2 + 90 * r^3 * g3    + 65 * r^4 * g4 + 15 * r^5 * g5 + r^6 * g6
Here gj means $g^{(j)}(r)$.
Validation: involutions, $g(z)=z+z^2/2$
For


$$g(z)=z+\frac{z^2}{2},$$


we have


$$g'(r)=1+r,\qquad g''(r)=1,\qquad g^{(j)}(r)=0\quad(j\ge3).$$


Therefore


$$D^kg(r)=D^k r + \frac12D^k r^2
=
r+\frac12 2^k r^2
=
\boxed{r+2^{k-1}r^2}.$$


So for every $k\ge2$,


$$\boxed{b_k=r+2^{k-1}r^2.}$$


In particular:


$$b_2=r+2r^2,\quad
b_3=r+4r^2,\quad
b_4=r+8r^2,\quad
b_5=r+16r^2,\quad
b_6=r+32r^2.$$


This is exactly the known involution formula.
Bell numbers: $g(z)=e^z-1$
For


$$g(z)=e^z-1,$$


all positive derivatives are


$$g^{(j)}(r)=e^r.$$


Thus


$$b_k=e^r\sum_{j=1}^k {k\brace j}r^j.$$


With saddle equation


$$r e^r=n,$$


the explicit formulas are:


$$\boxed{
b_2=e^r(r+r^2)=n(1+r)
}$$




$$\boxed{
b_3=e^r(r+3r^2+r^3)=n(1+3r+r^2)
}$$




$$\boxed{
b_4=e^r(r+7r^2+6r^3+r^4)
=n(1+7r+6r^2+r^3)
}$$




$$\boxed{
b_5=e^r(r+15r^2+25r^3+10r^4+r^5)
=n(1+15r+25r^2+10r^3+r^4)
}$$




$$\boxed{
b_6=e^r(r+31r^2+90r^3+65r^4+15r^5+r^6)
=n(1+31r+90r^2+65r^3+15r^4+r^5)
}$$


For Lean, the most reusable abstraction is:
lean-- conceptualb_k r = (D^[k] g) rwhere D h r = r * deriv h r
and for concrete instances avoid Stirling infrastructure by proving the five explicit formulas above as instance lemmas.

I’ll separate the singular exponent issue first, because it decides (A): $f=e^{-z/2-z^2/4}(1-z)^{-1/2}$ is a negative-half singularity, not the positive square-root class. Then I’ll pin the partition correction from Rademacher/eta-transform rather than treating it as an ordinary local saddle.

(A) Two-regular labelled graphs
There is a small but important exponent mismatch.
Your existing third-order square-root meta for


$$F(z)=A(z)+B(z)\sqrt{1-z/\rho}$$


handles a positive square-root singularity and gives powers


$$n^{-3/2},\;n^{-5/2},\;n^{-7/2}.$$


But


$$f(z)=\frac{e^{-z/2-z^2/4}}{\sqrt{1-z}}$$


has a negative square-root singularity:


$$f(z)=B(z)(1-z)^{-1/2},
\qquad
B(z)=e^{-z/2-z^2/4}.$$


So it is not a direct corollary of the positive-$\sqrt{\phantom{x}}$ meta-applicator. If you try to force it into $A+B\sqrt{1-z}$, you would need $B(z)=e^{-z/2-z^2/4}/(1-z)$, which is not analytic at $z=1$. The obstruction is only this exponent mismatch; mathematically it is a bounded bookkeeping task if you already have a general algebraic transfer or can clone the $\alpha=+1/2$ proof to $\alpha=-1/2$.
Use the sibling form


$$F(z)=A(z)+B(z)(1-z/\rho)^{-1/2}.$$


Here $\rho=1$, $A=0$, and


$$\boxed{B(z)=e^{-z/2-z^2/4}.}$$


Set $t=1-z$. Then


$$-z/2-z^2/4
=
-3/4+t-t^2/4,$$


so


$$B(1-t)=e^{-3/4}e^{t-t^2/4}
=
e^{-3/4}
\left(
1+t+\frac14t^2-\frac1{12}t^3-\frac5{96}t^4+\cdots
\right).$$


Thus


$$f(z)
=
e^{-3/4}
\left(
t^{-1/2}+t^{1/2}+\frac14t^{3/2}-\frac1{12}t^{5/2}+\cdots
\right).$$


Derivative data at $z=1$:


$$B(1)=e^{-3/4},\qquad
B'(1)=-e^{-3/4},\qquad
B''(1)=\frac12e^{-3/4},\qquad
B'''(1)=\frac12e^{-3/4}.$$


For three terms of the reciprocal-square-root transfer,


$$[z^n]f(z)
=
\frac{e^{-3/4}}{\sqrt{\pi}}
\left(
n^{-1/2}
-\frac58n^{-3/2}
+\frac1{128}n^{-5/2}
+O(n^{-7/2})
\right).$$


If you want one more term, using the $t^{5/2}$ term above,


$$[z^n]f(z)
=
\frac{e^{-3/4}}{\sqrt{\pi}}
\left(
n^{-1/2}
-\frac58n^{-3/2}
+\frac1{128}n^{-5/2}
+\frac{425}{1024}n^{-7/2}
+O(n^{-9/2})
\right).$$


For labelled 2-regular graphs, multiply by $n!$.
Lean scoping: this is a small new meta-applicator, not a new analytic campaign. Define invSqrtSingularityThirdOrder or, better, a general algebraicSingularityThirdOrder specialized to exponent $-1/2$. Your current third-order saddle core already uses explicit universal third-order polynomial/correction definitions, so the proof style is likely compatible with this kind of transfer-by-expansion bookkeeping.
(B) Integer partitions
This is not a bounded bookkeeping task of the same kind.
For


$$P(q)=\prod_{k\ge1}(1-q^k)^{-1},$$


the dominant $q\to1$ expansion gives the main exponential, but a rigorous coefficient theorem for $p(n)$ needs control of the rest of the unit circle. For ordinary partitions that control comes from the modular transformation of the Dedekind eta function and the Hardy–Ramanujan/Rademacher circle method. Rademacher’s formula is a convergent series whose $k=1$ term gives the whole polynomial asymptotic expansion, while $k\ge2$ terms are exponentially smaller. Wikipedia
The cleanest exact form uses the shifted variable


$$\nu=n-\frac1{24},
\qquad
\lambda=\pi\sqrt{\frac{2\nu}{3}}.$$


The $k=1$ Rademacher term gives


$$\boxed{
p(n)
=
\frac{e^\lambda}{4\sqrt3\,\nu}
\left(1-\frac1{\lambda}\right)
+
O(e^{\lambda/2})
}$$


up to exponentially smaller terms. More precisely, Rademacher’s full formula has a sum over $k$, and the $k$-th term is of order $\exp(\pi\sqrt{2n/3}/k)$, so all $k\ge2$ terms are exponentially smaller than the principal $k=1$ term. Wikipedia
So, in the shifted Rademacher variable $\lambda$, there is no long polynomial correction series:


$$\boxed{
\text{principal expansion} = 1-\lambda^{-1},
}$$


and the next errors are exponentially small, not powers of $\lambda^{-1}$.
If instead you insist on the unshifted Hardy–Ramanujan scale


$$\mu=\pi\sqrt{\frac{2n}{3}},
\qquad
\frac{e^\mu}{4n\sqrt3},$$


then the shift $n\mapsto n-\frac1{24}$ expands into an infinite $1/\mu$-series. From the principal Rademacher term,


$$p(n)
=
\frac{e^\mu}{4n\sqrt3}
\left[
1
-\left(1+\frac{\pi^2}{72}\right)\frac1\mu
+\left(\frac{\pi^2}{24}+\frac{\pi^4}{10368}\right)\frac1{\mu^2}
-\left(\frac{\pi^2}{24}+\frac{\pi^4}{1728}
+\frac{\pi^6}{2239488}\right)\frac1{\mu^3}
+O(\mu^{-4})
\right]
+
O(e^{\mu/2}).$$


The coefficients look less “universal” because $\pi^2$-terms are artifacts of using the unshifted $\mu$. In shifted form, the principal correction is just $1-1/\lambda$.
Lean scoping verdict:


If the target is formal asymptotics from the principal modular/Rademacher term, the algebra after Rademacher is small.


If the target is a rigorous theorem for $p(n)$ from the product GF, this is a separate large effort: you need eta modular transformation/circle-method or an already-proved Rademacher/Meinardus theorem with exponentially small minor-arc control. It is not comparable to plugging $B(1),B'(1),B''(1)$ into a singularity meta.


So: two-regular third order = small reciprocal-square-root transfer wrapper. Partition third order = only small after a major modular/circle-method theorem is already available.
