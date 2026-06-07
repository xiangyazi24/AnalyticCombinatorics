[BRIDGE_WARNING] Likely truncated capture. The server rejected this text 4 times as intro-only or short (reasons: long_task_short_answer; last elapsed: 363s); the extension force-finalized at the kickback cap. The full ChatGPT answer is likely still visible in the browser tab — paste the actual reply back manually if you need the complete response.

---

The obstruction you found is real. With exactly inputs (1)–(5), there is no valid record-percolation argument proving hhigh/hlow. Those hypotheses are compatible with bounded, positive, nonconvergent “slow oscillations” that look constant on every $O(\sqrt n)$-window.
Here is the clean countermodel.
Let, for small $0<a<1$,


$$u_n=1+aA(n)\sin(\log\log(n+e^e)),$$


where $A(n)\uparrow 1$ very slowly, say $A(n)=1-1/\log\log(n+e^{e^2})$. Then


$$1-a\le u_n\le 1+a,$$


so (3) holds, and $u_n$ has infinitely many new running maxima near $1+a$ and intervening troughs near $1-a$. Thus hhigh is false for any $\varepsilon<2a$.
Now define


$$b(n):=u(n)-\sum_{m=1}^{n-1} W(n,m)u(n-m).$$


Then recurrence (1) holds tautologically. For the actual partition kernel, the mass is asymptotically concentrated on $m=O(\sqrt n)$, hence $m/n\to 0$ in kernel probability. Since the above $u_n$ is slowly varying under relative perturbations $m=o(n)$,


$$u(n-m)-u(n)\to 0$$


uniformly on the kernel mass. Therefore


$$b(n)
=
u(n)\Bigl(1-\sum_m W(n,m)\Bigr)
+
\sum_m W(n,m)\bigl(u(n)-u(n-m)\bigr)
\to 0,$$


using (2) and kernel tightness. Also (4) holds, because for every fixed $h$,


$$\sup_{0\le r\le h\sqrt n}|u(n+r)-u(n)|\to 0.$$


And (5) is a property of $W$, independent of $u$. So this nonconvergent $u$ satisfies the listed package, yet hhigh/hlow fail.
The failed step is exactly this one:


$$u(N)\text{ near record}
\quad\Longrightarrow\quad
\exists m\asymp \sqrt N:\ u(N-m)\ge u(N)-o(1).$$


That is true locally, but it only pulls the record back by $O(\sqrt N)$. A sequence may drift by $o(1)$ on every such window and still oscillate by $O(1)$ over a much larger scale, e.g. $\log\log n$. The “record reset” does not remove this unless the per-pullback error is summable on the $\sqrt n$-scale.
So the Lean lemma you want cannot have assumptions only (1)–(5). You need an extra input of roughly this form:


$$E(n):=
|b(n)|+M\left|\sum_m W(n,m)-1\right|+\text{kernel tail errors}$$


must satisfy a summability condition in the variable $t=\sqrt n$, for example


$$\sum_{j\ge J}
\sup_{j^2\le n<(j+1)^2} E(n)
\longrightarrow 0
\quad\text{as }J\to\infty.$$


For the genuine partition recurrence this is plausible/true because


$$b(n)=\sigma(n)e^{-C\sqrt n}$$


is exponentially small, and the mass defect is $O(1/n)=O(1/t^2)$, which is summable in $t$. But mere $b(n)\to0$ is far too weak.
A correct formalization route should therefore replace the intended hhigh/hlow lemma by a stronger-defect version:
Record pullback with summable defect.
If $N$ is a tail running maximum and a window $I_N=(a\sqrt N,b\sqrt N]$ has mass at least $\mu$, then


$$\max_{m\in I_N} u(N-m)
\ge
u(N)-\frac{E(N)}{\mu}.$$


The proof is just averaging: if every $u(N-m)$ in the window were below $u(N)-\eta$, the recurrence would give


$$u(N)
\le
u(N)\sum_m W(N,m)-\mu\eta+b(N)+\text{tail error},$$


hence $\eta\le E(N)/\mu$.
Then the pullback errors are not fixed $\varepsilon$-losses; they are $E(N_j)/\mu$, and along a chain


$$N_{j+1}=N_j-\Theta(\sqrt{N_j})$$


their total is controlled by the $\sqrt n$-scale summability. That is the missing “reset”: the record comparison is reset at each true running record, but the only quantity allowed to accumulate is the summable defect, not the forward-fill $\varepsilon$.
So the answer is: there is no percolation proof from (1)–(5) alone. The Lean theorem needs one more hypothesis, essentially a summable defect/rate estimate for $b(n)$ and the kernel approximation. Mere local forward fill plus positive window mass cannot rule out slow oscillations.

The crux is that “some near-max predecessor” plus one-step forward fill does not imply full tail cover. I’ll separate the honest obstruction from the strengthened lemma that actually makes the record method work.

There is no correct record-cover argument from (1)–(5) alone. The obstruction you found is not a technical gap; it is a genuine logical gap. The listed hypotheses only give a one-step pullback. They do not give the global hhigh/hlow cover unless you add a quantitative, summable error estimate.
The exact one-step fact is this.
Let


$$S_N=\sum_{m=1}^{N-1}W(N,m),
\qquad
I_N=(a_0\sqrt N,b_0\sqrt N],
\qquad
A_N=\sum_{m\in I_N}W(N,m).$$


Assume $N$ is a running maximum on $[N_0,N]$, so $u(k)\le u(N)$ for $N_0\le k\le N$. For $N$ large enough that $N-m\ge N_0$ on $I_N$, if every $m\in I_N$ satisfied


$$u(N-m)<u(N)-\eta,$$


then, using nonnegativity of $W$,


$$\begin{aligned}
u(N)
&=\sum_m W(N,m)u(N-m)+b(N) \\
&\le A_N(u(N)-\eta)+(S_N-A_N)u(N)+|b(N)| \\
&=S_Nu(N)-A_N\eta+|b(N)|.
\end{aligned}$$


Hence


$$A_N\eta
\le (S_N-1)u(N)+|b(N)|
\le M|S_N-1|+|b(N)|.$$


Using $A_N\ge \mu$, we get


$$\exists m\in I_N:\quad
u(N-m)\ge u(N)-\Delta_N,$$


where


$$\Delta_N
=
\frac{M|S_N-1|+|b(N)|}{\mu}.$$


This uses exactly (1), (2), (3), (5). It does not use forward fill.
The symmetric minimum version is:
if $N$ is a running minimum on $[N_0,N]$, then


$$\exists m\in I_N:\quad
u(N-m)\le u(N)+\Delta_N.$$


The proof is the same inequality reversed:


$$u(N)
\ge A_N(u(N)+\eta)+(S_N-A_N)u(N)-|b(N)|
=S_Nu(N)+A_N\eta-|b(N)|.$$


So


$$A_N\eta
\le (1-S_N)u(N)+|b(N)|
\le M|S_N-1|+|b(N)|.$$


That is the honest record-pullback lemma.
But this is only a single predecessor statement. It does not imply


$$u(N)-\varepsilon\le u(k)
\quad\text{for all }k\in[N_0,N].$$


The reason is that the loss $\Delta_N$ is paid each time you pull back. If you form a chain


$$N=N_0^{*}>N_1^{*}>N_2^{*}>\cdots$$


with


$$N_{j+1}^{*}=N_j^{*}-\Theta(\sqrt{N_j^{*}}),$$


then after $J$ pullbacks the available lower bound is only


$$u(N_J^{*})
\ge
u(N)-\sum_{j<J}\Delta_{N_j^{*}}.$$


There is no reset of the $\varepsilon$-budget unless the pullback is exact. The running-record property resets the upper comparison level, but it does not reset the accumulated numerical loss.
Forward fill helps only locally. If


$$u(n)-\theta\le u(n+r)
\qquad
0\le r\le h\sqrt n,$$


then a high predecessor $y=N-m$ with $m\le h\sqrt y$ covers the interval $[y,N]$ at one additional cost $\theta$. That cost is paid once for points in that interval. But the pullback losses used to create the chain still accumulate:


$$u(k)
\ge
u(N)
-
\theta
-
\sum_j \Delta_{N_j^{*}}.$$


Thus forward fill removes the local fill accumulation, but not the record-pullback accumulation.
So to make this route work, you need a stronger quantitative hypothesis, not merely $b(n)\to0$. A sufficient form is a summability condition on the defect in the variable $t=\sqrt n$. For example, define


$$E(n)=M|S_n-1|+|b(n)|+\text{tail/prefix error}.$$


You need something like


$$\sum_{j\ge J}
\sup_{j^2\le n<(j+1)^2} E(n)
\longrightarrow 0
\qquad (J\to\infty).$$


Then, after choosing a small window $I_n=(a\sqrt n,b\sqrt n]$ with $b<h$, the pullback loss is


$$\Delta_n=\frac{E(n)}{\mu},$$


and along a backward chain,


$$\sum_j \Delta_{N_j^{*}}$$


can be made $<\varepsilon$ by taking the starting scale large enough. That is the only sense in which the budget “resets”: the fixed forward-fill cost is paid once per covered interval, while the remaining pullback defects are summable on the $\sqrt n$-scale.
For the actual partition recurrence this extra input is natural because


$$b(n)=\sigma(n)e^{-C\sqrt n}$$


is exponentially small, and


$$|S_n-1|=O(1/n).$$


Since $1/n\sim 1/t^2$ with $t=\sqrt n$, this is summable over unit $t$-blocks. But the statement $b(n)\to0$ is far too weak.
Indeed, (1)–(5) are compatible with bounded nonconvergent slow oscillations. Take, for small $a>0$,


$$u(n)=1+aA(n)\sin(\log\log(n+e^e)),$$


with $A(n)\uparrow1$ very slowly. Then $u$ is bounded above and below, and it is nearly constant on every $O(\sqrt n)$-window:


$$u(n+r)-u(n)\to0
\qquad
(r=O(\sqrt n)).$$


If one defines


$$b(n)=u(n)-\sum_{m=1}^{n-1}W(n,m)u(n-m),$$


then the kernel concentration on $m=O(\sqrt n)$ gives $b(n)\to0$. Conditions (1), (3), (4), (5) hold, and (2) is a property of $W$. But $u(n)$ does not converge, and hhigh/hlow fail.
So the correct conclusion is:


$$\boxed{
\text{From (1)–(5) alone, } hhigh/hlow \text{ are not derivable.}
}$$


The formal Lean route should add a quantitative summable-defect hypothesis, or prove the concrete stronger estimates for the actual partition $b(n)=\sigma(n)e^{-C\sqrt n}$ and the mass defect. Then the record-pullback argument can be made honest; without that, the $\varepsilon$-loss cannot be prevented from accumulating over wide windows.