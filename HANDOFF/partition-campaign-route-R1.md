The best route is not to lower-bound $p(n)$ directly from $P(x)$. Formalize a small logarithmic Tauberian theorem for cumulative coefficients, then use monotonicity of $p(n)$. This keeps the whole proof real-variable and avoids eta/modular/circle-method machinery. The full Hardy–Ramanujan equivalent is stronger, but the sharp log-asymptotic target is exactly


$$\frac{\log p(n)}{\sqrt n}\to \pi\sqrt{\frac23}.$$


The full asymptotic $p(n)\sim e^{\pi\sqrt{2n/3}}/(4n\sqrt3)$ is the classical Hardy–Ramanujan result, while Erdős-style elementary methods give the logarithmic constant without the circle method; Nathanson’s paper explicitly describes this Erdős elementary route for partition-type functions. Wikipedia+1

0. Constants and definitions
Use
noncomputable def part (n : ℕ) : ℝ :=
  (Fintype.card (Nat.Partition n) : ℝ)

noncomputable def A : ℝ := Real.pi ^ 2 / 6

noncomputable def C : ℝ := 2 * Real.sqrt A
-- later prove C = Real.pi * Real.sqrt (2 / 3)

noncomputable def PartLaplace (t : ℝ) : ℝ :=
  ∑' n : ℕ, part n * Real.exp (-(t * n))

noncomputable def PartCum (N : ℕ) : ℝ :=
  ∑ n in Finset.range (N + 1), part n

Main theorem:
theorem partition_log_asymptotic :
  Tendsto
    (fun n : ℕ => Real.log (part n) / Real.sqrt (n : ℝ))
    atTop
    (𝓝 (Real.pi * Real.sqrt (2 / 3))) := ...

I would prove first:
theorem partition_cum_log_asymptotic :
  Tendsto
    (fun n : ℕ => Real.log (PartCum n) / Real.sqrt (n : ℝ))
    atTop
    (𝓝 (2 * Real.sqrt A)) := ...

Then transfer to part n by monotonicity.

1. Elementary upper bound: the clean formal version of (a)
For $0<x<1$,


$$P(x)=\sum_{n\ge0}p(n)x^n=\prod_{k\ge1}\frac1{1-x^k}.$$


Then


$$\log P(x)
= \sum_{j\ge1}\frac{x^j}{j(1-x^j)}
\le \frac{x}{1-x}\sum_{j\ge1}\frac1{j^2}
= A\frac{x}{1-x}.$$


The key inequality is


$$1-x^j=(1-x)(1+x+\cdots+x^{j-1})
\ge (1-x)\, j x^{j-1},$$


hence


$$\frac{x^j}{1-x^j}\le \frac{x}{j(1-x)}.$$


So for every $n$,


$$p(n)x^n\le P(x)
\quad\Rightarrow\quad
\log p(n)\le -n\log x + A\frac{x}{1-x}.$$


Set


$$y=\frac{x}{1-x},\qquad x=\frac{y}{1+y}.$$


Then


$$-\log x=\log(1+1/y)\le 1/y.$$


Choose


$$y=\sqrt{\frac nA},\qquad
x_n=\frac{\sqrt n}{\sqrt n+\sqrt A}.$$


Then


$$\log p(n)\le Ay+\frac n y
=2\sqrt{An}
=\pi\sqrt{\frac{2n}{3}}.$$


Lean lemma statements:
theorem partition_log_product_bound
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Real.log (∑' n : ℕ, part n * x ^ n)
      ≤ A * x / (1 - x) := ...

theorem partition_upper_exp_bound
    (n : ℕ) :
    part n ≤ Real.exp (Real.pi * Real.sqrt (2 * n / 3)) := ...

or, cleaner in real constants:
theorem partition_log_upper
    (n : ℕ) :
    Real.log (part n) ≤ 2 * Real.sqrt (A * n) := ...

This upper bound is one of the easiest bounded subgoals.

2. The real-analytic input: $t\log P(e^{-t})\to \pi^2/6$
Do not use Dedekind eta. Use the double-series expansion.
For $t>0$,


$$\log P(e^{-t})
= \sum_{k\ge1}-\log(1-e^{-tk})
= \sum_{k\ge1}\sum_{j\ge1}\frac{e^{-tjk}}{j}.$$


Interchange the nonnegative sums:


$$\log P(e^{-t})
= \sum_{j\ge1}\frac1j \frac{e^{-tj}}{1-e^{-tj}}
= \sum_{j\ge1}\frac1{j(e^{tj}-1)}.$$


Hence


$$t\log P(e^{-t})
= \sum_{j\ge1}\frac{t}{j(e^{tj}-1)}.$$


For fixed $j$,


$$\frac{t}{j(e^{tj}-1)}\to \frac1{j^2}.$$


And since $e^u-1\ge u$,


$$0\le \frac{t}{j(e^{tj}-1)}\le \frac1{j^2}.$$


So by dominated convergence for series,


$$t\log P(e^{-t})\to \sum_{j\ge1}\frac1{j^2}
=\frac{\pi^2}{6}=A.$$


Lean statements:
theorem partition_laplace_log_eq_series
    {t : ℝ} (ht : 0 < t) :
    Real.log (PartLaplace t)
      =
    ∑' j : ℕ+, 1 / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1)) := ...

theorem partition_laplace_log_asymptotic :
  Tendsto
    (fun t : ℝ => t * Real.log (PartLaplace t))
    (𝓝[>] 0)
    (𝓝 A) := ...

The finite-tail version avoids needing a heavy dominated-convergence theorem:
theorem exp_partition_term_bound
    {t : ℝ} (ht : 0 < t) (j : ℕ+) :
    0 ≤ t / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1))
    ∧
    t / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1))
      ≤ 1 / (j : ℝ)^2 := ...

theorem exp_partition_term_tendsto
    (j : ℕ+) :
    Tendsto
      (fun t : ℝ =>
        t / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1)))
      (𝓝[>] 0)
      (𝓝 (1 / (j : ℝ)^2)) := ...

Then do epsilon-tail splitting against
∑' j : ℕ+, 1 / (j : ℝ)^2 = Real.pi ^ 2 / 6

or whatever Basel theorem name exists in your environment.

3. The right lower-bound extraction: cumulative Tauberian theorem
The clean theorem to formalize is:
theorem log_tauberian_cumulative_sqrt
    (a : ℕ → ℝ)
    (ha_nonneg : ∀ n, 0 ≤ a n)
    (K : ℝ) (hK : 0 < K)
    (F : ℝ → ℝ)
    (hF_def : ∀ t > 0, F t = ∑' n : ℕ, a n * Real.exp (-(t * n)))
    (hF_asymp :
      Tendsto (fun t : ℝ => t * Real.log (F t)) (𝓝[>] 0) (𝓝 K)) :
    Tendsto
      (fun N : ℕ =>
        Real.log (∑ n in Finset.range (N + 1), a n)
          / Real.sqrt (N : ℝ))
      atTop
      (𝓝 (2 * Real.sqrt K)) := ...

Apply with a n = part n and K = A.
The proof has two halves.
3.1 Upper half
Let


$$S_N=\sum_{m\le N}a_m.$$


For $t>0$,


$$S_N e^{-tN}
\le \sum_{m\le N}a_m e^{-tm}
\le F(t).$$


Thus


$$\log S_N\le tN+\log F(t).$$


Given $\varepsilon>0$, for small $t$,


$$\log F(t)\le \frac{K+\varepsilon}{t}.$$


Choose


$$t=\sqrt{\frac{K+\varepsilon}{N}}.$$


Then


$$\log S_N\le 2\sqrt{(K+\varepsilon)N}.$$


Lean lemma:
theorem tauberian_cum_limsup
    ... :
    Filter.limsup
      (fun N : ℕ =>
        Real.log (Cum a N) / Real.sqrt (N : ℝ))
      atTop
      ≤ 2 * Real.sqrt K := ...

where
noncomputable def Cum (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n in Finset.range (N + 1), a n

3.2 Lower half: the non-handwavy part
Use Abel summation:


$$F(t)
=(1-e^{-t})\sum_{N\ge0}S_N e^{-tN}.$$


Lean statement:
theorem laplace_eq_abel_cum
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    {t : ℝ} (ht : 0 < t) :
    (∑' n : ℕ, a n * Real.exp (-(t * n)))
      =
    (1 - Real.exp (-t))
      * ∑' N : ℕ, Cum a N * Real.exp (-(t * N)) := ...

Now prove a localization lemma. Let $K>0$. If


$$\log F(t)\sim K/t,$$


then for every small $\varepsilon,\delta>0$, for all sufficiently small $t$, there exists an integer $N_t$ with


$$(1-\delta)\frac K{t^2}\le N_t\le (1+\delta)\frac K{t^2}$$


and


$$\log S_{N_t}\ge (2\sqrt K-\varepsilon)\sqrt{N_t}.$$


Lean statement:
theorem tauberian_exists_large_cum_near_saddle
    (a : ℕ → ℝ)
    (ha_nonneg : ∀ n, 0 ≤ a n)
    (K : ℝ) (hK : 0 < K)
    (hF_asymp :
      Tendsto (fun t : ℝ => t * Real.log (F t)) (𝓝[>] 0) (𝓝 K))
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ t in 𝓝[>] 0,
      ∃ N : ℕ,
        (1 - δ) * K / t^2 ≤ N ∧
        (N : ℝ) ≤ (1 + δ) * K / t^2 ∧
        (2 * Real.sqrt K - ε) * Real.sqrt (N : ℝ)
          ≤ Real.log (Cum a N) := ...

Proof idea: suppose no such $N$ exists in the saddle window. From the upper half we already have, for every $\eta>0$,


$$S_N\le \exp((2\sqrt K+\eta)\sqrt N)$$


eventually. Then in Abel’s formula split the sum into:


$$N\in I_t
=
\left[(1-\delta)K/t^2,\,(1+\delta)K/t^2\right],$$


and its complement.
Inside $I_t$, the bad assumption gives


$$S_N\le \exp((2\sqrt K-\varepsilon)\sqrt N).$$


The exponent


$$(2\sqrt K-\varepsilon)\sqrt N-tN$$


has maximum


$$\frac{(2\sqrt K-\varepsilon)^2}{4t}
<
\frac Kt.$$


Outside $I_t$, the global upper bound gives


$$S_N\le \exp((2\sqrt K+\eta)\sqrt N),$$


but the normalized exponent


$$(2\sqrt K+\eta)\sqrt N-tN$$


is strictly below $K/t$ away from the saddle $N=K/t^2$, provided $\eta$ is chosen small relative to $\delta$.
Thus Abel’s formula implies


$$F(t)\le \exp((K-\rho)/t)$$


for some $\rho>0$, contradicting


$$\log F(t)\ge (K-\rho/2)/t.$$


The analytic estimate to isolate as an independent task is:
theorem sqrt_laplace_restricted_gap
    {K B δ : ℝ}
    (hK : 0 < K)
    (hδ : 0 < δ)
    (hB : B < 2 * Real.sqrt K + small δ K) :
    ∃ ρ > 0,
      ∀ᶠ t in 𝓝[>] 0,
        (1 - Real.exp (-t))
          *
        (∑' N : ℕ,
          if (1 - δ) * K / t^2 ≤ (N : ℝ)
             ∧ (N : ℝ) ≤ (1 + δ) * K / t^2
          then 0
          else Real.exp (B * Real.sqrt (N : ℝ) - t * N))
        ≤ Real.exp ((K - ρ) / t) := ...

And the inside-window bad-bound estimate:
theorem sqrt_laplace_bad_inside_gap
    {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) :
    ∃ ρ > 0,
      ∀ᶠ t in 𝓝[>] 0,
        (1 - Real.exp (-t))
          *
        (∑' N : ℕ,
          Real.exp ((2 * Real.sqrt K - ε)
                    * Real.sqrt (N : ℝ) - t * N))
        ≤ Real.exp ((K - ρ) / t) := ...

These are pure real-analysis lemmas about sums of


$$\exp(B\sqrt N-tN).$$


Your existing sum-integral comparison infrastructure should be enough.
Finally, convert the local lower bound into all $N$. Given large $M$, choose


$$t=\sqrt{\frac{(1+\delta)K}{M}}.$$


Then the upper end of the saddle window is $\le M$, while the lower end is


$$\frac{1-\delta}{1+\delta}M.$$


So there exists $N_t\le M$ with $N_t\ge rM$, where


$$r=\frac{1-\delta}{1+\delta}.$$


Since $S_N$ is monotone,


$$S_M\ge S_{N_t}
\ge \exp((2\sqrt K-\varepsilon)\sqrt{N_t})
\ge \exp((2\sqrt K-\varepsilon)\sqrt r\,\sqrt M).$$


Let $\delta,\varepsilon\to0$. This gives


$$\liminf_{M\to\infty}\frac{\log S_M}{\sqrt M}\ge 2\sqrt K.$$



4. Transfer from cumulative partitions to $p(n)$
This is the clean answer to the “$p(n)\ge\cdots$” issue.
You do not extract $p(n)$ directly from $P(x)$. You prove the sharp asymptotic for


$$S_N=\sum_{m\le N}p(m).$$


Then use monotonicity:


$$p(N)\le S_N\le (N+1)p(N).$$


Therefore


$$\log p(N)
\le \log S_N
\le \log p(N)+\log(N+1).$$


Since


$$\frac{\log(N+1)}{\sqrt N}\to0,$$


the two logarithmic ratios have the same limit.
Lean statements:
theorem partition_card_mono :
  Monotone part := ...

Proof: inject Nat.Partition n → Nat.Partition (n+1) by adding one part of size 1.
Generalized:
theorem partition_card_mono_of_le {m n : ℕ} (h : m ≤ n) :
  part m ≤ part n := ...

Then:
theorem partition_cum_le :
  PartCum n ≤ (n + 1 : ℝ) * part n := ...

theorem partition_le_cum :
  part n ≤ PartCum n := ...

theorem partition_log_same_as_cum :
  Tendsto
    (fun n : ℕ =>
      (Real.log (PartCum n) - Real.log (part n))
        / Real.sqrt (n : ℝ))
    atTop
    (𝓝 0) := ...

Then final:
theorem partition_log_asymptotic :
  Tendsto
    (fun n : ℕ => Real.log (part n) / Real.sqrt (n : ℝ))
    atTop
    (𝓝 (Real.pi * Real.sqrt (2 / 3))) := ...

using
theorem two_sqrt_A_eq_partition_constant :
  2 * Real.sqrt (Real.pi ^ 2 / 6)
    = Real.pi * Real.sqrt (2 / 3) := ...


5. Recommended campaign ordering
I would split the project into these milestones.
Milestone A: sharp upper bound
Formalize:
theorem partition_log_upper :
  Real.log (part n) ≤ 2 * Real.sqrt (A * n)

This already gives the clean elementary inequality


$$p(n)\le e^{\pi\sqrt{2n/3}}.$$


Milestone B: Laplace asymptotic
Formalize:
theorem partition_laplace_log_asymptotic :
  Tendsto
    (fun t : ℝ => t * Real.log (PartLaplace t))
    (𝓝[>] 0)
    (𝓝 A)

The crucial sublemma is the dominated finite-tail proof for


$$\sum_{j\ge1}\frac{t}{j(e^{tj}-1)}
\to
\sum_{j\ge1}\frac1{j^2}.$$


Milestone C: general Tauberian theorem
Prove the general theorem for arbitrary nonnegative a : ℕ → ℝ.
This is reusable across analytic combinatorics, not just partitions.
Milestone D: cumulative-to-coefficient transfer
Prove monotonicity of Nat.Partition card and transfer


$$\log S_n\sim C\sqrt n
\quad\Rightarrow\quad
\log p(n)\sim C\sqrt n.$$



6. Hardest Lean step and fallback
The hardest step will be the restricted saddle-window estimate for


$$(1-e^{-t})\sum_N \exp(B\sqrt N-tN).$$


Everything else is routine real analysis, formal power series evaluation, positivity, or monotonicity.
The key fallback is:
theorem partition_log_upper_and_weak_lower :
  ∃ c > 0,
    (∀ᶠ n in atTop,
      c * Real.sqrt (n : ℝ) ≤ Real.log (part n))
    ∧
    (∀ n,
      Real.log (part n) ≤ Real.pi * Real.sqrt (2 * n / 3)) := ...

A very easy lower bound uses distinct parts. Subsets of {1,2,...,m} give $2^m$ distinct-part partitions with total size at most $m(m+1)/2$. Hence for $m\sim\sqrt{2n}$,


$$p(n)\ge \frac{2^m}{n+1},$$


so


$$\liminf \frac{\log p(n)}{\sqrt n}
\ge \sqrt2\log 2.$$


This is much weaker than $\pi\sqrt{2/3}$, but it gives a robust first lower-bound theorem while the Tauberian localization is still under construction.
The optimal final route is therefore:


$$\boxed{
\log P(e^{-t})\sim \frac{\pi^2}{6t}
\quad\Longrightarrow\quad
\log\sum_{m\le n}p(m)\sim \pi\sqrt{\frac{2n}{3}}
\quad\Longrightarrow\quad
\log p(n)\sim \pi\sqrt{\frac{2n}{3}}.
}$$


That middle implication, as a reusable logarithmic Tauberian lemma, is the central formalization asset.