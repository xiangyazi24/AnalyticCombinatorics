[BRIDGE_WARNING] Likely truncated capture. The server rejected this text 4 times as intro-only or short (reasons: intro_preamble_short; last elapsed: 561s); the extension force-finalized at the kickback cap. The full ChatGPT answer is likely still visible in the browser tab — paste the actual reply back manually if you need the complete response.

---

Your budget analysis is right: Abel summation against the currently banked pointwise estimate


$$S(x)=\sum_{m\le x}\sigma(m)
=\frac{\pi^2}{12}x^2+O(x\log x)$$


only gives about


$$O\!\left(\frac{\log n}{\sqrt n}\right)$$


for kernelMass n - 1. It is not enough for the barriers or for the summable shell errors. The claimed $O(\log n/n)$ really needs a second-order smoothed divisor calculation and the cancellation of the $n^{-1/2}$ term.
The clean route is not to first prove a sharp ordinary summatory formula for Sigma.summatory. For the ordinary right-continuous summatory function, a pointwise secondary formula with o(x) error is not even the right object: Perron’s half-weighted summatory has the residue secondary term -x/2, but the ordinary summatory at integers differs from the half-weighted one by roughly sigmaR n / 2, which can be of order $n\log\log n$ along large values. Perron’s formula uses a half-weight convention at jumps, and the Dirichlet series of $\sigma_a$ is $\zeta(s)\zeta(s-a)$, giving the -x/2 residue for $a=1$, but that is a smoothed/half-weighted fact, not a usable ordinary S(x)=...+O(x^{2/3}) brick. (en.wikipedia.org)
So I would prove the rate through Lambert-series moment asymptotics, i.e. smoothed divisor sums. This gives exactly the needed secondary term and avoids endpoint-jump bookkeeping.

0. Target namespace and definitions
Use a separate file, say:
leanimport Mathlibimport AnalyticCombinatorics.Ch8.Partitions.ErdosKernelimport AnalyticCombinatorics.Ch8.Partitions.ErdosUniformimport AnalyticCombinatorics.Ch8.Partitions.ErdosKernelClose
Namespace:
leannamespace AnalyticCombinatorics.Ch8.Partitions.Erdos
Define the mass:
leannoncomputable def kernelMass (n : ℕ) : ℝ :=  ∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m
Define the Lambert moments:
leannoncomputable def sigmaMoment (r : ℕ) (t : ℝ) : ℝ :=  ∑' m : ℕ,    if m = 0 then 0    else (m : ℝ) ^ r * Sigma.sigmaR m * Real.exp (-t * (m : ℝ))
Define the saddle parameter:
leannoncomputable def massLam : ℝ := C / 2
Then prove:
leanlemma massLam_pos : 0 < massLam
and the key identity:
leanlemma massLam_sq :    massLam ^ 2 = Real.pi ^ 2 / 6
Proof sketch: unfold massLam, use C = π√(2/3) and Real.sq_sqrt.

1. Do not use ordinary refined summatory as the main brick
This is the first important correction.
1.1 Half-weighted summatory secondary term
If you want to record the classical statement, state it only for a half-weighted summatory:
leannoncomputable def Sigma.summatoryHalfWeighted (x : ℝ) : ℝ :=  ∑ m ∈ Finset.Icc 1 ⌊x⌋₊,    (if (m : ℝ) = x then (1 / 2 : ℝ) * Sigma.sigmaR m else Sigma.sigmaR m)
Classical analytic statement:
leantheorem Sigma.summatoryHalfWeighted_secondary :  ∃ K : ℝ, 0 < K ∧    ∀ x : ℝ, 2 ≤ x →      |Sigma.summatoryHalfWeighted x        - (Real.pi ^ 2 / 12) * x ^ 2        + (1 / 2 : ℝ) * x|        ≤ K * x ^ (3 / 4 : ℝ)   -- or whatever exponent you choose to prove
But I do not recommend this as the route. It is a Voronoi/Perron-type brick, not elementary in the same sense as your current real-variable stack.
1.2 Ordinary summatory cannot have a clean o(x) secondary
State this as a warning lemma if useful:
leantheorem Sigma.ordinary_summatory_secondary_not_pointwise_small :  ¬ ∃ E : ℝ → ℝ,      (Filter.Tendsto (fun x : ℝ => E x / x) Filter.atTop (𝓝 0)) ∧      ∀ n : ℕ,        Sigma.summatory (n : ℝ)          =        (Real.pi ^ 2 / 12) * (n : ℝ) ^ 2          - (1 / 2 : ℝ) * (n : ℝ)          + E n
Proof sketch: at integers, ordinary and half-weighted summatory differ by Sigma.sigmaR n / 2. Along large values of sigmaR n / n, this is not o(n). You probably do not need to formalize this; it is just to avoid bricking the wrong object.

2. Smoothed Lambert moment package
This is the right replacement for refined pointwise summatory.
Let


$$M_r(t)=\sum_{m\ge1}m^r\sigma(m)e^{-tm}.$$


You need moments r = 0,1,2 with two terms, and upper bounds for r = 3,4 to control Taylor remainders.

2.1 Lambert identity for M₀
leantheorem sigmaMoment_zero_lambert    {t : ℝ} (ht : 0 < t) :  sigmaMoment 0 t =    ∑' k : ℕ,      if k = 0 then 0      else        Real.exp (-t * (k : ℝ)) /          (1 - Real.exp (-t * (k : ℝ))) ^ 2
Proof sketch: use Sigma.sigmaR m = ∑_{d | m} d; rewrite m = d*k; use Tonelli for nonnegative terms:


$$\sum_m\sigma(m)e^{-tm}
=
\sum_{d,k\ge1}d e^{-tdk}
=
\sum_{k\ge1}\sum_{d\ge1}d(e^{-tk})^d
=
\sum_{k\ge1}\frac{e^{-tk}}{(1-e^{-tk})^2}.$$



2.2 Regularized Bose kernel
Define:
leannoncomputable def boseKernel (x : ℝ) : ℝ :=  Real.exp (-x) / (1 - Real.exp (-x)) ^ 2noncomputable def boseReg0 (x : ℝ) : ℝ :=  boseKernel x - 1 / x ^ 2
Near zero:


$$boseReg0(x)\to -\frac1{12}.$$


Integral:


$$\int_0^\infty \left(
\frac{e^{-x}}{(1-e^{-x})^2}-\frac1{x^2}
\right)\,dx=-\frac12.$$


Lean bricks:
leanlemma boseReg0_tendsto_zero :  Filter.Tendsto boseReg0 (𝓝[>] 0) (𝓝 (-(1 / 12 : ℝ)))
leanlemma boseReg0_integrable_Ioi :  IntegrableOn boseReg0 (Set.Ioi 0)
leanlemma integral_boseReg0_Ioi :  ∫ x in Set.Ioi 0, boseReg0 x = -(1 / 2 : ℝ)
Proof sketch: use


$$\frac{d}{dx}\left(\frac1{e^x-1}-\frac1x\right)
=
-\frac{e^x}{(e^x-1)^2}+\frac1{x^2}.$$


Since


$$\frac{e^{-x}}{(1-e^{-x})^2}
=
\frac{e^x}{(e^x-1)^2},$$


the integral telescopes from the endpoint limits. The endpoint at 0+ is -1/2; the endpoint at infinity is 0.

2.3 Euler-Maclaurin / trapezoid estimate for regularized kernels
You need a reusable real-variable lemma:
leantheorem eulerMaclaurin_step_sum_Ioi    {f : ℝ → ℝ}    (hf_int : IntegrableOn f (Set.Ioi 0))    (hf_var : HasBoundedVariationOn f (Set.Ioi 0))    (hf_zero : Filter.Tendsto f (𝓝[>] 0) (𝓝 f0))    (hf_inf : Filter.Tendsto f Filter.atTop (𝓝 0)) :  ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧    ∀ t : ℝ, 0 < t → t < δ →      |(∑' k : ℕ,          if k = 0 then 0 else f (t * (k : ℝ)))        - (1 / t) * ∫ x in Set.Ioi 0, f x        + (1 / 2) * f0|      ≤ K * t
For the boseReg0 case this yields:
leantheorem boseReg0_step_sum :  ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧    ∀ t : ℝ, 0 < t → t < δ →      |(∑' k : ℕ,          if k = 0 then 0 else boseReg0 (t * (k : ℝ)))        + (1 / (2 * t)) - (1 / 24 : ℝ)|      ≤ K * t
Proof sketch: this is the elementary trapezoidal-rule estimate for a function with integrable derivative or bounded variation. In Lean it is often easier to assume/prove IntegrableOn (deriv f) and use a one-cell estimate:


$$\left|
t\sum_{k\ge1}f(tk)-\int_0^\infty f
+\frac t2 f(0+)
\right|
\le C t^2.$$



2.4 Moment 0 asymptotic
leantheorem sigmaMoment_zero_asymp :  ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧    ∀ t : ℝ, 0 < t → t < δ →      |sigmaMoment 0 t        - ((Real.pi ^ 2 / 6) / t ^ 2            - (1 / 2 : ℝ) / t            + (1 / 24 : ℝ))|      ≤ K * t
Proof sketch:


$$M_0(t)
=
\sum_{k\ge1}\frac1{t^2k^2}
+
\sum_{k\ge1}boseReg0(tk)
=
\frac{\zeta(2)}{t^2}
-\frac1{2t}
+\frac1{24}
+O(t).$$


Use the already banked Basel value.

2.5 Moment 1 and 2 asymptotics
You can get these either by differentiating a sufficiently strong version of the M₀ expansion or by applying the same regularization to the derivative kernels. I recommend direct moment statements:
leantheorem sigmaMoment_one_asymp :  ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧    ∀ t : ℝ, 0 < t → t < δ →      |sigmaMoment 1 t        - (2 * (Real.pi ^ 2 / 6) / t ^ 3            - (1 / 2 : ℝ) / t ^ 2)|      ≤ K / t
leantheorem sigmaMoment_two_asymp :  ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧    ∀ t : ℝ, 0 < t → t < δ →      |sigmaMoment 2 t        - (6 * (Real.pi ^ 2 / 6) / t ^ 4            - 1 / t ^ 3)|      ≤ K / t ^ 2
Proof sketch: sigmaMoment 1 = - d/dt sigmaMoment 0, sigmaMoment 2 = d²/dt² sigmaMoment 0 at the exact series level. For formalization, prove exact differentiability of the Lambert series on t > 0 by dominated convergence on compact subintervals. Then differentiate the regularized Euler-Maclaurin formulas, or prove the analogous regularized step-sum estimates for


$$G_1(x)=-x\,boseKernel'(x),\qquad
G_2(x)=x^2\,boseKernel''(x)+x\,boseKernel'(x).$$


The displayed error sizes are more than enough.

2.6 Crude upper bounds for higher moments
leantheorem sigmaMoment_le_power    (r : ℕ) :  ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧    ∀ t : ℝ, 0 < t → t < δ →      sigmaMoment r t ≤ K / t ^ (r + 2)
You need this explicitly for r = 3 and r = 4.
Proof sketch: use the Lambert double sum:


$$M_r(t)
=
\sum_{d,k\ge1}d^{r+1}k^r e^{-tdk}.$$


For fixed k, compare the d-sum with an integral; then sum over k with 1/k². Equivalently, use the banked sigmaR m ≤ m² only for a weak bound, but that gives t^{-(r+3)} and is too weak for the final O(1/n). So use the divisor decomposition to get the sharp average order.

3. Kernel expansion on the main range
Set


$$\lambda=\frac C2,\qquad t_n=\lambda/\sqrt n.$$


For m ≤ n^(2/3):


$$\frac{e^{-C(\sqrt n-\sqrt{n-m})}}{n-m}
=
\frac{e^{-\lambda m/\sqrt n}}{n}
\left(
1+\frac mn-\frac{C m^2}{8n^{3/2}}
\right)
+
\text{remainder}.$$



3.1 Main-range cutoff
Use the cutoff


$$T_n=n^{2/3}.$$


In Lean avoid real powers where possible:
leandef mainRange (n m : ℕ) : Prop :=  (m : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ)
If rpow becomes annoying, replace by a natural cutoff
leandef T (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊
and use m ≤ T n.

3.2 Square-root drop expansion
leanlemma sqrt_drop_second_order    {n m : ℕ} (hn : 1 ≤ n)    (hm : (m : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ)) :  let s := Real.sqrt (n : ℝ)  let x := (m : ℝ) / (n : ℝ)  |(Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))    - ((m : ℝ) / (2 * s)       + (m : ℝ) ^ 2 / (8 * s ^ 3))|    ≤ Ksqrt * (m : ℝ) ^ 3 / s ^ 5
Proof sketch: write


$$\sqrt n-\sqrt{n-m}
=
\sqrt n\,(1-\sqrt{1-x}),
\qquad x=m/n.$$


For x ≤ n^{-1/3} eventually, use Taylor with explicit remainder:


$$1-\sqrt{1-x}
=
\frac x2+\frac{x^2}{8}+O(x^3).$$



3.3 Reciprocal expansion
leanlemma inv_sub_second_order    {n m : ℕ} (hn : 1 ≤ n)    (hm : (m : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ)) :  |1 / (((n - m : ℕ) : ℝ))    - (1 / (n : ℝ) + (m : ℝ) / (n : ℝ) ^ 2)|    ≤ Kinv * (m : ℝ) ^ 2 / (n : ℝ) ^ 3
Proof sketch: since m/n ≤ n^{-1/3}, eventually m ≤ n/2. Then


$$\frac1{n-m}
=
\frac1n\frac1{1-m/n}
=
\frac1n\left(1+\frac mn+O((m/n)^2)\right).$$



3.4 Exponential expansion
leanlemma exp_sqrt_drop_second_order    {n m : ℕ} (hn : 1 ≤ n)    (hm : (m : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ)) :  let s := Real.sqrt (n : ℝ)  |Real.exp (-C *      (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ)))    -    Real.exp (-(C / 2) * (m : ℝ) / s) *      (1 - C * (m : ℝ) ^ 2 / (8 * s ^ 3))|    ≤      Kexp *        Real.exp (-(C / 4) * (m : ℝ) / s) *        ((m : ℝ) ^ 3 / s ^ 5          + (m : ℝ) ^ 4 / s ^ 6)
Proof sketch: use Lemma 3.2 and


$$e^{-(a+\delta)}=e^{-a}(1-\delta+O(\delta^2))$$


with


$$a=\frac C2\frac m{\sqrt n},\qquad
\delta=\frac{C m^2}{8n^{3/2}}+O(m^3/n^{5/2}).$$


The weaker exponential exp(-(C/4)m/√n) absorbs all constants because δ=o(1) on the main range.

3.5 Combined coefficient expansion
This is the main local brick.
leanlemma erdosWeight_coef_second_order    {n m : ℕ} (hn : 1 ≤ n)    (hm1 : 1 ≤ m)    (hm : (m : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ)) :  let s := Real.sqrt (n : ℝ)  let e := Real.exp (-(C / 2) * (m : ℝ) / s)  |(1 / (((n - m : ℕ) : ℝ)) *      Real.exp (-C *        (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))))    -    (1 / (n : ℝ)) * e *      (1 + (m : ℝ) / (n : ℝ)         - C * (m : ℝ) ^ 2 / (8 * (n : ℝ) * s))|    ≤      Kcoef *        Real.exp (-(C / 4) * (m : ℝ) / s) *        ((m : ℝ) ^ 2 / (n : ℝ) ^ 3          + (m : ℝ) ^ 3 / ((n : ℝ) ^ 3 * s)          + (m : ℝ) ^ 4 / (n : ℝ) ^ 4)
The displayed correction is equivalent to


$$\frac{e^{-\lambda m/\sqrt n}}n
\left(1+\frac mn-\frac{C m^2}{8n^{3/2}}\right).$$


Proof sketch: multiply Lemma 3.3 and Lemma 3.4; keep only first-order cross terms; bound all products by the displayed moment-controlled error.

4. Tail cutoff
Use T_n = n^(2/3).
4.1 True kernel tail
leanlemma kernelMass_tail_mainRange_compl :  ∃ K c : ℝ, 0 < K ∧ 0 < c ∧    ∀ᶠ n : ℕ in Filter.atTop,      (∑ m ∈ Finset.Icc 1 (n - 1),        if (n : ℝ) ^ (2 / 3 : ℝ) < (m : ℝ)        then erdosWeight n m else 0)      ≤ K * (n : ℝ) ^ 3 *          Real.exp (-c * (n : ℝ) ^ (1 / 6 : ℝ))
Proof sketch: for all m ≤ n,


$$\sqrt n-\sqrt{n-m}\ge \frac{m}{2\sqrt n}.$$


If m > n^(2/3), the exponential is at most exp(-c n^(1/6)). Use Sigma.sigmaR m ≤ m² ≤ n², denominator n-m ≥ 1, and at most n terms.
This is far smaller than 1/n.

4.2 Model moment tails
For the expansion remainder you also need:
leanlemma sigmaMoment_tail_mainRange_compl    (r : ℕ) :  ∃ K c : ℝ, 0 < K ∧ 0 < c ∧    ∀ᶠ n : ℕ in Filter.atTop,      (∑ m ∈ Finset.Icc 1 (n - 1),        if (n : ℝ) ^ (2 / 3 : ℝ) < (m : ℝ)        then (m : ℝ) ^ r * Sigma.sigmaR m *          Real.exp (-(C / 4) * (m : ℝ) / Real.sqrt (n : ℝ))        else 0)      ≤ K * (n : ℝ) ^ (r + 3) *          Real.exp (-c * (n : ℝ) ^ (1 / 6 : ℝ))
Proof sketch: same exponential lower bound, with polynomial factor absorbed into n^(r+3).

5. Sum the local expansion
Define the second-order approximation:
leannoncomputable def kernelMassApprox2 (n : ℕ) : ℝ :=  let t := massLam / Real.sqrt (n : ℝ)  (1 / (n : ℝ)) * sigmaMoment 0 t  + (1 / (n : ℝ) ^ 2) * sigmaMoment 1 t  - (C / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ))) *      sigmaMoment 2 t
5.1 Kernel mass is close to the second-order approximation
leantheorem kernelMass_sub_approx2 :  ∃ K : ℝ, 0 < K ∧    ∀ᶠ n : ℕ in Filter.atTop,      |kernelMass n - kernelMassApprox2 n|        ≤ K / (n : ℝ)
Proof sketch:


Split at m ≤ n^(2/3) and its complement.


Tail is exponentially small by Lemma 4.1.


On the main range, use erdosWeight_coef_second_order.


The error terms reduce to moments:




$$\frac1{n^3}M_2(C/(4\sqrt n))
+
\frac1{n^3\sqrt n}M_3(C/(4\sqrt n))
+
\frac1{n^4}M_4(C/(4\sqrt n)).$$


Using M_r(t) ≤ K/t^(r+2) with t≈n^{-1/2} gives respectively:


$$O(n^{-1}),\quad O(n^{-1}),\quad O(n^{-1}).$$


So the total is O(1/n).

6. The cancellation in kernelMassApprox2
Let


$$Z=\frac{\pi^2}{6},\qquad \lambda=\frac C2.$$


Then


$$\lambda^2=Z.$$


Use the moment expansions at


$$t_n=\lambda/\sqrt n.$$


They are:


$$M_0(t)
=
Zt^{-2}-\frac12t^{-1}+O(1),$$




$$M_1(t)
=
2Zt^{-3}-\frac12t^{-2}+O(t^{-1}),$$




$$M_2(t)
=
6Zt^{-4}-t^{-3}+O(t^{-2}).$$


Plug into:


$$A_n
=
\frac1nM_0(t_n)
+\frac1{n^2}M_1(t_n)
-\frac{C}{8n^2\sqrt n}M_2(t_n).$$


The leading term:


$$\frac1n Zt_n^{-2}
=
\frac1n Z\frac n{\lambda^2}
=1.$$


The $n^{-1/2}$-terms are:


$$-\frac1{2\lambda\sqrt n}
+
\frac{2Z}{\lambda^3\sqrt n}
-
\frac{C}{8}\frac{6Z}{\lambda^4\sqrt n}.$$


Since C = 2λ and Z = λ², this is


$$-\frac1{2\lambda}
+
\frac2{\lambda}
-
\frac{3}{2\lambda}
=0.$$


This is the precise cancellation.
Lean brick:
leanlemma kernelMassApprox2_cancel_sqrt_term :  ∃ K : ℝ, 0 < K ∧    ∀ᶠ n : ℕ in Filter.atTop,      |kernelMassApprox2 n - 1| ≤ K / (n : ℝ)
Proof sketch: instantiate sigmaMoment_zero_asymp, sigmaMoment_one_asymp, and sigmaMoment_two_asymp at t = massLam / sqrt n. Use massLam_sq. The algebraic cancellation should be isolated:
leanlemma mass_rate_sqrt_coeff_cancel :  -(1 / (2 * massLam))    + 2 * (Real.pi ^ 2 / 6) / massLam ^ 3    - C * (6 * (Real.pi ^ 2 / 6)) / (8 * massLam ^ 4)    = 0
Proof: field_simp [massLam_pos.ne'], rewrite massLam = C/2 and massLam_sq = π²/6, then ring.

7. Final rate
Combine:
leantheorem kernelMass_sub_one_rate :  ∃ K : ℝ, 0 < K ∧    ∀ᶠ n : ℕ in Filter.atTop,      |kernelMass n - 1| ≤ K / (n : ℝ)
Proof sketch:


$$|K_n-1|
\le |K_n-A_n|+|A_n-1|
\le K_1/n+K_2/n.$$


Then weaken to the requested logarithmic rate:
leantheorem erdos_kernel_total_log_rate :  ∃ A : ℝ, 0 < A ∧    ∀ᶠ n : ℕ in Filter.atTop,      |kernelMass n - 1|        ≤ A * Real.log ((n : ℝ) + 3) / (n : ℝ)
Proof sketch: from kernelMass_sub_one_rate; eventually 1 ≤ Real.log ((n : ℝ) + 3). Take the same constant or double it.

8. How this answers your four points
(1) Refined divisor summatory
The exact classical secondary is -x/2, but it belongs naturally to the half-weighted/Perron summatory. For the ordinary right-continuous Sigma.summatory, there is no clean pointwise


$$S(x)=\frac{\pi^2}{12}x^2-\frac x2+o(x)$$


at integers because of jumps of size sigmaR n.
So the cheapest formal route is not a pointwise refined S(x) theorem. It is the smoothed Lambert moment package:
leansigmaMoment_zero_asympsigmaMoment_one_asympsigmaMoment_two_asympsigmaMoment_le_power
These are elementary real-variable Euler-Maclaurin statements.
(2) Kernel second-order expansion
The essential local expansion is:
leanerdosWeight_coef_second_order
with correction


$$1+\frac mn-\frac{C m^2}{8n^{3/2}}.$$


The reciprocal contributes +m/n; the square-root exponent contributes -C m²/(8 n^{3/2}).
(3) Cancellation
The cancellation is between three terms:


the -1/(2t) secondary in M₀;


the reciprocal correction +m/n, producing the leading part of M₁;


the exponent correction -C m²/(8n^{3/2}), producing the leading part of M₂.


In symbols:


$$-\frac1{2\lambda}
+
\frac{2Z}{\lambda^3}
-
\frac{C}{8}\frac{6Z}{\lambda^4}=0,
\qquad
Z=\lambda^2,\quad C=2\lambda.$$


This is the main algebra lemma to isolate.
(4) Cut structure
Use:


$$T_n=n^{2/3}.$$


Main range:


$$m\le n^{2/3}$$


for the second-order Taylor expansion.
Tail:


$$m>n^{2/3}$$


is exponentially small:


$$\exp(-c n^{1/6})$$


because


$$\sqrt n-\sqrt{n-m}\ge \frac{m}{2\sqrt n}.$$


This tail estimate is much stronger than needed and avoids relying on the already banked erdos_kernel_tail, which only gives qualitative smallness. The banked tail machinery is useful stylistically, but for the log-rate brick you want the explicit exponential tail.

9. Recommended brick order
I would implement in this order:


massLam_pos, massLam_sq.


Lambert identities for sigmaMoment 0, and optionally exact derivative identities for moments.


Regularized Euler-Maclaurin for boseReg0.


sigmaMoment_zero_asymp.


sigmaMoment_one_asymp, sigmaMoment_two_asymp.


sigmaMoment_le_power for r = 2,3,4.


sqrt_drop_second_order.


inv_sub_second_order.


erdosWeight_coef_second_order.


Explicit tail estimates beyond n^(2/3).


kernelMass_sub_approx2.


mass_rate_sqrt_coeff_cancel.


kernelMassApprox2_cancel_sqrt_term.


kernelMass_sub_one_rate.


erdos_kernel_total_log_rate.


This is the route that actually delivers the rate needed by both the barrier package and the record shell-error package.
## 2026-06-06 Opus design supplement: M₁ reduces to the M₀ core

- G(z) := Σ_d d²e^{−dz} = −boseKernel′(z)  [sign verified]
- M₁(t) = (1/t)·Σ_c h(tc), h(z) = z·G(z), singular part 2/z² (so Σ 2/(tc)² = 2ζ(2)/t² gives the
  leading 2Z/t³ after the 1/t prefactor)
- ∫₀^∞ (h − 2/z²) via antiderivative assembly: h − 2/z² = d/dz[−z·boseKernel] + boseReg0 − 1/z²;
  F(z) = −z·boseKernel(z) + 1/z has F(0+) = 0 (the −1/z + 1/z cancellation!) and F(∞) = 0, so
  ∫ (h − 2/z²) = ∫ boseReg0 = −1/2  — EXACTLY the M₁ secondary, no new integral needed.
- Same EM-O(1) core then gives M₁ = 2Z/t³ − 1/(2t²)·(1/t-scaled…) wait: M₁ = (1/t)[2Z/t² + (1/t)(−1/2) + O(1)]
  = 2Z/t³ − 1/(2t²) + O(1/t) ✓ matches R8.
- M₂ analogously: Σ d³e^{−dz} = boseKernel″, h₂(z) = z²·boseKernel″-form, singular 6/z²·…; same
  pattern (boundary algebra + the SAME two cores).
- Remaining hard core therefore: (a) ∫boseReg0 = −1/2 (FTC + integrability), (b) EM-O(1) Riemann
  bound for boseReg0-type kernels (R10 pending), (c) two-exponent antidiagonal rearrangements
  (M₁ = Σ'_{(d,c)} d²c x^{dc} etc.; mimic Mathlib TsumDivisorsAntidiagonal whose aux is private).

## 2026-06-06 Opus design supplement 2: the ∫boseReg0 = −1/2 brick (execution-ready)

- Antiderivative F(x) = 1/x − 1/(e^x−1); F′ = boseReg0 (via banked boseKernel_eq_exp_form).
- F(0+) = 1/2: F = (e^x−1−x)/(x(e^x−1)); with Real.exp_bound (n=3, |x|≤1): e^x−1 = x + x²/2 + δ,
  |δ| ≤ 2x³/9; F = (1/2 + δ/x²)/(1 + x/2 + δ/x) → 1/2 by tendsto algebra (δ/x² ≤ 2x/9 → 0).
- F(∞) = 0 (1/x → 0; 1/(e^x−1) → 0).
- Split ∫_{Ioi 0} = ∫_{Ioc 0 1} + ∫_{Ioi 1} (Set.Ioc_union_Ioi_eq_Ioi + setIntegral_union):
  · Ioc 0 1: extend F̃(0) := 1/2 continuous on [0,1] (the F(0+) limit);
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ⇒ ∫ = F(1) − 1/2.
  · Ioi 1: MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto ⇒ ∫ = 0 − F(1).
  · Total −1/2.
- Integrability: (0,1]: |boseReg0| ≤ 1 — numerator analysis x²e^x − (e^x−1)² = x⁴/4 − 2xδ − δ²
  (with the SAME δ), |num| ≤ x⁴(1/4+4/9+4/81) ≤ x⁴; denominator x²(e^x−1)² ≥ x⁴ (e^x−1 ≥ x);
  bounded + continuous on (0,1] + finite measure ⇒ integrable.
  Ioi 1: |boseReg0| ≤ boseKernel + 1/x²; boseKernel(x) ≤ e^{−x}/(1−e^{−1})² (x ≥ 1) +
  exp_neg_integrableOn_Ioi; 1/x² integrable on Ioi 1.
- All exp-Taylor needs are covered by Real.exp_bound at n = 3 (no series manipulation).

## 2026-06-06 Opus assembly-prerequisite finding: sharp moment bound needed

M₀/M₁/M₂ weak asymptotics BANKED (#112,#114,#116): |M_r − c_r·Z/t^{r+2}| ≤ K/t^{r+1}
(M₀ two-term O(1), M₁ |·−2Z/t³|≤388/t², M₂ |·−6Z/t⁴|≤K/t³). c_r = (r+1)!.

GAP for §5 kernelMass_sub_approx2: the error terms (1/n³)M₂ + (1/(n³√n))M₃ + (1/n⁴)M₄
need M_r ≤ K/t^{r+2} (true leading order), giving each O(1/n) at t≈C/(4√n)≈n^{−1/2}.
- (1/n³)M₂: M₂≤K/t⁴ ✓ (have weak asymp).
- (1/(n³√n))M₃: needs M₃≤K/t⁵=K/t^{3+2}.
- (1/n⁴)M₄: needs M₄≤K/t⁶=K/t^{4+2}.
BUT current sigmaMoment_le_power (#111) only gives M_r ≤ (r+2)!·2^{r+3}/t^{r+3}
(σ(m)≤m² crude) → too weak by 1/t for r=3,4 (would give O(n^{−1/2}), breaks O(1/n)).

NEXT BRICK: `sigmaMoment_le_power_sharp (r) : M_r(t) ≤ K_r/t^{r+2}` on (0,1].
Proof route (divisor reindexing + two-regime, no new kernels):
M_r(t) = Σ_d d^{r+1} Σ_k k^r e^{−tdk} [σ(m)=Σ_{d|m}d, m=dk]. Bound inner Σ_k k^r e^{−tdk}:
- td ≤ 1: ≤ r!·2^{r+1}/(td)^{r+1} (tsum_pow_mul_geometric_le).
- td > 1: ≤ C_r e^{−td} (geometric tail).
Two-regime over d (d≤1/t poly bucket gives Σ_{d≤1/t} d^{r+1}·r!/(td)^{r+1} = r!/t^{r+1}·(1/t)=r!/t^{r+2};
d>1/t exp bucket Σ d^{r+1}e^{−td} ~ /t^{r+2}). Mirrors weighted_decay_sum_bound structure.
Then §5 assembly (kernelMassApprox2, cancel_sqrt_term via mass_rate_sqrt_coeff_cancel #94,
kernelMass_sub_one_rate) proceeds.

## 2026-06-06 (cont.) Sharp moment bound — progress + remaining

File: AnalyticCombinatorics/Ch8/Partitions/MassRateMomentSharp.lean (WIP, NOT committed/imported).

DONE (verified, EXIT 0): `summable_weighted_antidiag (r) (0<ρ<1) : Summable (fun c:ℕ+×ℕ+ =>
  c.1^{r+1} c.2^r ρ^{c.1·c.2})` — via ρ^{ab} ≤ ρ^{a+b-1} (ab≥a+b-1) ⟹ dominated by
  ρ⁻¹(a^{r+1}ρ^a)(b^rρ^b), product of two `summable_pow_mul_geometric ∘ PNat.coe_injective`.

IN PROGRESS: `sigmaMoment_eq_prod_tsum (r) : M_r t = Σ_a Σ_b a^{r+1} b^r (e^{-t})^{ab}`.
  Structure (mirrors Mathlib tsum_prod_pow_eq_tsum_sigma), all structural blockers RESOLVED:
  - M_r in ℕ+ σ-form (tsum_if_ne_zero_eq_pnat + sigmaR_eq_sigma_one + exp=ρ^).
  - `← hsumm.tsum_prod` to Σ_{ℕ+×ℕ+}.
  - `← Equiv.tsum_eq _root_.sigmaAntidiagonalEquivProd F` (MUST use _root_. — name is
    ambiguous with Finset.sigmaAntidiagonalEquivProd; this caused rounds 2-7 of failures).
  - `hg.tsum_sigma` with hg : Summable in APPLICATION form (not ∘) via Equiv.summable_iff.
  - `unfold _root_.sigmaAntidiagonalEquivProd _root_.divisorsAntidiagonalFactors;
     simp only [Equiv.coe_fn_mk, PNat.mk_coe]` to expose explicit factors (simp/dsimp can't
     name-unfold the Equiv def; `unfold` works WITH _root_ qualification).
  - `Finset.sum_coe_sort` (NOT sum_attach — goal is ∑ b:↥s not ∑∈s.attach).
  BLOCKER (last step, line ~102): `Nat.sum_divisorsAntidiagonal (f := ... : ℕ→ℕ→ℝ) (n := e)`
  gives "AddCommMonoid ?m metavariable stuck". The per-e identity Σ_{(a,b):ab=e} a^{r+1}b^r
  = e^r σ(e) is mathematically: a^{r+1}b^r = a·(ab)^r = a·e^r, Σ a = σ(e). FIX OPTIONS:
  (i) @Nat.sum_divisorsAntidiagonal ℝ _ f e with full explicit args (find exact sig);
  (ii) factor ρ^e out first (constant on antidiag since ab=e), then prove
       Σ_{x∈antidiag e} x.1^{r+1}x.2^r = e^r σ(e) via per-x rewrite x.1^{r+1}x.2^r = e^r·x.1
       + a divisors↔antidiag first-projection sum lemma.

THEN: singular two-regime bound `sigmaMoment_le_power_sharp (r) : ∃K, M_r t ≤ K/t^{r+2}` on
  (0,1]: M_r = Σ_a a^{r+1} g(ta), g(z)=Σ_b b^r e^{-zb}, g(z) ≤ r!2^{r+1}/z^{r+1} (z≤1) and
  ≤ C_r e^{-z} (z≥1); two-regime over a (a≤1/t poly bucket = r!2^{r+1}/t^{r+2};
  a>1/t exp bucket via tsum_pow_mul_geometric_le = K/t^{r+2}). This is a SINGULAR-g variant
  of weighted_decay_sum_bound (#113, which has bounded g).

THEN §5 assembly uses sigmaMoment_le_power_sharp for M₃,M₄ + the banked M₀/M₁/M₂ weak asymptotics.

## 2026-06-06 (cont. 2) Sharp moment bound — inner geometric bound DONE, final assembly designed

DONE & BANKED: summable_weighted_antidiag, sigmaMoment_eq_prod_tsum (#117),
tsum_pnat_pow_mul_geometric_le (Σ'_{b≥1} b^r x^b ≤ x·2^r(r!+1)/(1−x)^{r+1}; the x-decay factor).

REMAINING: `sigmaMoment_le_power_sharp (r) : ∃ K, 0≤K ∧ ∀t∈(0,1], M_r t ≤ K/t^{r+2}`.
KEY INSIGHT (avoids two-regime — use a GLOBAL dominator):
  rw [sigmaMoment_eq_prod_tsum]; M_r = Σ'_a F(a), F(a)=Σ'_b a^{r+1}b^r ρ^{ab}=a^{r+1}·inner_a.
  inner_a = Σ'_b b^r (ρ^a)^b ≤ ρ^a·E/(1−ρ^a)^{r+1}  (tsum_pnat_pow_mul_geometric_le, E=2^r(r!+1)).
  1−ρ^a = 1−e^{−ta} ≥ ta/(1+ta)  [from 1+x≤e^x: e^{−ta}≤1/(1+ta), via one_div_le_one_div_of_le].
  ⟹ 1/(1−ρ^a)^{r+1} ≤ ((1+ta)/(ta))^{r+1}, and (1+ta)^{r+1} ≤ 2^{r+1}(1+(ta)^{r+1}).
  ⟹ F(a) ≤ D(a) := E·2^{r+1}(ρ^a/t^{r+1} + a^{r+1}ρ^a)   [a^{r+1}/(ta)^{r+1}=1/t^{r+1}, (ta)^{r+1}/t^{r+1}=a^{r+1}].
  Σ'_a F(a) ≤ Σ'_a D(a) [tsum_le_tsum; F summable via summable_prod_of_nonneg marginal of
    summable_weighted_antidiag; D summable = geometric + pow-geometric over ℕ+].
  Σ'_a D(a) = E2^{r+1}(Σ'_a ρ^a/t^{r+1} + Σ'_a a^{r+1}ρ^a)
    ≤ E2^{r+1}(2/(t·t^{r+1}) + (r+1)!2^{r+2}/t^{r+2})  [Σ'_a ρ^a ≤ ρ/(1−ρ) ≤ 2/t since 1−ρ≥t/2;
      Σ'_a a^{r+1}ρ^a ≤ Σ_ℕ a^{r+1}ρ^a ≤ (r+1)!/(1−ρ)^{r+2} ≤ (r+1)!2^{r+2}/t^{r+2}]
    = E·2^{r+1}(2 + (r+1)!2^{r+2})/t^{r+2}.  ⟹ K = E·2^{r+1}(2+(r+1)!2^{r+2}).
~100 lines, mechanical. Draft attempted (hden clean version works); per-a algebra + D-sum remain.

THEN §5 assembly uses sigmaMoment_le_power_sharp for r=2,3,4 (the M₃,M₄ error terms).

---

## §5 装配精确分解（Opus, 2026-06-06，实现中）

文件 `MassRateApprox2.lean`。已 banked: sub-lemma 1。

**关键发现**：`erdosWeight n m = σ(m)·[1/(n−m)·exp(−C(√n−√(n−m)))]`，σ(m) 是 divisor 权重。
#97 (`erdosWeight_coef_second_order`) bound 的是 bracket（不含 σ），exp 因子是 `exp(−(C/2)m/s)=exp(−tm)`，
t=λ/√n（**同一个 t**，不是 C/4！）。误差 RHS 分母 s⁶/s⁷/s⁸ = n³/n³s/n⁴。
`modelSummand n m = σ(m)·#97model`，所以 `erdosWeight−modelSummand = σ(m)·(#97 inner diff)`。

- **sub-lemma 1** `kernelMassApprox2_eq_tsum_model` ✅ banked (ababbf0):
  kernelMassApprox2 n = ∑' m, modelSummand n m，modelSummand = σ(m)e^{−tm}(1/n+m/n²−Cm²/(8n²√n))。
- **sub-lemma 2** `model_error_moment_bound`（写好，待验）:
  (3C²+5C+2)·[(1/n³)M₂+(1/(n³√n))M₃+(1/n⁴)M₄](t) ≤ K/n。纯 sharp #119 三连（r=2,3,4），t=λ/√n。
- **sub-lemma 3** `erdosWeight_sub_model_le`（per-term，待写）:
  对 1≤m, 2m≤n, 4Cm²≤s³: |erdosWeight−modelSummand| ≤ σ(m)(3C²+5C+2)e^{−tm}(m²/n³+m³/(n³s)+m⁴/n⁴)。
  证：erdosWeight−modelSummand=σ·(#97inner)，|·|=σ|#97inner|≤σ·#97RHS（×σ≥0），s⁶=n³ 等转换。
- **sub-lemma 4** `main_range_error_le`（main 和，待写）:
  Σ_{m∈Icc 1 ⌊n^{2/3}⌋}|err| ≤ Σ_{Icc}σ·#97RHS ≤ Σ'_m σ·#97RHS [sum_le_tsum,nonneg]
  = sub-lemma 2 表达式 ≤ K/n。需 #97 条件在 Icc 上成立（n≥max((4C)^6,8)）+ tsum 线性（同 sub-lemma 1）。
- **sub-lemma 5** 尾界（待写/可派 Codex）:
  (a) Σ_{⌊n^{2/3}⌋<m≤n−1} erdosWeight：右半 (n<2m) 有 `right_half_kernel_sum_le` = n³exp(−(C/10)√n) exp-small；
      左半远区 (n^{2/3}<m≤n/2) 需 quantitative 尾（n^{2/3}>√n·n^{1/6}≥R√n，但现有 erdos_kernel_tail 是 ε-form 定性，
      可能需新 quantitative 引理或用 leftBlockMajorant 几何尾）。
  (b) tail_model = Σ'_{m>⌊n^{2/3}⌋} modelSummand：exp-small。
      bound: modelSummand≤σ(m)e^{−tm}(1/n+m/n²+Cm²/(8n²s))，m>n^{2/3}⟹tm>λn^{1/6}，
      Σ'_{m>M}σm^k e^{−tm}≤e^{−tM/2}M_k(t/2)=exp-small·poly→exp-small。
- **assemble** `kernelMass_sub_approx2`:
  kernelMass−kernelMassApprox2 = Σ_{main}(err) + Σ_{far}erdosWeight − tail_model；三角 + 上述。
- 然后 `kernelMass_sub_one_rate`（= sub_approx2 + cancel #banked），barrier 实例化，R7 records，erdos_partition_limit_exists。
