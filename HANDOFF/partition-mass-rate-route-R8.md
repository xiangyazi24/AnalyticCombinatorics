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