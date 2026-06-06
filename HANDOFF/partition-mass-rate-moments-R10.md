I’ll treat this as a route-design brick tied to the banked MassRateMoments interfaces: first verify the moment precision budget, then give Lean-ready BV/Riemann-sum and Lambert-moment statements.

The precision simplification does reduce the needed asymptotics, but the near-zero cancellation still must be formalized directly; the monotone split loses it.

(1) Precision budget: confirmed
Yes. For the final kernel-mass assembly, it is enough to prove the weak moment asymptotics


$$M_0(t)=\frac{Z}{t^2}-\frac1{2t}+O(1),$$




$$M_1(t)=\frac{2Z}{t^3}+O(t^{-2}),$$




$$M_2(t)=\frac{6Z}{t^4}+O(t^{-3}),$$


where


$$Z=\frac{\pi^2}{6},\qquad t=\lambda/\sqrt n,\qquad \lambda=C/2,\qquad \lambda^2=Z.$$


The second terms of M₁ and M₂, and the constant term of M₀, are not needed.
The approximation was


$$A_n
=
\frac1n M_0(t)
+\frac1{n^2}M_1(t)
-\frac{C}{8n^2\sqrt n}M_2(t).$$


Substitute $t=\lambda/\sqrt n$:
M₀


$$\frac1nM_0(t)
=
\frac1n\left(\frac{Z}{t^2}-\frac1{2t}+O(1)\right)
=
\frac{Z}{\lambda^2}
-\frac1{2\lambda\sqrt n}
+O(1/n)
=
1-\frac1{2\lambda\sqrt n}+O(1/n).$$


M₁


$$\frac1{n^2}M_1(t)
=
\frac1{n^2}\left(\frac{2Z}{t^3}+O(t^{-2})\right)
=
\frac{2Z}{\lambda^3\sqrt n}
+O(1/n).$$


M₂


$$-\frac{C}{8n^2\sqrt n}M_2(t)
=
-\frac{C}{8n^2\sqrt n}
\left(\frac{6Z}{t^4}+O(t^{-3})\right)
=
-\frac{6CZ}{8\lambda^4\sqrt n}
+O(1/n).$$


The $n^{-1/2}$-coefficient is


$$-\frac1{2\lambda}
+
\frac{2Z}{\lambda^3}
-
\frac{6CZ}{8\lambda^4}.$$


Using $Z=\lambda^2$ and $C=2\lambda$, this becomes


$$-\frac1{2\lambda}
+\frac2\lambda
-\frac{3}{2\lambda}
=0.$$


So the weak statements are enough:
leantheorem sigmaMoment_zero_asymp_weak :  ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧    ∀ t : ℝ, 0 < t → t < δ →      |sigmaMoment 0 t -        ((Real.pi ^ 2 / 6) / t ^ 2 - (1 / 2 : ℝ) / t)|        ≤ K
leantheorem sigmaMoment_one_asymp_weak :  ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧    ∀ t : ℝ, 0 < t → t < δ →      |sigmaMoment 1 t -        (2 * (Real.pi ^ 2 / 6) / t ^ 3)|        ≤ K / t ^ 2
leantheorem sigmaMoment_two_asymp_weak :  ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧    ∀ t : ℝ, 0 < t → t < δ →      |sigmaMoment 2 t -        (6 * (Real.pi ^ 2 / 6) / t ^ 4)|        ≤ K / t ^ 3
These are strictly easier than the earlier R8 precision.

(2) Riemann-sum mechanism: use bounded variation of the regularized kernel
Your diagnosis is right: splitting


$$boseReg0 = boseKernel - x^{-2}$$


and applying monotone estimates to the two singular pieces separately loses the cancellation and gives useless $O(t^{-2})$-scale errors.
The clean route is:


$$f=boseReg0$$


as a single regularized function. Prove:


boseReg0 is bounded near 0;


boseReg0 is integrable on (0,∞);


boseReg0 has integrable derivative on (0,∞).


Then prove the general Riemann-sum lemma:
leantheorem riemann_sum_Ioi_sub_integral_over_t_bound    {f f' : ℝ → ℝ}    (hf_deriv :      ∀ x : ℝ, 0 < x → HasDerivAt f (f' x) x)    (hf'_integrable :      IntegrableOn f' (Set.Ioi 0))    (hf_integrable :      IntegrableOn f (Set.Ioi 0))    (hf_bdd_zero :      ∃ η M : ℝ, 0 < η ∧ 0 ≤ M ∧        ∀ x : ℝ, 0 < x → x ≤ η → |f x| ≤ M) :    ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧      ∀ t : ℝ, 0 < t → t < δ →        |(∑' k : ℕ, if k = 0 then 0 else f (t * (k : ℝ)))          - (1 / t) * ∫ x in Set.Ioi 0, f x|        ≤ K
Proof sketch:
For each cell [kt,(k+1)t],


$$t f(kt)-\int_{kt}^{(k+1)t}f(x)\,dx
=
\int_{kt}^{(k+1)t}(f(kt)-f(x))\,dx.$$


By absolute continuity,


$$|f(kt)-f(x)|
\le
\int_{kt}^{(k+1)t}|f'(u)|\,du.$$


So


$$\left|
t\sum_{k\ge1}f(tk)-\int_t^\infty f
\right|
\le
t\int_t^\infty |f'|.$$


Then


$$\left|
t\sum_{k\ge1}f(tk)-\int_0^\infty f
\right|
\le
t\int_0^\infty |f'|
+
\int_0^t |f|.$$


The boundedness of f near zero gives


$$\int_0^t |f| \le M t.$$


Divide by t:


$$\left|
\sum_{k\ge1}f(tk)-\frac1t\int_0^\infty f
\right|
\le
\int_0^\infty |f'| + M.$$


This gives the desired O(1) bound.
This avoids trapezoid endpoint constants entirely.

(3a) Integral of boseReg0
Define the antiderivative:
leannoncomputable def boseAntideriv (x : ℝ) : ℝ :=  1 / x - 1 / (Real.exp x - 1)
For 0 < x,


$$boseAntideriv'(x)
=
-\frac1{x^2}
+
\frac{e^x}{(e^x-1)^2}
=
boseReg0(x).$$


Bank this finite-interval FTC first.
leanlemma boseAntideriv_hasDerivAt    {x : ℝ} (hx : 0 < x) :    HasDerivAt boseAntideriv (boseReg0 x) x
Proof sketch: use boseKernel_eq_exp_form, derivative of 1/x, derivative of 1/(exp x - 1), and field_simp with Real.exp x - 1 ≠ 0.
Then:
leanlemma intervalIntegral_boseReg0_eq    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :    ∫ x in a..b, boseReg0 x =      boseAntideriv b - boseAntideriv a
Proof sketch: use the finite compact FTC. I would not rely on a one-shot improper-FTC theorem. Use the finite lemma currently named around
leanintervalIntegral.integral_deriv_eq_sub
or its primed variant, depending on your Mathlib snapshot. This is the only API-sensitive line. The statement itself should be wrapped as intervalIntegral_boseReg0_eq so the rest of the file is stable.
Endpoint limits:
leanlemma boseAntideriv_tendsto_atTop :    Tendsto boseAntideriv atTop (𝓝 0)
Proof sketch:


$$1/x\to0,\qquad 1/(e^x-1)\to0.$$


leanlemma exp_sub_one_sub_self_div_sq_tendsto_half :    Tendsto      (fun x : ℝ => (Real.exp x - 1 - x) / x ^ 2)      (𝓝[>] 0)      (𝓝 (1 / 2 : ℝ))
leanlemma exp_sub_one_div_self_tendsto_one :    Tendsto      (fun x : ℝ => (Real.exp x - 1) / x)      (𝓝[>] 0)      (𝓝 1)
Then:
leanlemma boseAntideriv_tendsto_zero_right :    Tendsto boseAntideriv (𝓝[>] 0) (𝓝 (1 / 2 : ℝ))
because


$$\frac1x-\frac1{e^x-1}
=
\frac{e^x-1-x}{x(e^x-1)}
=
\frac{(e^x-1-x)/x^2}{(e^x-1)/x}.$$


Now the integral:
leantheorem integral_boseReg0_Ioi :    ∫ x in Set.Ioi 0, boseReg0 x = -(1 / 2 : ℝ)
Proof sketch:
Split at 1:


$$\int_0^\infty f
=
\int_0^1 f+\int_1^\infty f.$$


For the first part, take the limit of


$$\int_\varepsilon^1 f = F(1)-F(\varepsilon)$$


as $\varepsilon\to0^+$. For the second, take the limit of


$$\int_1^R f = F(R)-F(1)$$


as $R\to\infty$. The sum is


$$(F(1)-1/2)+(0-F(1))=-1/2.$$


Lean wrapper statements:
leanlemma integral_Ioc_zero_one_boseReg0 :    ∫ x in Set.Ioc 0 1, boseReg0 x =      boseAntideriv 1 - (1 / 2 : ℝ)
leanlemma integral_Ioi_one_boseReg0 :    ∫ x in Set.Ioi 1, boseReg0 x =      - boseAntideriv 1
Then combine using Set.Ioi 0 = Set.Ioc 0 1 ∪ Set.Ioi 1 up to null endpoints.

(3a) Integrability of boseReg0
Use explicit local and tail bounds.
Near zero
The stable rational expression is:


$$boseReg0(x)
=
\frac{x^2e^x-(e^x-1)^2}{x^2(e^x-1)^2}.$$


State:
leanlemma boseReg0_eq_small_num    {x : ℝ} (hx : 0 < x) :    boseReg0 x =      (x ^ 2 * Real.exp x - (Real.exp x - 1) ^ 2) /        (x ^ 2 * (Real.exp x - 1) ^ 2)
Then bank polynomial exponential bounds for 0 ≤ x ≤ 1:
leanlemma exp_sub_one_bounds_order3    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :    x + x ^ 2 / 2 ≤ Real.exp x - 1 ∧    Real.exp x - 1 ≤ x + x ^ 2 / 2 + x ^ 3
leanlemma exp_sub_one_sub_self_sq_bound    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :    |Real.exp x - 1 - x - x ^ 2 / 2| ≤ x ^ 3
From these:
leanlemma boseReg0_bdd_near_zero :  ∃ M : ℝ, 0 ≤ M ∧    ∀ x : ℝ, 0 < x → x ≤ 1 → |boseReg0 x| ≤ M
Proof sketch: write y = Real.exp x - 1. Use


$$y=x+\frac{x^2}{2}+O(x^3).$$


The numerator


$$x^2e^x-y^2$$


is $O(x^4)$, while the denominator is $\ge x^4$, because e^x - 1 ≥ x.
Tail
For 1 ≤ x:


$$boseKernel(x)=\frac{e^x}{(e^x-1)^2}
\le 4e^{-x}$$


because e^x - 1 ≥ e^x / 2 for large enough x, say x ≥ 1.
Thus:
leanlemma boseReg0_tail_bound :  ∃ M : ℝ, 0 ≤ M ∧    ∀ x : ℝ, 1 ≤ x →      |boseReg0 x| ≤ M * (Real.exp (-x) + 1 / x ^ 2)
Then:
leanlemma boseReg0_integrable_Ioi :    IntegrableOn boseReg0 (Set.Ioi 0)
Proof sketch: split (0,1] and [1,∞). Near zero use boundedness on finite measure. At infinity dominate by exp (-x) and x^{-2}.

(3b) O(1) Riemann-sum bound for boseReg0
Define derivative formula:
leannoncomputable def boseReg0Deriv (x : ℝ) : ℝ :=  - Real.exp x * (Real.exp x + 1) / (Real.exp x - 1) ^ 3    + 2 / x ^ 3
leanlemma boseReg0_hasDerivAt    {x : ℝ} (hx : 0 < x) :    HasDerivAt boseReg0 (boseReg0Deriv x) x
For the small-x derivative bound, use the cancellation numerator:


$$boseReg0'(x)
=
\frac{
2(e^x-1)^3
-
x^3e^x(e^x+1)
}{
x^3(e^x-1)^3
}.$$


State:
leanlemma boseReg0Deriv_eq_small_num    {x : ℝ} (hx : 0 < x) :    boseReg0Deriv x =      (2 * (Real.exp x - 1) ^ 3        - x ^ 3 * Real.exp x * (Real.exp x + 1)) /        (x ^ 3 * (Real.exp x - 1) ^ 3)
Polynomial bounds sufficient for 0 ≤ x ≤ 1:
leanlemma exp_sub_one_order4_bound    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :    |Real.exp x - 1 - x - x ^ 2 / 2 - x ^ 3 / 6| ≤ x ^ 4
Then:
leanlemma boseReg0Deriv_bdd_near_zero :  ∃ M : ℝ, 0 ≤ M ∧    ∀ x : ℝ, 0 < x → x ≤ 1 →      |boseReg0Deriv x| ≤ M
Proof sketch: write


$$y=e^x-1=x+\frac{x^2}{2}+\frac{x^3}{6}+O(x^4).$$


The numerator


$$2y^3-x^3(1+y)(2+y)$$


has all terms through degree 5 cancel; the crude degree-4 remainder is enough to prove


$$|2y^3-x^3(1+y)(2+y)|\le Mx^6.$$


The denominator satisfies


$$x^3(e^x-1)^3\ge x^6.$$


Then nlinarith or ring_nf plus nlinarith closes.
Tail derivative bound:
leanlemma boseReg0Deriv_tail_bound :  ∃ M : ℝ, 0 ≤ M ∧    ∀ x : ℝ, 1 ≤ x →      |boseReg0Deriv x| ≤        M * (Real.exp (-x / 2) + 1 / x ^ 3)
Proof sketch: the exponential part is


$$\frac{e^x(e^x+1)}{(e^x-1)^3}
\ll e^{-x}$$


for x ≥ 1; weaken to e^{-x/2}. The rational part is 2/x^3.
Then:
leanlemma boseReg0Deriv_integrable_Ioi :    IntegrableOn boseReg0Deriv (Set.Ioi 0)
Finally apply the general Riemann-sum lemma:
leantheorem boseReg0_riemann_sum_bound :  ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧    ∀ t : ℝ, 0 < t → t < δ →      |(∑' k : ℕ,          if k = 0 then 0 else boseReg0 (t * (k : ℝ)))        - (1 / t) * ∫ x in Set.Ioi 0, boseReg0 x|      ≤ K
Together with integral_boseReg0_Ioi, this gives:
leantheorem boseReg0_step_sum_weak :  ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧    ∀ t : ℝ, 0 < t → t < δ →      |(∑' k : ℕ,          if k = 0 then 0 else boseReg0 (t * (k : ℝ)))        + (1 / (2 * t))|      ≤ K

(3b) Weak M₀ asymptotic
Use:
leantheorem sigmaMoment_zero_lambert {t : ℝ} (ht : 0 < t) :  sigmaMoment 0 t =    ∑' k : ℕ, if k = 0 then 0 else boseKernel (t * (k : ℝ))
and
leanlemma boseKernel_eq_inv_sq_add_reg    {x : ℝ} (hx : x ≠ 0) :    boseKernel x = 1 / x ^ 2 + boseReg0 x
Then:
leantheorem sigmaMoment_zero_asymp_weak :  ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧    ∀ t : ℝ, 0 < t → t < δ →      |sigmaMoment 0 t -        ((Real.pi ^ 2 / 6) / t ^ 2 - (1 / 2 : ℝ) / t)|      ≤ K
Proof sketch:


$$M_0(t)
=
\sum_{k\ge1}\frac1{t^2k^2}
+
\sum_{k\ge1}boseReg0(tk).$$


Use Basel:
leanlemma tsum_inv_nat_sq :  (∑' k : ℕ, if k = 0 then 0 else 1 / (k : ℝ) ^ 2)    = Real.pi ^ 2 / 6
Then:


$$\sum_{k\ge1}\frac1{t^2k^2}
=
\frac{Z}{t^2},$$


and the regularized sum is


$$-\frac1{2t}+O(1).$$



(3c) M₁, M₂ without derivatives in t
For M₁ and M₂, use Lambert forms from power sums over d.
Define:
leannoncomputable def boseKernel2 (x : ℝ) : ℝ :=  Real.exp (-x) * (1 + Real.exp (-x)) /    (1 - Real.exp (-x)) ^ 3
This is


$$\sum_{d\ge1} d^2e^{-xd}.$$


leannoncomputable def boseKernel3 (x : ℝ) : ℝ :=  Real.exp (-x) *    (1 + 4 * Real.exp (-x) + Real.exp (-2 * x)) /    (1 - Real.exp (-x)) ^ 4
This is


$$\sum_{d\ge1} d^3e^{-xd}.$$


Then define the profiles:
leannoncomputable def momentProfile1 (x : ℝ) : ℝ :=  x * boseKernel2 xnoncomputable def momentProfile2 (x : ℝ) : ℝ :=  x ^ 2 * boseKernel3 x
and regularizations:
leannoncomputable def momentReg1 (x : ℝ) : ℝ :=  momentProfile1 x - 2 / x ^ 2noncomputable def momentReg2 (x : ℝ) : ℝ :=  momentProfile2 x - 6 / x ^ 2
Geometric power-sum identities
For |y| < 1:
leanlemma tsum_nat_sq_mul_geometric    {y : ℝ} (hy : |y| < 1) :    (∑' d : ℕ,      if d = 0 then 0 else (d : ℝ) ^ 2 * y ^ d)      =    y * (1 + y) / (1 - y) ^ 3
leanlemma tsum_nat_cube_mul_geometric    {y : ℝ} (hy : |y| < 1) :    (∑' d : ℕ,      if d = 0 then 0 else (d : ℝ) ^ 3 * y ^ d)      =    y * (1 + 4 * y + y ^ 2) / (1 - y) ^ 4
Proof sketch: derive from the geometric series by differentiating finite partial sums and then taking limits, or prove by algebraic recurrence on the closed-form generating functions. This is independent of t.
Lambert identities
leantheorem sigmaMoment_one_lambert    {t : ℝ} (ht : 0 < t) :    sigmaMoment 1 t =      ∑' k : ℕ,        if k = 0 then 0        else (k : ℝ) * boseKernel2 (t * (k : ℝ))
leantheorem sigmaMoment_two_lambert    {t : ℝ} (ht : 0 < t) :    sigmaMoment 2 t =      ∑' k : ℕ,        if k = 0 then 0        else (k : ℝ) ^ 2 * boseKernel3 (t * (k : ℝ))
Proof sketch:


$$M_r(t)
=
\sum_{d,k\ge1}(dk)^r d\,e^{-tdk}.$$


For r = 1:


$$M_1(t)
=
\sum_{k\ge1}k\sum_{d\ge1}d^2e^{-tdk}.$$


For r = 2:


$$M_2(t)
=
\sum_{k\ge1}k^2\sum_{d\ge1}d^3e^{-tdk}.$$


Use the already planned tsum divisor-pair reindexing from R9.
Rewrite into profiles
For t > 0:
leanlemma sigmaMoment_one_profile    {t : ℝ} (ht : 0 < t) :    sigmaMoment 1 t =      (1 / t) *        ∑' k : ℕ,          if k = 0 then 0          else momentProfile1 (t * (k : ℝ))
because


$$k\,boseKernel2(tk)
=
\frac1t(tk)boseKernel2(tk).$$


Similarly:
leanlemma sigmaMoment_two_profile    {t : ℝ} (ht : 0 < t) :    sigmaMoment 2 t =      (1 / t ^ 2) *        ∑' k : ℕ,          if k = 0 then 0          else momentProfile2 (t * (k : ℝ))
because


$$k^2\,boseKernel3(tk)
=
\frac1{t^2}(tk)^2boseKernel3(tk).$$


Regularized profile bounds
For M₁, prove:
leanlemma momentReg1_pointwise_bound :  ∃ K : ℝ, 0 ≤ K ∧    ∀ x : ℝ, 0 < x →      |momentReg1 x| ≤        if x ≤ 1 then K else K / x ^ 2
For M₂:
leanlemma momentReg2_pointwise_bound :  ∃ K : ℝ, 0 ≤ K ∧    ∀ x : ℝ, 0 < x →      |momentReg2 x| ≤        if x ≤ 1 then K else K / x ^ 2
Proof sketch for both:
Near zero, use polynomial bounds for e^x - 1. The expansions are:


$$momentProfile1(x)=\frac2{x^2}+O(1),$$




$$momentProfile2(x)=\frac6{x^2}+O(1).$$


No integral or derivative is needed. At infinity, the Bose kernels are exponentially small, so the regularizations are essentially -2/x² and -6/x².
From this, get the generic summation bound:
leanlemma regularized_profile_sum_le_const_over_t    {f : ℝ → ℝ}    (hf :      ∃ K : ℝ, 0 ≤ K ∧        ∀ x : ℝ, 0 < x →          |f x| ≤ if x ≤ 1 then K else K / x ^ 2) :    ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧      ∀ t : ℝ, 0 < t → t < δ →        |∑' k : ℕ, if k = 0 then 0 else f (t * (k : ℝ))|          ≤ K / t
Proof sketch: split at k ≤ ⌈1/t⌉.
For tk ≤ 1, there are O(1/t) terms, each bounded by K.
For tk > 1,


$$|f(tk)|\le \frac{K}{t^2k^2},$$


and


$$\sum_{k>1/t}\frac1{t^2k^2}
\le
\frac{K'}t.$$


This is much easier than an Euler-Maclaurin estimate.
Weak M₁ asymptotic
leantheorem sigmaMoment_one_asymp_weak :  ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧    ∀ t : ℝ, 0 < t → t < δ →      |sigmaMoment 1 t -        (2 * (Real.pi ^ 2 / 6) / t ^ 3)|      ≤ K / t ^ 2
Proof sketch:


$$M_1(t)
=
\frac1t
\sum_{k\ge1}
\left(\frac{2}{t^2k^2}+momentReg1(tk)\right).$$


The first term is


$$\frac1t\cdot \frac{2Z}{t^2}
=
\frac{2Z}{t^3}.$$


The regularized sum is O(1/t), hence after multiplying by 1/t, it contributes O(1/t²).
Weak M₂ asymptotic
leantheorem sigmaMoment_two_asymp_weak :  ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧    ∀ t : ℝ, 0 < t → t < δ →      |sigmaMoment 2 t -        (6 * (Real.pi ^ 2 / 6) / t ^ 4)|      ≤ K / t ^ 3
Proof sketch:


$$M_2(t)
=
\frac1{t^2}
\sum_{k\ge1}
\left(\frac{6}{t^2k^2}+momentReg2(tk)\right).$$


The first term is


$$\frac1{t^2}\cdot\frac{6Z}{t^2}
=
\frac{6Z}{t^4}.$$


The regularized sum is O(1/t), hence after multiplying by 1/t², it contributes O(1/t³).

Recommended brick order
I would implement the R10 layer in this order:


exp_sub_one_bounds_order3


exp_sub_one_sub_self_sq_bound


exp_sub_one_order4_bound


boseReg0_eq_small_num


boseReg0_bdd_near_zero


boseReg0_tail_bound


boseReg0_integrable_Ioi


boseAntideriv


boseAntideriv_hasDerivAt


intervalIntegral_boseReg0_eq


boseAntideriv_tendsto_atTop


boseAntideriv_tendsto_zero_right


integral_boseReg0_Ioi


boseReg0Deriv, boseReg0_hasDerivAt


boseReg0Deriv_bdd_near_zero


boseReg0Deriv_tail_bound


boseReg0Deriv_integrable_Ioi


riemann_sum_Ioi_sub_integral_over_t_bound


boseReg0_riemann_sum_bound


boseReg0_step_sum_weak


sigmaMoment_zero_asymp_weak


boseKernel2, boseKernel3


tsum_nat_sq_mul_geometric, tsum_nat_cube_mul_geometric


sigmaMoment_one_lambert, sigmaMoment_two_lambert


momentProfile1, momentProfile2, momentReg1, momentReg2


momentReg1_pointwise_bound, momentReg2_pointwise_bound


regularized_profile_sum_le_const_over_t


sigmaMoment_one_asymp_weak


sigmaMoment_two_asymp_weak


This keeps the genuinely delicate cancellation proof localized to boseReg0 and avoids needing full trapezoid constants or derivative-based Euler-Maclaurin for M₁ and M₂.