I’ll give a Lean-facing theorem dependency graph using the verified kernel interface, replacing naive max induction with a good-scale block envelope and high/low propagation renewal package.

The route will be stated at lemma granularity, with boundedness handled by a barrier/slab induction over √n layers and oscillation control using monotonicity to rule out isolated spikes.

Recommendation
Use a two-layer route.
First prove two-sided boundedness by logarithmic Lyapunov barriers, not by the naive running maximum induction. The naive induction fails because kernelMass n → 1 is too weak: a recurrence with mass 1 + 1 / √n can have subexponential but unbounded solutions. The clean formal mechanism is:


$$H_+(n)=1-\frac{A}{\log(n+E)},\qquad
H_-(n)=1+\frac{A}{\log(n+E)}.$$


H_+ is an increasing bounded supersolution; H_- is a decreasing bounded subsolution. A fixed positive kernel window gives a drift of size


$$\frac{1}{\sqrt n\,\log^2 n},$$


which dominates a sharpened total-mass error of size, for example,


$$O\!\left(\frac{\log n}{n}\right).$$


Then prove convergence by a finite-block renewal theorem in the variable $\sqrt n$. The high-value propagation argument is best formalized as this block-renewal theorem; direct pointwise propagation is messier and tends to lose constants.
So the answer to option (1) is:
Do not use constant supersolutions. Do not try to close naive max induction from kernelMass → 1. Add one sharpened “critical mass rate” lemma, then use logarithmic barriers for boundedness. After boundedness, use an abstract finite-block renewal/aperiodic smoothing theorem for liminf = limsup.

A. Kernel-rate and fixed-window package
You already have erdos_kernel_total : kernelMass n → 1, but for boundedness I would add the following sharpened rate. Without something of this strength, boundedness is not formally forced by the currently listed hypotheses.
leannamespace AnalyticCombinatorics.Ch8.Partitions.Erdosnoncomputable def kernelMass (n : ℕ) : ℝ :=  ∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n mnoncomputable def kernelWindow (a b : ℝ) (n : ℕ) : ℝ :=  ∑ m ∈ Finset.Icc 1 (n - 1),    if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧       (m : ℝ) ≤ b * Real.sqrt (n : ℝ)    then erdosWeight n m    else 0
1. Critical total-mass rate
leantheorem erdos_kernel_total_log_rate :  ∃ A : ℝ, 0 < A ∧    ∀ᶠ n : ℕ in Filter.atTop,      |kernelMass n - 1|        ≤ A * Real.log ((n : ℝ) + 3) / (n : ℝ)
Proof sketch: expand erdosWeight against the model kernel. The apparent $1/\sqrt n$ term from 1/(n-m) and the square-root drop cancels with the linear secondary term in the smoothed divisor summatory. The remaining smooth weighted error is $O(\log n/n)$. This is the one extra analytic brick I would add before boundedness. It is elementary but sharper than the already banked kernelMass → 1.
A slightly more abstract version sufficient for the barriers is:
leantheorem erdos_kernel_total_barrier_rate :  ∃ A : ℝ, 0 < A ∧    ∀ᶠ n : ℕ in Filter.atTop,      |kernelMass n - 1|        ≤ A / (Real.sqrt (n : ℝ) *               (Real.log ((n : ℝ) + 3)) ^ 2) / 10
The log_rate statement implies this eventually.

2. Positive fixed window
leantheorem erdos_kernel_fixed_window_pos :  ∃ a₀ b₀ μ : ℝ,    0 < a₀ ∧ a₀ < b₀ ∧ 0 < μ ∧    ∀ᶠ n : ℕ in Filter.atTop,      μ ≤ kernelWindow a₀ b₀ n
Proof sketch: take any 0 < a₀ < b₀, for example a₀ = 1, b₀ = 2. By erdos_kernel_window,


$$\kernelWindow(a₀,b₀,n)
\to
\int_{a₀}^{b₀} \frac{\pi^2}{6}y e^{-Cy/2}\,dy,$$


and the integral is positive because the integrand is positive on the interval.

B. Logarithmic barriers: the mechanism that closes boundedness
Define, with L n = log ((n : ℝ) + E):
leannoncomputable def upperBarrier (A E : ℝ) (n : ℕ) : ℝ :=  1 - A / Real.log ((n : ℝ) + E)noncomputable def lowerBarrier (A E : ℝ) (n : ℕ) : ℝ :=  1 + A / Real.log ((n : ℝ) + E)noncomputable def barrierSlack (E : ℝ) (n : ℕ) : ℝ :=  1 / (Real.sqrt (n : ℝ) *       (Real.log ((n : ℝ) + E)) ^ 2)
Choose E large enough so logs are positive and upperBarrier A E n > 0 eventually.

3. Barrier monotonicity and boundedness
leanlemma upperBarrier_eventually_pos_bdd    {A E : ℝ} (hA : 0 < A) (hE : 3 ≤ E) :  ∀ᶠ n : ℕ in Filter.atTop,    0 < upperBarrier A E n ∧ upperBarrier A E n ≤ 1lemma lowerBarrier_eventually_pos_bdd    {A E : ℝ} (hA : 0 < A) (hE : 3 ≤ E) :  ∀ᶠ n : ℕ in Filter.atTop,    1 ≤ lowerBarrier A E n ∧ lowerBarrier A E n ≤ 1 + A
Proof sketch: direct logarithmic estimates. upperBarrier increases to 1; lowerBarrier decreases to 1.

4. Barrier gap on a positive kernel window
For a₀√n < m ≤ b₀√n, the difference between n and n-m is of order √n, so the logarithmic barrier changes by order


$$\frac{1}{\sqrt n \log^2 n}.$$


leanlemma upperBarrier_gap_on_window    {A E a₀ b₀ : ℝ}    (hA : 0 < A) (hE : 3 ≤ E)    (ha₀ : 0 < a₀) (hab₀ : a₀ < b₀) :  ∃ c : ℝ, 0 < c ∧    ∀ᶠ n : ℕ in Filter.atTop,      ∀ m : ℕ,        a₀ * Real.sqrt (n : ℝ) < (m : ℝ) →        (m : ℝ) ≤ b₀ * Real.sqrt (n : ℝ) →        upperBarrier A E n - upperBarrier A E (n - m)          ≥ c * barrierSlack E n
leanlemma lowerBarrier_gap_on_window    {A E a₀ b₀ : ℝ}    (hA : 0 < A) (hE : 3 ≤ E)    (ha₀ : 0 < a₀) (hab₀ : a₀ < b₀) :  ∃ c : ℝ, 0 < c ∧    ∀ᶠ n : ℕ in Filter.atTop,      ∀ m : ℕ,        a₀ * Real.sqrt (n : ℝ) < (m : ℝ) →        (m : ℝ) ≤ b₀ * Real.sqrt (n : ℝ) →        lowerBarrier A E (n - m) - lowerBarrier A E n          ≥ c * barrierSlack E n
Proof sketch: use the mean-value theorem for x ↦ 1 / log (x + E) on [n-m,n]. Since m ≥ a₀√n and m ≤ b₀√n, eventually n-m ≥ n/2, and the derivative is comparable to 1 / (n log² n).

5. Upper barrier is superharmonic
leantheorem upperBarrier_kernel_superharmonic :  ∃ A E δ : ℝ,    0 < A ∧ 3 ≤ E ∧ 0 < δ ∧    ∀ᶠ n : ℕ in Filter.atTop,      (∑ m ∈ Finset.Icc 1 (n - 1),          erdosWeight n m * upperBarrier A E (n - m))        ≤ upperBarrier A E n - δ * barrierSlack E n
Proof sketch: split the kernel into the positive window from erdos_kernel_fixed_window_pos and its complement. On the complement, use monotonicity of upperBarrier, giving at most upperBarrier n * kernelMass n. On the fixed window, subtract the window gap from Lemma 4. The loss is ≈ μ c barrierSlack n. The total-mass excess is at most O(log n / n), which is eventually smaller than half of this window loss. Choose A large enough if needed.

6. Lower barrier is subharmonic
leantheorem lowerBarrier_kernel_subharmonic :  ∃ A E δ : ℝ,    0 < A ∧ 3 ≤ E ∧ 0 < δ ∧    ∀ᶠ n : ℕ in Filter.atTop,      lowerBarrier A E n + δ * barrierSlack E n        ≤      (∑ m ∈ Finset.Icc 1 (n - 1),          erdosWeight n m * lowerBarrier A E (n - m))
Proof sketch: same split. lowerBarrier is decreasing, so predecessors have larger barrier values. The fixed window gives a positive surplus of order barrierSlack n, while the possible total-mass deficit is only O(log n / n).

7. Boundary is negligible relative to the barrier slack
leanlemma boundaryTerm_is_o_barrierSlack    {E : ℝ} (hE : 3 ≤ E) :  Filter.Tendsto    (fun n : ℕ => boundaryTerm n / barrierSlack E n)    Filter.atTop    (𝓝 0)
Equivalently:
leanlemma boundaryTerm_le_barrierSlack    {E δ : ℝ} (hE : 3 ≤ E) (hδ : 0 < δ) :  ∀ᶠ n : ℕ in Filter.atTop,    boundaryTerm n ≤ δ * barrierSlack E n
Proof sketch: boundaryTerm n = σ(n)e^{-C√n}, and σ(n) ≤ n²; exponential decay beats every power and logarithm.

C. Order-sharp upper and lower bounds
8. Upper induction using the superharmonic barrier
leantheorem u_upper_by_barrier :  ∃ M A E : ℝ,    0 < M ∧ 0 < A ∧ 3 ≤ E ∧    ∀ᶠ n : ℕ in Filter.atTop,      u n ≤ M * upperBarrier A E n
Proof sketch: choose A,E,δ from upperBarrier_kernel_superharmonic. Choose M large enough to dominate the finitely many initial values and to absorb the boundary:


$$boundaryTerm(n) \le M \delta\, barrierSlack(n).$$


Then induct on n using u_recurrence. For previous terms, apply the induction hypothesis. The superharmonic inequality gives


$$u_n \le M(H_+(n)-\delta s_n)+boundaryTerm(n)\le M H_+(n).$$



9. Upper boundedness
leantheorem u_limsup_finite :  ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in Filter.atTop, u n ≤ M
Proof sketch: upperBarrier A E n ≤ 1 eventually, so Lemma 8 gives u n ≤ M.

10. Positivity of u
leanlemma u_pos (n : ℕ) (hn : 1 ≤ n) : 0 < u n
Proof sketch: p(n) > 0, n > 0, and the exponential factor is positive.

11. Lower induction using the subharmonic barrier
leantheorem u_lower_by_barrier :  ∃ c A E : ℝ,    0 < c ∧ 0 < A ∧ 3 ≤ E ∧    ∀ᶠ n : ℕ in Filter.atTop,      c * lowerBarrier A E n ≤ u n
Proof sketch: choose A,E,δ from lowerBarrier_kernel_subharmonic. Pick c > 0 smaller than the finitely many ratios u k / lowerBarrier A E k before the induction threshold. Since boundaryTerm n ≥ 0, the recurrence gives


$$u_n
\ge c\sum_m W(n,m)H_-(n-m)
\ge c(H_-(n)+\delta s_n)
\ge cH_-(n).$$


No geometric decay occurs: the fixed positive kernel window gives an additive surplus in the subharmonic inequality at every large n.

12. Positive liminf
leantheorem u_liminf_positive :  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, c ≤ u n
Proof sketch: lowerBarrier A E n ≥ 1 eventually, so Lemma 11 gives c ≤ u n.

D. Where monotonicity enters
The barrier proofs above do not need partition monotonicity. They use only recurrence, positivity, kernel estimates, and boundary decay.
Monotonicity is needed for local Harnack/oscillation control and the convergence step.
13. Partition monotonicity
leantheorem part_monotone :  Monotone Partitions.part
Proof sketch: inject a partition of n into a partition of n+1 by adding one part of size 1.

14. Forward propagation for u
leantheorem u_local_lower_from_monotone    {n r : ℕ} (hn : 1 ≤ n) :  u (n + r)    ≥ ((n + r : ℝ) / (n : ℝ)) *        Real.exp (-C * (Real.sqrt (n + r : ℝ) - Real.sqrt (n : ℝ))) *        u n
Proof sketch:


$$u_{n+r}
=(n+r)p(n+r)e^{-C\sqrt{n+r}}
\ge (n+r)p(n)e^{-C\sqrt{n+r}}
=
\frac{n+r}{n}e^{-C(\sqrt{n+r}-\sqrt n)}u_n.$$


This is the only place where monotonicity of p is essential.

15. Local ratio control on √n-blocks
leantheorem u_local_ratio_control :  ∀ ε > 0, ∃ h > 0, ∀ᶠ n : ℕ in Filter.atTop,    ∀ r : ℕ,      (r : ℝ) ≤ h * Real.sqrt (n : ℝ) →        (1 - ε) * u n ≤ u (n + r) ∧        u n ≤ (1 + ε) * u (n + r)
Proof sketch: apply Lemma 14 and choose h small so


$$\frac{n+r}{n}e^{-C(\sqrt{n+r}-\sqrt n)}$$


is between 1 - ε and 1 + ε for r ≤ h√n. The reverse inequality follows by rearranging the same lower bound.
A bounded absolute version is often easier to use:
leantheorem u_local_abs_oscillation    (hupper : ∃ M > 0, ∀ᶠ n : ℕ in Filter.atTop, u n ≤ M) :  ∀ ε > 0, ∃ h > 0, ∀ᶠ n : ℕ in Filter.atTop,    ∀ r : ℕ,      (r : ℝ) ≤ h * Real.sqrt (n : ℝ) →        |u (n + r) - u n| ≤ ε
Proof sketch: combine u_local_ratio_control with the eventual upper bound.
No stronger information about p(n+r)/p(n) is needed.

E. Convergence: formalize as a finite-block renewal theorem
For liminf = limsup, I would not formalize Erdős’s high-value argument point-by point. The clean Lean object is a finite-block renewal theorem in the variable √n. It captures the same smoothing mechanism but avoids delicate pointwise interval bookkeeping.
Fix a small block width h > 0 and define blocks


$$B_j=\{n: jh\le \sqrt n < (j+1)h\}.$$


In Lean I would use finite integer intervals:
leannoncomputable def sqrtBlock (h : ℝ) (j : ℕ) : Finset ℕ :=  Finset.Icc ⌊((j : ℝ) * h) ^ 2⌋₊             ⌊(((j : ℝ) + 1) * h) ^ 2⌋₊
Then choose a representative, for example the left endpoint:
leannoncomputable def blockRep (h : ℝ) (j : ℕ) : ℕ :=  ⌊((j : ℝ) * h) ^ 2⌋₊
and the block sequence:
leannoncomputable def blockU (h : ℝ) (j : ℕ) : ℝ :=  u (blockRep h j)
Local oscillation says every u n in sqrtBlock h j is close to blockU h j, once h is small.

16. Block oscillation is small
leantheorem sqrtBlock_oscillation_small :  ∀ ε > 0, ∃ h > 0, ∀ᶠ j : ℕ in Filter.atTop,    ∀ n ∈ sqrtBlock h j,      |u n - blockU h j| ≤ ε
Proof sketch: numbers in the same √n-block differ by O(h√n). Apply u_local_abs_oscillation.

17. Discretized kernel weights
For fixed h, partition the jump variable


$$z=\sqrt n-\sqrt{n-m}\approx \frac{m}{2\sqrt n}$$


into finitely many h-blocks. Equivalently partition m/√n into intervals of length about 2h.
leannoncomputable def jumpWeight (h : ℝ) (r : ℕ) : ℝ :=  ∫ y in (2 * (r : ℝ) * h)..(2 * ((r : ℝ) + 1) * h),    (Real.pi ^ 2 / 6) * y * Real.exp (-(C / 2) * y)
Truncate at a large finite R.
leantheorem jumpWeight_nonneg :  ∀ h r, 0 ≤ jumpWeight h rtheorem jumpWeight_finite_mass_close_one :  ∀ ε > 0, ∃ h > 0, ∃ R : ℕ,    |(∑ r ∈ Finset.range R, jumpWeight h r) - 1| ≤ ε
Proof sketch: nonnegativity is by integral positivity. The total integral is 1, using your kernel total/integral identity. Choose R by tail control.

18. Aperiodic two-neighbor support
To use the finite renewal theorem, make sure two adjacent jump weights are positive.
leantheorem jumpWeight_adjacent_positive :  ∃ h > 0, ∃ r : ℕ,    0 < jumpWeight h r ∧ 0 < jumpWeight h (r + 1)
Proof sketch: the density is strictly positive on every interval inside (0,∞). Pick any small h and an interior pair of adjacent bins away from zero.
This is the formal replacement for “the kernel has a spread-out positive window.”

19. Approximate renewal equation for block representatives
leantheorem blockU_approx_renewal :  ∀ ε > 0, ∃ h > 0, ∃ R : ℕ, ∀ᶠ j : ℕ in Filter.atTop,    |blockU h j -      ∑ r ∈ Finset.range R, jumpWeight h r * blockU h (j - r - 1)|      ≤ ε
Proof sketch: apply u_recurrence at blockRep h j. Split the kernel into jump bins. Use erdos_kernel_window to identify the mass in each bin. Use sqrtBlock_oscillation_small to replace u(n-m) by the representative of the corresponding predecessor block. Use erdos_kernel_tail for the truncated tail and boundaryTerm → 0.
Half-open windows are useful here: the bins partition exactly without boundary double-counting.

20. Abstract finite-renewal convergence theorem
This is the core smoothing theorem I would formalize once and reuse.
leantheorem finite_renewal_approx_tendsto    {R : ℕ} {p : ℕ → ℝ} {v : ℕ → ℝ}    (hp_nonneg : ∀ r ∈ Finset.range R, 0 ≤ p r)    (hp_mass : (∑ r ∈ Finset.range R, p r) = 1)    (hp_aperiodic :      ∃ r, r ∈ Finset.range R ∧ r + 1 ∈ Finset.range R ∧        0 < p r ∧ 0 < p (r + 1))    (hv_bdd : ∃ M, ∀ j, |v j| ≤ M)    (hrec :      Tendsto        (fun j : ℕ =>          v j - ∑ r ∈ Finset.range R, p r * v (j - r - 1))        Filter.atTop        (𝓝 0)) :    ∃ L : ℝ, Tendsto v Filter.atTop (𝓝 L)
Proof sketch: this is the elementary finite-state renewal/maximum-principle lemma. Let D = limsup v, d = liminf v. Passing to limsup/liminf in the approximate convolution gives that any near-maximum forces predecessor blocks in the positive support to be near maximum. Because the support contains adjacent jumps, the additive semigroup is eventually all large integers. Hence near-maximum and near-minimum tails overlap, forcing D = d.
This is the cleanest Lean version of Erdős’s high-value propagation.

21. Convergence of u
leantheorem u_tendsto_exists :  ∃ L : ℝ, Tendsto u Filter.atTop (𝓝 L)
Proof sketch: choose h,R,p from blockU_approx_renewal; normalize the finite weights if necessary so their mass is exactly 1, with the normalization error absorbed into ε. Apply finite_renewal_approx_tendsto to blockU h. Then transfer from blockU h j back to arbitrary u n using sqrtBlock_oscillation_small.

22. Liminf equals limsup
leantheorem u_liminf_eq_limsup :  Filter.liminf u Filter.atTop = Filter.limsup u Filter.atTop
Proof sketch: immediate from u_tendsto_exists. If you want to avoid Filter.liminf API, prove the Cauchy/tendsto statement first, then derive this as a wrapper lemma.

23. Positive Erdős limit
leantheorem erdos_partition_limit_exists :  ∃ a : ℝ, 0 < a ∧ Tendsto u Filter.atTop (𝓝 a)
Proof sketch: get ∃ L, Tendsto u atTop (𝓝 L) from Lemma 21. Use u_liminf_positive to show 0 < L.

F. Direct high-value propagation skeleton
If you do want the proof closer to Erdős’s original language, formalize these after boundedness. They are equivalent in spirit to the finite-renewal theorem above.
24. Near-maximum pulls back through a positive kernel window
leanlemma near_limsup_pulls_back_window    {D ε η a b : ℝ}    (hD : IsLimsup u D)    (hε : 0 < ε)    (hwin : 0 < a ∧ a < b)    (hmass : ∀ᶠ n, μ ≤ kernelWindow a b n) :  ∀ᶠ n : ℕ in Filter.atTop,    D - ε ≤ u n →      ∃ k : ℕ,        n - ⌊b * Real.sqrt (n : ℝ)⌋₊ ≤ k ∧        k < n - ⌊a * Real.sqrt (n : ℝ)⌋₊ ∧        D - η ≤ u k
Proof sketch: use the recurrence at n. If every predecessor in the window were below D - η, while all sufficiently large predecessors are below D + ε, then the weighted average would be below D - ε, contradicting u n ≥ D - ε.

25. Monotonicity fills a short forward block
leanlemma high_point_fills_forward_block    {η L : ℝ} (hη : 0 < η) (hL : 0 < L) :  ∀ᶠ n : ℕ in Filter.atTop,    ∀ r : ℕ,      (r : ℝ) ≤ L * Real.sqrt (n : ℝ) →        D - η ≤ u n →          D - 2 * η ≤ u (n + r)
Proof sketch: use u_local_lower_from_monotone. Choose L small so the exponential loss is less than η, using boundedness of D.

26. Backward interval expansion
leanlemma near_high_interval_expands_backward    {s₀ s₁ : ℝ} (hs : 0 < s₀ ∧ s₀ < s₁) :  ∀ η > 0, ∃ η' > 0, ∀ᶠ N : ℕ in Filter.atTop,    high_on_sqrt_interval u (D - η) N s₀ s₁ →      high_on_sqrt_interval u (D - η') N (s₀ + c₁) (s₁ + c₂)
Proof sketch: combine Lemmas 24 and 25. A high interval at the right endpoint pulls back through a fixed positive kernel window, then monotonicity fills short forward gaps. In √n-coordinates this is Minkowski addition by a fixed interval.

27. Interval percolation
leanlemma sqrt_interval_percolation :  ∃ K : ℕ, ∀ I : sqrtInterval,    after K iterations of the expansion operator,    I covers every sufficiently long sqrt-block interval
Proof sketch: because the expansion interval has positive length and contains two incommensurable/adjacent block offsets after discretization, repeated Minkowski sums eventually cover a tail of the block lattice. This is the pointwise version of the finite-renewal aperiodicity lemma.

28. Contradiction from high and low intervals
leanlemma liminf_eq_limsup_from_high_low_propagation    (hupper : ∃ M > 0, ∀ᶠ n, u n ≤ M)    (hlower : ∃ m > 0, ∀ᶠ n, m ≤ u n)    (hlocal : u_local_abs_oscillation_statement)    (hprop : near_high_interval_expansion_statement) :  Filter.liminf u Filter.atTop = Filter.limsup u Filter.atTop
Proof sketch: assume d < D. Pick high and low subsequences. Propagate high intervals and low intervals in the √n block lattice. Aperiodicity forces overlap. Local oscillation prevents a block from being simultaneously near D and near d, contradiction.
This direct version is faithful to Erdős but heavier than the finite-renewal theorem.

G. Answer to the four specific concerns
(1) Why naive upper induction fails, and what closes
Naive induction fails because kernelMass n = 1 + o(1) allows products of small excesses to drift over $\sqrt n$-many renewal steps. The exact Lean mechanism should be:
leanerdos_kernel_total_log_rateupperBarrier_kernel_superharmoniclowerBarrier_kernel_subharmonic
This is option (a), but not with a constant supersolution. Use logarithmic barriers 1 ± A/log n. Option (b) is possible but duplicates the same drift calculation in a less reusable form. Option (c), a pure renewal theorem, is excellent for convergence after boundedness, but by itself does not prove boundedness unless you add a critical mass-rate or Lyapunov hypothesis.
(2) Positive liminf and geometric decay
The clean lower-bound proof is not an iterated product. It is one-step induction with a decreasing lower barrier 1 + A/log n. The fixed positive window gives a surplus of order


$$1/(\sqrt n\log^2 n),$$


and the total-mass error is smaller. Thus the lower bound is preserved by induction without geometric decay.
The monotonicity lemma
leanu_local_lower_from_monotone
is still essential later for local oscillation/convergence, but not necessary for the barrier proof of u_liminf_positive.
(3) Liminf equals limsup
The cleanest formal skeleton is:
leanu_local_abs_oscillationblockU_approx_renewalfinite_renewal_approx_tendstou_tendsto_existsu_liminf_eq_limsup
This is the block-renewal version of Erdős’s high-value propagation. If you want the literal high-value route, use Lemmas 24–28, but I would formalize the finite-renewal theorem instead.
(4) Where p-monotonicity is needed
Only here:
leanu_local_lower_from_monotoneu_local_ratio_controlu_local_abs_oscillationsqrtBlock_oscillation_small
No stronger estimate on p(n+r)/p(n) is needed. The recurrence, kernel package, barrier lemmas, and boundary estimates handle boundedness and positive liminf.
Half-open versus closed windows
Use half-open windows everywhere:


$$(a\sqrt n,\ b\sqrt n].$$


They make block additivity exact:
leanblockSum C a b n =  blockSum C a c n + blockSum C c b n
for a ≤ c ≤ b, without endpoint correction terms. Closed windows would double-count mesh boundaries. Analytically the difference is negligible, but in Lean the half-open convention avoids a large amount of singleton bookkeeping.