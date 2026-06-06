I’ll treat your counterexample as decisive and replace the convergence layer rather than patching the false finite-renewal lemma. I’ll also spell out the barrier inequalities explicitly.

The answer will distinguish the summable-residual abstract repair from the usable finite-depth interval expansion, and check whether the block residuals meet that stronger condition.

You are right: the R6 finite_renewal_approx_tendsto is false. The sin (sqrt j) counterexample is decisive, and the issue is exactly that an o(1) residual does not prevent slow macroscopic drift.
The corrected convergence layer should not be the fixed-block approximate-renewal theorem. The route I would brick is:


$$\text{barrier boundedness}
\quad\to\quad
\text{record-extrema interval percolation}
\quad\to\quad
\text{tail oscillation } \to 0.$$


The key correction is to propagate record highs/lows, not arbitrary near-limsup points. Record extrema remove the exponential-loss quantifier trap: all predecessors are bounded by the record itself, and the accumulated pullback errors are summable in the $\sqrt n$-scale because the kernel-mass error is $O(\log n/n)$.

1. Repair (a): summable residuals
Corrected abstract theorem
This version is true, but I would prove it by a primitive companion-matrix contraction, not by the naive pullback-of-near-maxima argument.
leannamespace AnalyticCombinatorics.Renewalnoncomputable def finiteRenewalResidual    (R : ℕ) (p v : ℕ → ℝ) (j : ℕ) : ℝ :=  v j - ∑ r ∈ Finset.range R, p r * v (j - (r + 1))theorem finite_renewal_summable_residual_tendsto    {R : ℕ} {p v eps : ℕ → ℝ}    (hR : 2 ≤ R)    (hp_nonneg :      ∀ r ∈ Finset.range R, 0 ≤ p r)    (hp_mass :      (∑ r ∈ Finset.range R, p r) = 1)    (hp_adjacent :      ∃ r : ℕ,        r ∈ Finset.range R ∧ r + 1 ∈ Finset.range R ∧        0 < p r ∧ 0 < p (r + 1))    (hv_bdd :      ∃ M : ℝ, ∀ j : ℕ, |v j| ≤ M)    (heps_nonneg :      ∀ j : ℕ, 0 ≤ eps j)    (heps_summable :      Summable eps)    (hrec :      ∀ᶠ j : ℕ in Filter.atTop,        |finiteRenewalResidual R p v j| ≤ eps j) :    ∃ L : ℝ, Filter.Tendsto v Filter.atTop (𝓝 L)
Proof skeleton
Convert the scalar recurrence into a companion-vector recurrence. Define
leandef renewalState (R : ℕ) (v : ℕ → ℝ) (j : ℕ) : Fin R → ℝ :=  fun i => v (j - i)
and a stochastic companion matrix P. The first row is p 0, ..., p (R-1), and lower rows shift coordinates. The adjacent-positive hypothesis implies that P is primitive.
Brick the primitive contraction as:
leantheorem primitive_companion_osc_contract    {R : ℕ} {p : ℕ → ℝ}    (hR : 2 ≤ R)    (hp_nonneg : ∀ r ∈ Finset.range R, 0 ≤ p r)    (hp_mass : (∑ r ∈ Finset.range R, p r) = 1)    (hp_adjacent :      ∃ r : ℕ,        r ∈ Finset.range R ∧ r + 1 ∈ Finset.range R ∧        0 < p r ∧ 0 < p (r + 1)) :    ∃ L : ℕ, ∃ θ : ℝ,      0 < θ ∧ θ < 1 ∧      ∀ x : Fin R → ℝ,        osc (companionPower R p L x) ≤          (1 - θ) * osc x
where
leannoncomputable def osc {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=  (Finset.univ.sup' _ ?nonempty x) -  (Finset.univ.inf' _ ?nonempty x)
Then show the residual perturbation contributes at most a finite convolution of eps:
leanlemma renewal_state_contract_with_error :  ∃ L : ℕ, ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧    ∀ᶠ j : ℕ in Filter.atTop,      osc (renewalState R v (j + L))        ≤ (1 - θ) * osc (renewalState R v j)          + A * ∑ i ∈ Finset.Icc j (j + L), eps i
Since eps is summable, the moving finite-window error tends to zero. A standard contraction lemma gives:
leanlemma eventually_contracting_osc_tends_zero    {w e : ℕ → ℝ} {q A : ℝ} {L : ℕ}    (hq : 0 ≤ q ∧ q < 1)    (he_nonneg : ∀ n, 0 ≤ e n)    (he_tendsto : Filter.Tendsto e Filter.atTop (𝓝 0))    (hw_nonneg : ∀ n, 0 ≤ w n)    (hcontract :      ∀ᶠ n in Filter.atTop,        w (n + L) ≤ q * w n + A * e n) :    Filter.Tendsto w Filter.atTop (𝓝 0)
Finally osc (renewalState R v j) → 0 implies v j is Cauchy, hence convergent.
Check against v j = sin (sqrt j)
It is excluded. Its residual for a nontrivial finite delay law is


$$v_j-\sum_r p_r v_{j-r-1}
=
\frac{\mu}{2\sqrt j}\cos(\sqrt j)+O(j^{-1}),
\qquad
\mu=\sum_r p_r(r+1)>0.$$


The absolute value is $\gg |\cos\sqrt j|/\sqrt j$ on a positive-density set of $\sqrt j$-blocks, so no summable eps can dominate it eventually.
Does repair (a) apply here?
No. Your diagnosis is correct.
For the fixed √n-block sequence blockU h j, the residual from replacing all values in a block by a representative is $O(h)$ for fixed h. That is not summable in j. The finite-bin truncation and mesh errors are also fixed tolerances, not summable sequences. Taking h = h j → 0 would destroy the fixed finite-renewal structure and reintroduce a nonstationary kernel problem.
So repair (a) is a valid abstract theorem, but it is not the right tool for the Erdős partition recurrence.

2. Correct convergence route: record-extrema interval percolation
The direct route should be formulated with records, not arbitrary near-limsup points.
The central statement should be:
leantheorem high_record_covers_tail :  ∀ ε > 0, ∃ N₀ : ℕ, ∀ N : ℕ,    highRecordFrom N₀ N →      ∀ k : ℕ, N₀ ≤ k → k ≤ N →        u N - ε ≤ u k
and similarly:
leantheorem low_record_covers_tail :  ∀ ε > 0, ∃ N₀ : ℕ, ∀ N : ℕ,    lowRecordFrom N₀ N →      ∀ k : ℕ, N₀ ≤ k → k ≤ N →        u k ≤ u N + ε
Then convergence is immediate from finite-interval record maxima/minima.

3. Core definitions
3.1 Records
leannamespace AnalyticCombinatorics.Ch8.Partitions.Erdosdef highRecordFrom (N₀ N : ℕ) : Prop :=  N₀ ≤ N ∧ ∀ k : ℕ, N₀ ≤ k → k ≤ N → u k ≤ u Ndef lowRecordFrom (N₀ N : ℕ) : Prop :=  N₀ ≤ N ∧ ∀ k : ℕ, N₀ ≤ k → k ≤ N → u N ≤ u k
Existence on finite intervals:
leanlemma exists_highRecordFrom    (N₀ N : ℕ) (hN : N₀ ≤ N) :  ∃ R : ℕ, N₀ ≤ R ∧ R ≤ N ∧ highRecordFrom N₀ R
leanlemma exists_lowRecordFrom    (N₀ N : ℕ) (hN : N₀ ≤ N) :  ∃ R : ℕ, N₀ ≤ R ∧ R ≤ N ∧ lowRecordFrom N₀ R
Proof sketch: take a maximizer/minimizer of u on Finset.Icc N₀ N.

3.2 Backward sqrt bands
Use half-open bands to match the kernel windows.
leandef sqrtBackBand (N : ℕ) (s t : ℝ) : Finset ℕ :=  (Finset.Icc 1 N).filter    (fun k : ℕ =>      s < Real.sqrt (N : ℝ) - Real.sqrt (k : ℝ) ∧      Real.sqrt (N : ℝ) - Real.sqrt (k : ℝ) ≤ t)
leandef highOnSqrtInterval    (level : ℝ) (N : ℕ) (s t : ℝ) : Prop :=  ∀ k : ℕ, k ∈ sqrtBackBand N s t → level ≤ u k
leandef lowOnSqrtInterval    (level : ℝ) (N : ℕ) (s t : ℝ) : Prop :=  ∀ k : ℕ, k ∈ sqrtBackBand N s t → u k ≤ level
For records it is better to measure loss from the record value:
leandef highRecordOnSqrtInterval    (N₀ N : ℕ) (loss s t : ℝ) : Prop :=  ∀ k : ℕ,    N₀ ≤ k →    k ∈ sqrtBackBand N s t →      u N - loss ≤ u k
leandef lowRecordOnSqrtInterval    (N₀ N : ℕ) (loss s t : ℝ) : Prop :=  ∀ k : ℕ,    N₀ ≤ k →    k ∈ sqrtBackBand N s t →      u k ≤ u N + loss

4. Error bookkeeping in sqrt shells
This is the key replacement for the false o(1) finite-renewal residual.
Define a shell index:
leandef sqrtShell (j : ℕ) : Finset ℕ :=  (Finset.Icc (j ^ 2) ((j + 1) ^ 2)).filter    (fun n : ℕ => 1 ≤ n)
Define an explicit shell error dominating all one-step record pullback errors for n in shell j.
leannoncomputable def recordPullErrorShell (j : ℕ) : ℝ :=  K₀ * Real.log ((j : ℝ) + 3) / (((j : ℝ) + 1) ^ 2)    + K₁ * Real.exp (-K₂ * (j : ℝ))
The constants come from:


|kernelMass n - 1| ≤ A log n / n;


boundaryTerm n;


fixed-window convergence errors after choosing large N₀;


tail errors, chosen once below the final epsilon.


Brick the following:
leantheorem recordPullErrorShell_nonneg :  ∀ j : ℕ, 0 ≤ recordPullErrorShell j
leantheorem summable_recordPullErrorShell :  Summable recordPullErrorShell
leantheorem record_one_step_error_le_shell    {N₀ n : ℕ}    (hn : N₀ ≤ n)    (hj : n ∈ sqrtShell j) :  oneStepRecordPullError N₀ n ≤ recordPullErrorShell j
Proof sketch: log n / n becomes O(log j / j²), which is summable. The boundary term is exponentially small in j.
This is the main reason the record route closes while the fixed-block o(1) renewal route does not.

5. Fixed kernel-bin package for expansion
Choose a compact positive kernel window in sqrt-drop coordinates. It is convenient to start from an m/√n window and then translate to sqrt-drop.
Pick numbers:


$$0 < r_0 < r_1$$


in the m/√n coordinate, and let the corresponding sqrt-drop window be roughly:


$$A=\frac{r_0}{2},\qquad B=\frac{r_1}{2}.$$


Use small margins to absorb the sqrt_diff_window_approx.
5.1 Positive mass in finitely many bins
leanstructure KernelBinData where  J : ℕ  left right : ℕ → ℝ  hJ_pos : 0 < J  hleft_nonneg : ∀ i ∈ Finset.range J, 0 ≤ left i  hleft_lt_right : ∀ i ∈ Finset.range J, left i < right i  hchain :    ∀ i ∈ Finset.range (J - 1), right i = left (i + 1)  hfirst_pos : 0 < left 0  hmass_pos :    ∃ μ : ℝ, 0 < μ ∧      ∀ i ∈ Finset.range J,        ∀ᶠ n : ℕ in Filter.atTop,          μ ≤ kernelWindow (left i) (right i) n
The construction is from erdos_kernel_window, taking a finite partition of a fixed interval [r₀,r₁] where the density is positive.

5.2 Sqrt-drop translation
leantheorem m_window_to_sqrt_drop_window    {α β A B : ℝ}    (hα : 0 < α) (hαβ : α < β)    (hA : A < α / 2)    (hB : β / 2 < B) :  ∀ᶠ n : ℕ in Filter.atTop,    ∀ m : ℕ,      α * Real.sqrt (n : ℝ) < (m : ℝ) →      (m : ℝ) ≤ β * Real.sqrt (n : ℝ) →      A < Real.sqrt (n : ℝ) -            Real.sqrt ((n - m : ℕ) : ℝ) ∧      Real.sqrt (n : ℝ) -            Real.sqrt ((n - m : ℕ) : ℝ) ≤ B
Proof sketch: use sqrt_diff_window_approx:


$$\sqrt n-\sqrt{n-m}
=
\frac{m}{2\sqrt n}+O(1/\sqrt n).$$



5.3 Local monotone fill
This is where p-monotonicity enters.
leantheorem u_local_lower_from_monotone    {n r : ℕ} (hn : 1 ≤ n) :  u (n + r)    ≥ ((n + r : ℝ) / (n : ℝ)) *        Real.exp          (-C * (Real.sqrt (n + r : ℝ) -                 Real.sqrt (n : ℝ))) *        u n
Then the additive, bounded version:
leantheorem u_local_forward_fill    (hupper : ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in Filter.atTop, u n ≤ M) :  ∀ ε > 0, ∃ h > 0,    ∀ᶠ n : ℕ in Filter.atTop,      ∀ r : ℕ,        (r : ℝ) ≤ h * Real.sqrt (n : ℝ) →          u n - ε ≤ u (n + r)
Proof sketch: the multiplier in u_local_lower_from_monotone is 1 - O(r/√n). Use eventual upper boundedness to convert multiplicative loss into additive loss.
No other estimate on p(n+r)/p(n) is needed.

6. One-step record pullback
This is the main high-record brick.
leantheorem high_record_pulls_back_each_bin    (hupper : ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in Filter.atTop, u n ≤ M)    (hbins : KernelBinData)    :  ∃ μ : ℝ, 0 < μ ∧    ∀ᶠ N₀ : ℕ in Filter.atTop,      ∀ N n : ℕ,        highRecordFrom N₀ N →        N₀ ≤ n → n ≤ N →        u N - L ≤ u n →          ∀ i ∈ Finset.range hbins.J,            ∃ m : ℕ,              m ∈ Finset.Icc 1 (n - 1) ∧              hbins.left i * Real.sqrt (n : ℝ) < (m : ℝ) ∧              (m : ℝ) ≤ hbins.right i * Real.sqrt (n : ℝ) ∧              u N - (L + oneStepRecordPullError N₀ n / μ) ≤                u (n - m)
Proof sketch: use u_recurrence at n. Since N is a high record on [N₀,N], every large predecessor satisfies u (n-m) ≤ u N. If an entire bin were below the claimed level, the weighted average would lose at least μ * loss. The only things that can offset this are kernelMass n - 1, boundaryTerm n, and the chosen tail/window errors, all collected in oneStepRecordPullError.
The low-record analogue:
leantheorem low_record_pulls_back_each_bin    (hlower : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, c ≤ u n)    (hbins : KernelBinData)    :  ∃ μ : ℝ, 0 < μ ∧    ∀ᶠ N₀ : ℕ in Filter.atTop,      ∀ N n : ℕ,        lowRecordFrom N₀ N →        N₀ ≤ n → n ≤ N →        u n ≤ u N + L →          ∀ i ∈ Finset.range hbins.J,            ∃ m : ℕ,              m ∈ Finset.Icc 1 (n - 1) ∧              hbins.left i * Real.sqrt (n : ℝ) < (m : ℝ) ∧              (m : ℝ) ≤ hbins.right i * Real.sqrt (n : ℝ) ∧              u (n - m) ≤                u N + (L + oneStepRecordPullError N₀ n / μ)
For the low side, all predecessors are bounded below by the low record.

7. From bin pullback to interval expansion
Choose the bin mesh fine enough and the monotone-fill length large enough that points found in adjacent bins fill the gaps in sqrt-coordinate.
7.1 One-point expansion
leantheorem high_record_point_expands    (hupper : ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in Filter.atTop, u n ≤ M)    :  ∃ A B : ℝ, 0 < A ∧ A < B ∧    ∀ εfill > 0, ∃ N₀ : ℕ,      ∀ N n : ℕ,        highRecordFrom N₀ N →        N₀ ≤ n → n ≤ N →        u N - L ≤ u n →          highRecordOnSqrtInterval            N₀ n            (L + oneStepRecordPullError N₀ n + εfill)            A B
Important: the center of the resulting band is n, not the original record N.
Proof sketch: apply high_record_pulls_back_each_bin to get one high predecessor in every small m/√n bin. Translate each bin to a sqrt-drop bin. Use u_local_forward_fill to fill between adjacent found predecessors. The half-open convention makes the bins disjoint and avoids endpoint singleton corrections.
Low analogue:
leantheorem low_record_point_expands    (hlower : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, c ≤ u n)    :  ∃ A B : ℝ, 0 < A ∧ A < B ∧    ∀ εfill > 0, ∃ N₀ : ℕ,      ∀ N n : ℕ,        lowRecordFrom N₀ N →        N₀ ≤ n → n ≤ N →        u n ≤ u N + L →          lowRecordOnSqrtInterval            N₀ n            (L + oneStepRecordPullError N₀ n + εfill)            A B

7.2 Band expansion
To iterate, translate bands centered at interior points back to a band centered at the record.
leantheorem high_record_band_expands    {A B : ℝ} (hA : 0 < A) (hAB : A < B) :  ∀ ρ > 0, ρ < (B - A) / 4 →    ∃ N₀ : ℕ,      ∀ N : ℕ, highRecordFrom N₀ N →      ∀ L s t : ℝ,        0 ≤ s → s < t →        highRecordOnSqrtInterval N₀ N L s t →          highRecordOnSqrtInterval            N₀ N            (L + bandStepError N₀ N s t + ρ)            (s + A + ρ)            (t + B - ρ)
Low analogue:
leantheorem low_record_band_expands    {A B : ℝ} (hA : 0 < A) (hAB : A < B) :  ∀ ρ > 0, ρ < (B - A) / 4 →    ∃ N₀ : ℕ,      ∀ N : ℕ, lowRecordFrom N₀ N →      ∀ L s t : ℝ,        0 ≤ s → s < t →        lowRecordOnSqrtInterval N₀ N L s t →          lowRecordOnSqrtInterval            N₀ N            (L + bandStepError N₀ N s t + ρ)            (s + A + ρ)            (t + B - ρ)
Proof sketch: if k lies in the current band relative to N, and j lies in the expansion band behind k, then


$$\sqrt N-\sqrt j
=
(\sqrt N-\sqrt k)+(\sqrt k-\sqrt j).$$


The margin ρ absorbs lattice rounding and the half-open boundaries.

8. Percolation on the sqrt lattice
Let


$$A' = A+\rho,\qquad B' = B-\rho.$$


Choose ρ so 0 < A' < B'.
Define reachability:
leandef sqrtReach (A B : ℝ) (K : ℕ) (x : ℝ) : Prop :=  ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧ (k : ℝ) * A < x ∧ x ≤ (k : ℝ) * B
Finite reach:
leanlemma sqrtReach_step    {A B x : ℝ} {K : ℕ}    (h : sqrtReach A B K x) :  sqrtReach A B (K + 1) x
Tail cover by arbitrary many steps:
leantheorem sqrtReach_tail_cover    {A B : ℝ} (hA : 0 < A) (hAB : A < B) :  ∃ K₀ : ℕ, ∀ x : ℝ,    (K₀ : ℝ) * A < x →      ∃ K : ℕ, K₀ ≤ K ∧        (K : ℝ) * A < x ∧ x ≤ (K : ℝ) * B
Proof sketch: intervals (K A, K B] overlap once (K+1)A ≤ K B, i.e. once K ≥ A/(B-A).
But do not use this with exponentially growing degradation from arbitrary near-limsup points. Use it only together with the summable shell errors in the record proof.

9. Summable-loss record percolation
This is the corrected version of “interval percolation covers a tail.”
leantheorem high_record_covers_tail    (hupper : ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in Filter.atTop, u n ≤ M)    :  ∀ ε > 0, ∃ N₀ : ℕ, ∀ N : ℕ,    highRecordFrom N₀ N →      ∀ k : ℕ, N₀ ≤ k → k ≤ N →        u N - ε ≤ u k
Proof sketch:


Choose A < B and ρ from high_record_point_expands.


Choose N₀ so the tail sum of recordPullErrorShell over all shells after sqrt N₀ is < ε/4.


Start from the record point N, which is high with loss 0.


Apply point expansion and then band expansion repeatedly.


The union of reached bands covers every k ∈ [N₀,N] by sqrtReach_tail_cover.


The total loss accumulated along any chain is bounded by the shell-error tail plus the chosen fill margins, hence < ε.


Low side:
leantheorem low_record_covers_tail    (hlower : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, c ≤ u n)    :  ∀ ε > 0, ∃ N₀ : ℕ, ∀ N : ℕ,    lowRecordFrom N₀ N →      ∀ k : ℕ, N₀ ≤ k → k ≤ N →        u k ≤ u N + ε
Same proof, with inequalities reversed.
This is the place where the R6 bounded-depth statement must be replaced. The proof may require arbitrarily many expansion rounds, but the loss is summable in sqrt shells, so it remains bounded by the chosen ε.

10. Tail oscillation collapse
Define finite-interval oscillation:
leannoncomputable def intervalMaxU (N₀ N : ℕ) : ℝ :=  Finset.sup' (Finset.Icc N₀ N) ?nonempty unoncomputable def intervalMinU (N₀ N : ℕ) : ℝ :=  Finset.inf' (Finset.Icc N₀ N) ?nonempty unoncomputable def intervalOscU (N₀ N : ℕ) : ℝ :=  intervalMaxU N₀ N - intervalMinU N₀ N
The record-cover lemmas imply:
leantheorem intervalOsc_tends_zero_from_record_cover    (hhigh :      ∀ ε > 0, ∃ N₀ : ℕ, ∀ N : ℕ,        highRecordFrom N₀ N →          ∀ k : ℕ, N₀ ≤ k → k ≤ N → u N - ε ≤ u k)    (hlow :      ∀ ε > 0, ∃ N₀ : ℕ, ∀ N : ℕ,        lowRecordFrom N₀ N →          ∀ k : ℕ, N₀ ≤ k → k ≤ N → u k ≤ u N + ε) :  ∀ ε > 0, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →    intervalOscU N₀ N ≤ ε
Proof sketch: take a high record H and low record L in [N₀,N]. The high-cover lemma applied to k = L gives


$$u_H - ε \le u_L.$$


The low-cover lemma applied to k = H gives


$$u_H \le u_L + ε.$$


Thus max minus min is at most ε up to harmless 2ε bookkeeping.
Then:
leantheorem u_cauchy_atTop_from_intervalOsc :  (∀ ε > 0, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →      intervalOscU N₀ N ≤ ε) →  CauchySeq u
and since ℝ is complete:
leantheorem u_tendsto_exists_from_intervalOsc :  (∀ ε > 0, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →      intervalOscU N₀ N ≤ ε) →  ∃ L : ℝ, Filter.Tendsto u Filter.atTop (𝓝 L)
Finally:
leantheorem u_liminf_eq_limsup :  Filter.liminf u Filter.atTop = Filter.limsup u Filter.atTop
leantheorem erdos_partition_limit_exists :  ∃ a : ℝ, 0 < a ∧ Filter.Tendsto u Filter.atTop (𝓝 a)
The positivity of a comes from the already accepted lower barrier:
leanu_liminf_positive :  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, c ≤ u n

11. Barrier split bookkeeping
Your check of the monotonicity directions is correct.
Let
leanHplus n  = upperBarrier A E n   -- increasingHminus n = lowerBarrier A E n   -- decreasings n      = barrierSlack E nK n      = kernelMass nW n      = kernelWindow a₀ b₀ n
Assume eventually:
lean|K n - 1| ≤ eta nμ ≤ W neta n ≤ (γ * μ / 4) * s n
and on the fixed window:
leanHplus n - Hplus (n - m) ≥ γ * s nHminus (n - m) - Hminus n ≥ γ * s n
Also globally:
leanHplus (n - m) ≤ Hplus nHminus n ≤ Hminus (n - m)
because Hplus is increasing and Hminus is decreasing.
Upper barrier inequality
leanlemma upperBarrier_superharmonic_from_split :  (∑ m ∈ Finset.Icc 1 (n - 1),      erdosWeight n m * Hplus (n - m))    ≤ Hplus n - (γ * μ / 2) * s n
Proof algebra:


$$\begin{aligned}
\sum_m W_m H_+(n-m)
&=
H_+(n)\sum_m W_m
-
\sum_m W_m\bigl(H_+(n)-H_+(n-m)\bigr)\\
&\le
H_+(n)(1+\eta_n)-\gamma s_n\,W(n)\\
&\le
H_+(n)+\eta_n-\gamma\mu s_n\\
&\le
H_+(n)-\frac{\gamma\mu}{2}s_n.
\end{aligned}$$


Use Hplus n ≤ 1 eventually. No tail problem occurs: outside the chosen window the difference is merely nonnegative, and inside the window it has the fixed drift.
Lower barrier inequality
Let Hminus n ≤ H0 eventually.
leanlemma lowerBarrier_subharmonic_from_split :  Hminus n + (γ * μ / 2) * s n    ≤  (∑ m ∈ Finset.Icc 1 (n - 1),      erdosWeight n m * Hminus (n - m))
Proof algebra:


$$\begin{aligned}
\sum_m W_m H_-(n-m)
&=
H_-(n)\sum_m W_m
+
\sum_m W_m\bigl(H_-(n-m)-H_-(n)\bigr)\\
&\ge
H_-(n)(1-\eta_n)+\gamma s_n\,W(n)\\
&\ge
H_-(n)-H_0\eta_n+\gamma\mu s_n\\
&\ge
H_-(n)+\frac{\gamma\mu}{2}s_n.
\end{aligned}$$


Here the far tail m close to n only helps, since Hminus (n-m) ≥ Hminus n. Boundedness of Hminus is needed only to control the possible mass deficit term Hminus n * eta n.
So the barrier package remains sound.

12. Half-open windows
Keep the convention


$$(a\sqrt n,\ b\sqrt n].$$


It matters in three places:


finite bin partitions of the kernel window are exactly additive;


summatory_diff_eq_window_sum matches the half-open convention;


the record-percolation bands avoid duplicate boundary points.


Analytically closed versus half-open is irrelevant, but in Lean the half-open convention prevents singleton endpoint terms from appearing in every expansion step.

You are correct: R6 Lemma 20 is false, and the sin (√j) example is exactly the obstruction. The fixed-delay approximate-renewal theorem with only residual → 0 proves, at best, local flatness on bounded block ranges. It cannot rule out slow oscillations.
The corrected picture is:


$$\text{summable residual finite-renewal theorem is true,}$$


but


$$\text{the fixed-mesh `blockU` residual in this problem is not summable.}$$


So repair (a) is mathematically valid but not the right brick for this Erdős route. The direct route must be stated as a record-extrema interval-percolation theorem, and the finite-depth expansion lemma should be used only as a local brick. A finite-depth statement alone still does not prove convergence unless it is upgraded to a tail-cover statement.

1. Repair (a): summable residuals
The corrected abstract theorem should be stated with summable absolute residuals.
leannamespace AnalyticCombinatorics.Renewalnoncomputable def finiteRenewalResidual    (R : ℕ) (p v : ℕ → ℝ) (j : ℕ) : ℝ :=  v j - ∑ r ∈ Finset.range R, p r * v (j - (r + 1))theorem finite_renewal_summable_residual_tendsto    {R : ℕ} {p v eps : ℕ → ℝ}    (hR : 2 ≤ R)    (hp_nonneg :      ∀ r : ℕ, r ∈ Finset.range R → 0 ≤ p r)    (hp_mass :      (∑ r ∈ Finset.range R, p r) = 1)    (hp_adjacent :      ∃ r : ℕ,        r ∈ Finset.range R ∧        r + 1 ∈ Finset.range R ∧        0 < p r ∧        0 < p (r + 1))    (hv_bdd :      ∃ M : ℝ, ∀ j : ℕ, |v j| ≤ M)    (heps_nonneg :      ∀ j : ℕ, 0 ≤ eps j)    (heps_summable :      Summable eps)    (hrec :      ∀ᶠ j : ℕ in Filter.atTop,        |finiteRenewalResidual R p v j| ≤ eps j) :    ∃ L : ℝ, Filter.Tendsto v Filter.atTop (𝓝 L)
Proof skeleton:


Convert the scalar recurrence into a finite-dimensional companion system
leannoncomputable def renewalState    (R : ℕ) (v : ℕ → ℝ) (j : ℕ) : Fin R → ℝ :=  fun i => v (j - i)


Define the stochastic companion operator. The first row is p 0, ..., p (R - 1), and the remaining rows shift coordinates.


From hp_adjacent, prove primitivity/Doeblin contraction:
leantheorem primitive_companion_osc_contract :  ∃ L : ℕ, ∃ theta : ℝ,    0 < theta ∧ theta < 1 ∧    ∀ x : Fin R → ℝ,      osc (companionPower R p L x)        ≤ (1 - theta) * osc x


The residual enters as an additive perturbation:
leantheorem renewal_state_contract_with_error :  ∃ L : ℕ, ∃ theta A : ℝ,    0 < theta ∧ theta < 1 ∧ 0 ≤ A ∧    ∀ᶠ j : ℕ in Filter.atTop,      osc (renewalState R v (j + L))        ≤ (1 - theta) * osc (renewalState R v j)          + A * ∑ i ∈ Finset.Icc j (j + L), eps i


Since eps is summable, the moving finite-window tail
leanfun j => ∑ i ∈ Finset.Icc j (j + L), eps i
tends to 0.


Therefore osc (renewalState R v j) → 0.


A companion invariant linear functional, for example the stationary left eigenvector, changes by a summable amount; hence it converges. Since the state oscillation tends to zero, every coordinate, in particular v j, converges.


This excludes v j = sin (Real.sqrt j). Its residual is of order


$$\frac{|\cos(\sqrt j)|}{\sqrt j}$$


on infinitely many long ranges, so it cannot be bounded eventually by a summable nonnegative sequence.
For the Erdős application, however, this repair does not apply. For fixed block width h, the blockU residual contains the within-block oscillation error. Even after boundedness and local monotonicity, that error is O(h) per block. For fixed h, the sequence fun j => O(h) is not summable. Taking h smaller only makes a smaller nonsummable constant. Letting h = h j → 0 destroys the fixed finite-renewal theorem.
So repair (a) is true but not useful for the current coefficient recurrence.

2. Repair (b): finite interval-percolation must be strengthened
The finite-depth statement


$$\eta \mapsto \kappa^K \eta$$


is useful only for a fixed bounded sqrt-distance. It does not by itself prove convergence, because K grows with the sqrt-distance between high and low witnesses. The same slow-oscillation obstruction reappears: a sequence may be locally flat on every bounded sqrt-window while still oscillating on an unbounded sqrt-scale.
The correct direct route is:


prove local finite-depth interval expansion;


use it to prove record tail cover;


derive tail oscillation collapse from high-record and low-record cover.


The record-tail cover is the actual convergence brick.

3. Exact definitions
Work in:
leannamespace AnalyticCombinatorics.Ch8.Partitions.Erdos
Records
leandef highRecordFrom (N₀ N : ℕ) : Prop :=  N₀ ≤ N ∧    ∀ k : ℕ, N₀ ≤ k → k ≤ N → u k ≤ u Ndef lowRecordFrom (N₀ N : ℕ) : Prop :=  N₀ ≤ N ∧    ∀ k : ℕ, N₀ ≤ k → k ≤ N → u N ≤ u k
Finite existence:
leanlemma exists_highRecordFrom    (N₀ N : ℕ) (hN : N₀ ≤ N) :  ∃ R : ℕ,    N₀ ≤ R ∧ R ≤ N ∧ highRecordFrom N₀ R
leanlemma exists_lowRecordFrom    (N₀ N : ℕ) (hN : N₀ ≤ N) :  ∃ R : ℕ,    N₀ ≤ R ∧ R ≤ N ∧ lowRecordFrom N₀ R
Proof sketch: take a maximizer/minimizer of u on Finset.Icc N₀ N.

Sqrt drop and half-open bands
leannoncomputable def sqrtDrop (N k : ℕ) : ℝ :=  Real.sqrt (N : ℝ) - Real.sqrt (k : ℝ)def inSqrtBackBand (N₀ N : ℕ) (s t : ℝ) (k : ℕ) : Prop :=  N₀ ≤ k ∧ k ≤ N ∧ s < sqrtDrop N k ∧ sqrtDrop N k ≤ t
The half-open convention is (s,t], matching your kernel windows.
leandef highOnSqrtInterval    (N₀ N : ℕ) (level s t : ℝ) : Prop :=  ∀ k : ℕ,    inSqrtBackBand N₀ N s t k →      level ≤ u kdef lowOnSqrtInterval    (N₀ N : ℕ) (level s t : ℝ) : Prop :=  ∀ k : ℕ,    inSqrtBackBand N₀ N s t k →      u k ≤ level
Centered version for one-step expansion from an interior point:
leandef inCenteredSqrtBand (N₀ q : ℕ) (s t : ℝ) (k : ℕ) : Prop :=  N₀ ≤ k ∧ k ≤ q ∧ s < sqrtDrop q k ∧ sqrtDrop q k ≤ tdef highOnCenteredSqrtInterval    (N₀ q : ℕ) (level s t : ℝ) : Prop :=  ∀ k : ℕ,    inCenteredSqrtBand N₀ q s t k →      level ≤ u kdef lowOnCenteredSqrtInterval    (N₀ q : ℕ) (level s t : ℝ) : Prop :=  ∀ k : ℕ,    inCenteredSqrtBand N₀ q s t k →      u k ≤ level

4. Local monotone fill
This is exactly where p-monotonicity is used.
leantheorem u_local_lower_from_monotone    {n r : ℕ} (hn : 1 ≤ n) :  u (n + r)    ≥ ((n + r : ℝ) / (n : ℝ)) *        Real.exp          (-C * (Real.sqrt ((n + r : ℕ) : ℝ) -                 Real.sqrt (n : ℝ))) *        u n
High values fill forward:
leantheorem u_local_high_forward_fill    (hupper :      ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in Filter.atTop, u n ≤ M) :  ∀ ε > 0, ∃ h > 0,    ∀ᶠ n : ℕ in Filter.atTop,      ∀ r : ℕ,        (r : ℝ) ≤ h * Real.sqrt (n : ℝ) →          u n - ε ≤ u (n + r)
Low values fill backward:
leantheorem u_local_low_backward_fill    (hupper :      ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in Filter.atTop, u n ≤ M) :  ∀ ε > 0, ∃ h > 0,    ∀ᶠ n : ℕ in Filter.atTop,      ∀ r : ℕ,        (r : ℝ) ≤ h * Real.sqrt (n : ℝ) →          u (n + r) ≤ L →            u n ≤ L + ε
The second follows by rearranging the same monotone lower bound:


$$u(n+r)\ge q(n,r)u(n), \qquad q(n,r)\to 1,$$


so u n ≤ q⁻¹ u (n+r), and boundedness converts the multiplicative loss into an additive loss.
No stronger estimate on p(n+r)/p(n) is needed.

5. One-step record pullback
Use a fixed kernel window (α√n, β√n] with positive mass.
leannoncomputable def kernelWindow (α β : ℝ) (n : ℕ) : ℝ :=  ∑ m ∈ Finset.Icc 1 (n - 1),    if α * Real.sqrt (n : ℝ) < (m : ℝ) ∧       (m : ℝ) ≤ β * Real.sqrt (n : ℝ)    then erdosWeight n m    else 0
One-step high pullback:
leantheorem high_record_one_step_pullback    (hupper :      ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in Filter.atTop, u n ≤ M)    {α β μ : ℝ}    (hα : 0 < α) (hαβ : α < β) (hμ : 0 < μ)    (hmass :      ∀ᶠ n : ℕ in Filter.atTop,        μ ≤ kernelWindow α β n)    {Err : ℕ → ℝ}    (hErr_nonneg : ∀ n : ℕ, 0 ≤ Err n)    (hErr_controls :      ∀ᶠ n : ℕ in Filter.atTop,        recordHighPullDefect n ≤ Err n) :  ∀ᶠ N₀ : ℕ in Filter.atTop,    ∀ N q η : ℕ × ℕ × ℝ,      highRecordFrom N₀ N →      N₀ ≤ q → q ≤ N →      u N - η ≤ u q →        ∃ m : ℕ,          m ∈ Finset.Icc 1 (q - 1) ∧          α * Real.sqrt (q : ℝ) < (m : ℝ) ∧          (m : ℝ) ≤ β * Real.sqrt (q : ℝ) ∧          u N - ((η + Err q) / μ) ≤ u (q - m)
I would avoid the tuple binder in actual Lean and write it as:
lean  ∀ᶠ N₀ : ℕ in Filter.atTop,    ∀ N q : ℕ, ∀ η : ℝ,      ...
Low pullback:
leantheorem low_record_one_step_pullback    (hlower :      ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, c ≤ u n)    {α β μ : ℝ}    (hα : 0 < α) (hαβ : α < β) (hμ : 0 < μ)    (hmass :      ∀ᶠ n : ℕ in Filter.atTop,        μ ≤ kernelWindow α β n)    {Err : ℕ → ℝ}    (hErr_nonneg : ∀ n : ℕ, 0 ≤ Err n)    (hErr_controls :      ∀ᶠ n : ℕ in Filter.atTop,        recordLowPullDefect n ≤ Err n) :  ∀ᶠ N₀ : ℕ in Filter.atTop,    ∀ N q : ℕ, ∀ η : ℝ,      lowRecordFrom N₀ N →      N₀ ≤ q → q ≤ N →      u q ≤ u N + η →        ∃ m : ℕ,          m ∈ Finset.Icc 1 (q - 1) ∧          α * Real.sqrt (q : ℝ) < (m : ℝ) ∧          (m : ℝ) ≤ β * Real.sqrt (q : ℝ) ∧          u (q - m) ≤ u N + ((η + Err q) / μ)
Proof sketch: use u_recurrence at q. Since N is a high record, every predecessor in [N₀,N] is at most u N; since N is a low record, every predecessor is at least u N. If the whole positive-mass window failed to contain a sufficiently high/low predecessor, the weighted average would contradict u q being close to the record. The errors are total-mass defect, boundary, and small tails.
Important: this one-step pointwise lemma has a loss factor 1 / μ. Therefore it is safe for fixed finite depth, but not by itself for unbounded pullback chains.

6. Fixed-depth interval expansion
Package one-step pullback plus monotone fill into interval expansion.
leanstructure ExpansionConstants where  A B : ℝ  hA : 0 < A  hAB : A < B  kappa : ℝ  hkappa : 1 ≤ kappa
High interval expansion:
leantheorem high_interval_expands_once    (hupper :      ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in Filter.atTop, u n ≤ M) :  ∃ data : ExpansionConstants,    ∀ εfill > 0, ∃ N₀ : ℕ,      ∀ N : ℕ, ∀ η s t : ℝ,        highRecordFrom N₀ N →        0 ≤ s → s < t →        highOnSqrtInterval N₀ N (u N - η) s t →          highOnSqrtInterval            N₀ N            (u N - (data.kappa * η + εfill))            (s + data.A)            (t + data.B)
Low interval expansion:
leantheorem low_interval_expands_once    (hupper :      ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in Filter.atTop, u n ≤ M)    (hlower :      ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, c ≤ u n) :  ∃ data : ExpansionConstants,    ∀ εfill > 0, ∃ N₀ : ℕ,      ∀ N : ℕ, ∀ η s t : ℝ,        lowRecordFrom N₀ N →        0 ≤ s → s < t →        lowOnSqrtInterval N₀ N (u N + η) s t →          lowOnSqrtInterval            N₀ N            (u N + (data.kappa * η + εfill))            (s + data.A)            (t + data.B)
Proof sketch: apply one-step pullback to points in the current band; translate the m/√q window to a sqrt-drop window using sqrt_diff_window_approx; use local fill to bridge gaps between adjacent subwindows. The half-open convention makes the band decomposition exact.
This is the precise version of the “η becomes κ η” statement. κ is usually 1 / μ plus harmless slack, not necessarily 2.

7. Finite-depth percolation
Define reachability by repeated Minkowski addition of (A,B].
leandef sqrtReach (A B : ℝ) (K : ℕ) (x : ℝ) : Prop :=  (K : ℝ) * A < x ∧ x ≤ (K : ℝ) * B
For one fixed target scale:
leantheorem sqrtReach_fixed_cover    {A B S : ℝ} (hA : 0 < A) (hAB : A < B) (hS : 0 ≤ S) :  ∃ Kmax : ℕ,    ∀ x : ℝ,      A < x → x ≤ S →        ∃ K : ℕ,          1 ≤ K ∧ K ≤ Kmax ∧ sqrtReach A B K x
Proof sketch: intervals (K A, K B] eventually overlap once (K+1)A ≤ K B. For a bounded interval [A,S], finitely many such intervals cover.
This gives fixed-gap record cover.
High fixed-gap cover:
leantheorem high_record_fixed_sqrt_gap_cover    (hupper :      ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in Filter.atTop, u n ≤ M) :  ∀ ε > 0, ∀ S > 0,    ∃ N₀ : ℕ,      ∀ N k : ℕ,        highRecordFrom N₀ N →        N₀ ≤ k → k ≤ N →        sqrtDrop N k ≤ S →          u N - ε ≤ u k
Low fixed-gap cover:
leantheorem low_record_fixed_sqrt_gap_cover    (hupper :      ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in Filter.atTop, u n ≤ M)    (hlower :      ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, c ≤ u n) :  ∀ ε > 0, ∀ S > 0,    ∃ N₀ : ℕ,      ∀ N k : ℕ,        lowRecordFrom N₀ N →        N₀ ≤ k → k ≤ N →        sqrtDrop N k ≤ S →          u k ≤ u N + ε
These statements are true and useful, but they do not imply convergence. They only rule out oscillation on bounded sqrt-distance scales.
They do not exclude a sin (√j)-type slow oscillation in the block variable, because high and low witnesses may be separated by an unbounded sqrt-distance.

8. The actual convergence brick: record tail cover
The theorem that does imply convergence is the following.
High tail cover:
leantheorem high_record_covers_tail    (hupper :      ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in Filter.atTop, u n ≤ M) :  ∀ ε > 0, ∃ N₀ : ℕ,    ∀ N : ℕ,      highRecordFrom N₀ N →        ∀ k : ℕ,          N₀ ≤ k → k ≤ N →            u N - ε ≤ u k
Low tail cover:
leantheorem low_record_covers_tail    (hupper :      ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in Filter.atTop, u n ≤ M)    (hlower :      ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, c ≤ u n) :  ∀ ε > 0, ∃ N₀ : ℕ,    ∀ N : ℕ,      lowRecordFrom N₀ N →        ∀ k : ℕ,          N₀ ≤ k → k ≤ N →            u k ≤ u N + ε
This is the precise replacement for the false finite-renewal theorem.
How to prove it: not by the fixed finite-depth expansion alone. You need the Erdős block bookkeeping here. There are two viable ways to brick this:
Route 8A: summable shell-error record propagation
Define sqrt shells:
leandef sqrtShell (j : ℕ) : Finset ℕ :=  (Finset.Icc (j ^ 2) ((j + 1) ^ 2)).filter    (fun n : ℕ => 1 ≤ n)
Define a shell error dominating total-mass defect and boundary:
leannoncomputable def recordShellErr (j : ℕ) : ℝ :=  A₀ * Real.log ((j : ℝ) + 3) / (((j : ℝ) + 1) ^ 2)    + A₁ * Real.exp (-A₂ * (j : ℝ))
Brick:
leantheorem recordShellErr_nonneg :  ∀ j : ℕ, 0 ≤ recordShellErr jtheorem summable_recordShellErr :  Summable recordShellErr
Then prove the actual multi-step record theorem directly:
leantheorem high_record_tail_cover_from_shell_errors    (hupper :      ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in Filter.atTop, u n ≤ M)    (hshell :      Summable recordShellErr) :  ∀ ε > 0, ∃ N₀ : ℕ,    ∀ N : ℕ,      highRecordFrom N₀ N →        ∀ k : ℕ,          N₀ ≤ k → k ≤ N →            u N - ε ≤ u k
Low analogue:
leantheorem low_record_tail_cover_from_shell_errors    (hupper :      ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in Filter.atTop, u n ≤ M)    (hlower :      ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, c ≤ u n)    (hshell :      Summable recordShellErr) :  ∀ ε > 0, ∃ N₀ : ℕ,    ∀ N : ℕ,      lowRecordFrom N₀ N →        ∀ k : ℕ,          N₀ ≤ k → k ≤ N →            u k ≤ u N + ε
The proof should not amplify pointwise losses by κ^K. It should use record averaging: iterating the recurrence along kernel paths accumulates shell defects additively, and summability makes the tail loss arbitrarily small.
Route 8B: state the averaged path-spread lemma explicitly
Define a path of backward jumps:
leandef BackwardPath (N₀ N : ℕ) (path : List ℕ) : Prop :=  path.head? = some N ∧  (∀ q ∈ path, N₀ ≤ q ∧ q ≤ N) ∧  path.Chain' (fun q r => r < q)
Define shell loss along a path:
leannoncomputable def pathShellLoss (path : List ℕ) : ℝ :=  ∑ q ∈ path.toFinset, recordShellErr ⌊Real.sqrt (q : ℝ)⌋₊
Then the averaged spread brick:
leantheorem high_record_path_spread    (hupper :      ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in Filter.atTop, u n ≤ M) :  ∀ ε > 0, ∃ N₀ : ℕ,    ∀ N k : ℕ,      highRecordFrom N₀ N →      N₀ ≤ k → k ≤ N →        ∃ path : List ℕ,          BackwardPath N₀ N path ∧          k ∈ path.toFinset ∧          pathShellLoss path ≤ ε ∧          u N - ε ≤ u k
Low analogue:
leantheorem low_record_path_spread    (hupper :      ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in Filter.atTop, u n ≤ M)    (hlower :      ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, c ≤ u n) :  ∀ ε > 0, ∃ N₀ : ℕ,    ∀ N k : ℕ,      lowRecordFrom N₀ N →      N₀ ≤ k → k ≤ N →        ∃ path : List ℕ,          BackwardPath N₀ N path ∧          k ∈ path.toFinset ∧          pathShellLoss path ≤ ε ∧          u k ≤ u N + ε
This is more work, but it is the morally correct replacement for the false finite-renewal lemma.

9. Final oscillation collapse
Define finite interval extrema.
leannoncomputable def intervalMaxU (N₀ N : ℕ) : ℝ :=  Finset.sup' (Finset.Icc N₀ N) (by    classical    exact Finset.nonempty_Icc.mpr ?_) unoncomputable def intervalMinU (N₀ N : ℕ) : ℝ :=  Finset.inf' (Finset.Icc N₀ N) (by    classical    exact Finset.nonempty_Icc.mpr ?_) unoncomputable def intervalOscU (N₀ N : ℕ) : ℝ :=  intervalMaxU N₀ N - intervalMinU N₀ N
In actual Lean, avoid embedding the proof term in the definition by defining with an explicit default or by making N₀ ≤ N a hypothesis in the lemmas.
Oscillation collapse:
leantheorem intervalOsc_tends_zero_from_record_cover    (hhigh :      ∀ ε > 0, ∃ N₀ : ℕ,        ∀ N : ℕ,          highRecordFrom N₀ N →            ∀ k : ℕ, N₀ ≤ k → k ≤ N →              u N - ε ≤ u k)    (hlow :      ∀ ε > 0, ∃ N₀ : ℕ,        ∀ N : ℕ,          lowRecordFrom N₀ N →            ∀ k : ℕ, N₀ ≤ k → k ≤ N →              u k ≤ u N + ε) :  ∀ ε > 0, ∃ N₀ : ℕ,    ∀ N : ℕ, N₀ ≤ N →      intervalOscU N₀ N ≤ ε
Proof sketch: choose a high record H and a low record L in [N₀,N]. High cover applied to k = L gives


$$u_H - \varepsilon/2 \le u_L.$$


Low cover applied to k = H gives


$$u_H \le u_L + \varepsilon/2.$$


Thus the max-min oscillation is at most ε.
Cauchy/convergence:
leantheorem u_cauchySeq_from_intervalOsc :  (∀ ε > 0, ∃ N₀ : ℕ,    ∀ N : ℕ, N₀ ≤ N →      intervalOscU N₀ N ≤ ε) →  CauchySeq u
leantheorem u_tendsto_exists_from_intervalOsc :  (∀ ε > 0, ∃ N₀ : ℕ,    ∀ N : ℕ, N₀ ≤ N →      intervalOscU N₀ N ≤ ε) →  ∃ L : ℝ, Filter.Tendsto u Filter.atTop (𝓝 L)
Then:
leantheorem u_liminf_eq_limsup :  Filter.liminf u Filter.atTop = Filter.limsup u Filter.atTop
leantheorem erdos_partition_limit_exists :  ∃ a : ℝ, 0 < a ∧ Filter.Tendsto u Filter.atTop (𝓝 a)
The positivity of a uses your accepted lower barrier:
leantheorem u_liminf_positive :  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, c ≤ u n

10. Check against sin (√j)
The repaired statements behave as follows.
For repair (a), sin (√j) is excluded because its residual is not summably dominated.
For finite-depth interval expansion, sin (√j) is not excluded. It is locally flat on every fixed bounded j-window, so a theorem that only covers bounded sqrt-distance cannot force convergence.
For the record-tail-cover theorem, sin (√j) is excluded. Its high records cannot cover the full tail within arbitrary ε; low points remain arbitrarily far behind in the tail.
Thus the correct convergence brick is high_record_covers_tail plus low_record_covers_tail, not merely the finite-depth expansion lemma.

11. Barrier split bookkeeping
Your sign check is right. Here are the exact inequalities to brick.
Let:
leanHplus n  = upperBarrier A E nHminus n = lowerBarrier A E ns n      = barrierSlack E nK n      = kernelMass nW n      = kernelWindow a₀ b₀ n
Assume eventually:
lean|K n - 1| ≤ eta nμ ≤ W neta n ≤ (gamma * μ / 4) * s n0 ≤ eta n0 < μ0 < gamma
and on the fixed window:
leanHplus n - Hplus (n - m) ≥ gamma * s nHminus (n - m) - Hminus n ≥ gamma * s n
Also eventually:
lean0 ≤ Hplus nHplus n ≤ 11 ≤ Hminus nHminus n ≤ HminusMax
Upper barrier
The global monotonicity direction is:
leanHplus (n - m) ≤ Hplus n
because Hplus is increasing.
Then:
leanlemma upperBarrier_superharmonic_from_split :  (∑ m ∈ Finset.Icc 1 (n - 1),      erdosWeight n m * Hplus (n - m))    ≤ Hplus n - (gamma * μ / 2) * s n
Proof algebra:


$$\begin{aligned}
\sum_m W_mH_+(n-m)
&=
H_+(n)\sum_m W_m
-
\sum_m W_m(H_+(n)-H_+(n-m))\\
&\le
H_+(n)K(n)-\gamma s(n) W(n)\\
&\le
H_+(n)(1+\eta(n))-\gamma\mu s(n)\\
&\le
H_+(n)+\eta(n)-\gamma\mu s(n)\\
&\le
H_+(n)-\frac{\gamma\mu}{2}s(n).
\end{aligned}$$


In Lean, the last line only needs eta n ≤ (gamma * μ / 2) * s n; the stronger /4 version gives slack.
The far tail causes no issue. Outside the fixed positive window, the difference Hplus n - Hplus (n-m) is nonnegative, so dropping it is safe.
Lower barrier
The monotonicity direction is:
leanHminus n ≤ Hminus (n - m)
because Hminus is decreasing.
Then:
leanlemma lowerBarrier_subharmonic_from_split :  Hminus n + (gamma * μ / 2) * s n    ≤  (∑ m ∈ Finset.Icc 1 (n - 1),      erdosWeight n m * Hminus (n - m))
Proof algebra:


$$\begin{aligned}
\sum_m W_mH_-(n-m)
&=
H_-(n)\sum_m W_m
+
\sum_m W_m(H_-(n-m)-H_-(n))\\
&\ge
H_-(n)K(n)+\gamma s(n)W(n)\\
&\ge
H_-(n)(1-\eta(n))+\gamma\mu s(n)\\
&\ge
H_-(n)-HminusMax\cdot\eta(n)+\gamma\mu s(n)\\
&\ge
H_-(n)+\frac{\gamma\mu}{2}s(n).
\end{aligned}$$


The far tail m close to n only helps because Hminus (n-m) is larger than Hminus n. Its largeness is harmless; you only need the eventual global bound Hminus n ≤ HminusMax to control the possible mass deficit term.

12. Half-open windows
Keep everything half-open:


$$(a\sqrt n,\ b\sqrt n].$$


This matters formally in exactly these places:
leankernelWindow a b n =  kernelWindow a c n + kernelWindow c b n
for a ≤ c ≤ b, without endpoint corrections.
The same convention also matches:
leanSigma.summatory_diff_eq_window_sum
and prevents singleton terms from appearing in every mesh/percolation split.