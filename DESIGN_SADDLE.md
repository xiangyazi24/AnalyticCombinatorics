# Saddle-Point Method Recon and Architecture

Target: F&S Chapter VIII saddle-point method in Lean 4 / Mathlib v4.29.0, repo
`AnalyticCombinatorics`, no `.lean` edits in this pass.

This recon used local grep plus `lake env lean --stdin` checks. The key local
imports tested were:

```lean
import Mathlib
import AnalyticCombinatorics.Ch4.Analytic.CauchyCoeff
```

## Executive Verdict

There are two very different projects here.

1. **Saddle-point bound**:
   \[
     [z^n] f \le f(r) r^{-n}
   \]
   for power series with nonnegative real coefficients and valid radius
   hypotheses is a **BOUNDED brick**. It can be built on top of the existing
   Cauchy coefficient estimate. The crucial positivity-on-the-circle estimate
   was stdin-checked.

2. **Full saddle-point asymptotic**:
   \[
     [z^n] f \sim
     \frac{f(r_n)}{r_n^n\sqrt{2\pi b(r_n)}}
   \]
   under H-admissibility is a **WALL**. Mathlib has Gaussian integral values
   and dominated-convergence infrastructure, but no general Laplace method, no
   steepest descent theorem, no Hayman/H-admissibility framework, and no moving
   saddle contour machinery. This is comparable to, and probably harder than,
   the transfer-project estimate work.

The bounded win is still mathematically worthwhile: it gives clean, reusable
coefficient bounds and immediate concrete estimates such as
\[
  \frac{1}{n!} \le \frac{e^r}{r^n},\qquad
  \frac{1}{n!} \le \frac{e^n}{n^n}.
\]

## A. Saddle-Point Bound: Bounded Brick

### Existing Cauchy Brick

The repository already has the coefficient extraction and norm bound:

- `AnalyticCombinatorics/Ch4/Analytic/CauchyCoeff.lean:9`
  to `:27`: `coeff_eq_cauchy_circleIntegral_of_hasFPowerSeriesAt`.
- `AnalyticCombinatorics/Ch4/Analytic/CauchyCoeff.lean:29`
  to `:43`: `powerSeries_coeff_eq_cauchy_circleIntegral`.
- `AnalyticCombinatorics/Ch4/Analytic/CauchyCoeff.lean:45`
  to `:77`: `norm_coeff_le_of_circleIntegral`.

The checked shape of the last theorem is:

```lean
#check norm_coeff_le_of_circleIntegral
-- {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {R M : ℝ}
-- (hR : 0 < R) (hp : HasFPowerSeriesAt f p 0)
-- (hd : DifferentiableOn ℂ f (Metric.closedBall 0 R))
-- (hM : ∀ z ∈ Metric.sphere 0 R, ‖f z‖ ≤ M) (n : ℕ) :
-- ‖p.coeff n‖ ≤ M * R⁻¹ ^ n
```

Important point: this theorem does **not** require a formal theorem saying
`sSup` on the sphere equals `f r`. It only needs the pointwise bound
`∀ z ∈ Metric.sphere 0 R, ‖f z‖ ≤ M`.

For nonnegative real coefficients, take
`M = (PowerSeries.analyticSum F (R : ℂ)).re`. Then show directly:

```lean
∀ z ∈ Metric.sphere 0 R,
  ‖PowerSeries.analyticSum F z‖ ≤
    (PowerSeries.analyticSum F (R : ℂ)).re
```

This is the Lean-friendly version of
\[
  |f(z)| \le \sum_k a_k |z|^k = \sum_k a_k R^k = f(R).
\]

### Bridge to Analytic Sums

The local bridge file already exposes the relevant analytic sum facts:

- `AnalyticCombinatorics/Ch4/Analytic/Bridge.lean:15`
  to `:22`: `PowerSeries.toFMLS`, `PowerSeries.analyticSum`.
- `AnalyticCombinatorics/Ch4/Analytic/Bridge.lean:35`
  to `:41`: `PowerSeries.analyticSum_eq_tsum`.
- `AnalyticCombinatorics/Ch4/Analytic/Bridge.lean:43`
  to `:49`: `PowerSeries.hasSum_analyticSum_of_mem`.
- `AnalyticCombinatorics/Ch4/Analytic/Bridge.lean:51`
  to `:54`: `PowerSeries.hasFPowerSeriesOnBall_analyticSum`.

The checked facts used for summability/norm control:

- `.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/InfiniteSum.lean:140`
  to `:151`: `tsum_of_norm_bounded`, `norm_tsum_le_tsum_norm`.
- `.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/InfiniteSum.lean:172`
  to `:187`: `Summable.of_norm_bounded_eventually`, `Summable.of_norm`.
- `.lake/packages/mathlib/Mathlib/Analysis/Complex/Basic.lean:591`
  to `:601`: `Complex.hasSum_ofReal`, `Complex.summable_ofReal`,
  `Complex.ofReal_tsum`.

The following were stdin-checked:

```lean
#check PowerSeries.analyticSum_eq_tsum
#check PowerSeries.hasSum_analyticSum_of_mem
#check norm_tsum_le_tsum_norm
#check tsum_of_norm_bounded
#check Summable.of_norm
#check Summable.of_nonneg_of_le
#check tsum_nonneg
#check Complex.ofReal_tsum
#check Complex.hasSum_ofReal
```

### Stdin-Checked Sup Step

The actual checked foothold used `PowerSeries.mk` from a real nonnegative
coefficient sequence. This avoids fighting arbitrary complex coefficients
before the core inequality is stable.

Checked theorem shape:

```lean
lemma saddle_bound_sup_step_mk
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) {r : ℝ}
    {z : ℂ} (hz : ‖z‖ ≤ r)
    (hrmem :
      (r : ℂ) ∈ Metric.eball 0
        (PowerSeries.toFMLS
          (PowerSeries.mk fun n => (a n : ℂ))).radius) :
    ‖PowerSeries.analyticSum
        (PowerSeries.mk fun n => (a n : ℂ)) z‖ ≤
      (PowerSeries.analyticSum
        (PowerSeries.mk fun n => (a n : ℂ)) (r : ℂ)).re
```

This passed through `lake env lean --stdin`.

Proof sketch in Lean terms:

1. Let
   `F := PowerSeries.mk fun n => (a n : ℂ)`.
2. From `PowerSeries.hasSum_analyticSum_of_mem` at `z`, get summability of
   `fun n => PowerSeries.coeff n F * z ^ n`.
3. Use `norm_tsum_le_tsum_norm`.
4. Bound each term:
   \[
     \| (a_n : ℂ) z^n \| = a_n \|z\|^n
       \le a_n r^n.
   \]
   This uses `ha n` and `hz`.
5. Use `tsum_of_norm_bounded` to compare the norm tsum with
   `tsum fun n => a n * r ^ n`.
6. Convert the real tsum to the real part of the complex analytic sum at
   `(r : ℂ)`, using `Complex.ofReal_tsum`, `Complex.re_tsum`, and
   `PowerSeries.analyticSum_eq_tsum`.

The equality at the positive real radius was also stdin-checked:

```lean
lemma saddle_bound_real_radius_norm_eq_mk
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) {r : ℝ} (hr : 0 ≤ r)
    (hrmem :
      (r : ℂ) ∈ Metric.eball 0
        (PowerSeries.toFMLS
          (PowerSeries.mk fun n => (a n : ℂ))).radius) :
    ‖PowerSeries.analyticSum
        (PowerSeries.mk fun n => (a n : ℂ)) (r : ℂ)‖ =
      (PowerSeries.analyticSum
        (PowerSeries.mk fun n => (a n : ℂ)) (r : ℂ)).re
```

This is enough to justify the mathematical slogan
`sup_{|z|=r} ‖f z‖ = f(r)`, but the coefficient bound only needs the
`≤` direction on the circle.

### Stdin-Checked Cauchy Plug

The full Cauchy-bound plug also passed stdin-check:

```lean
lemma saddle_point_bound_mk
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) {R : ℝ} (hR : 0 < R)
    (hball :
      0 < (PowerSeries.toFMLS
        (PowerSeries.mk fun n => (a n : ℂ))).radius)
    (hRmem :
      (R : ℂ) ∈ Metric.eball 0
        (PowerSeries.toFMLS
          (PowerSeries.mk fun n => (a n : ℂ))).radius)
    (hd :
      DifferentiableOn ℂ
        (PowerSeries.analyticSum
          (PowerSeries.mk fun n => (a n : ℂ)))
        (Metric.closedBall 0 R))
    (n : ℕ) :
    ‖PowerSeries.coeff (R := ℂ) n
        (PowerSeries.mk fun n => (a n : ℂ))‖ ≤
      (PowerSeries.analyticSum
        (PowerSeries.mk fun n => (a n : ℂ)) (R : ℂ)).re * R⁻¹ ^ n
```

The last step uses:

```lean
(PowerSeries.hasFPowerSeriesOnBall_analyticSum F hball).hasFPowerSeriesAt
norm_coeff_le_of_circleIntegral hR hp hd hM n
PowerSeries.coeff_toFMLS
```

### Best Formal Statement for the First Brick

Recommended first theorem:

```lean
structure NonnegRealCoeff (F : PowerSeries ℂ) where
  coeffR : ℕ → ℝ
  coeff_nonneg : ∀ n, 0 ≤ coeffR n
  coeff_eq : ∀ n, PowerSeries.coeff n F = (coeffR n : ℂ)
```

Then prove:

```lean
theorem PowerSeries.norm_coeff_le_analyticSum_of_nonneg
    {F : PowerSeries ℂ} (hF : NonnegRealCoeff F)
    {R : ℝ} (hR : 0 < R)
    (hball : 0 < F.toFMLS.radius)
    (hRmem : (R : ℂ) ∈ Metric.eball 0 F.toFMLS.radius)
    (hd :
      DifferentiableOn ℂ
        (PowerSeries.analyticSum F)
        (Metric.closedBall 0 R))
    (n : ℕ) :
    ‖PowerSeries.coeff n F‖ ≤
      (PowerSeries.analyticSum F (R : ℂ)).re * R⁻¹ ^ n
```

This generalization from `PowerSeries.mk` is mechanical: replace each
`PowerSeries.coeff n F` by `(hF.coeffR n : ℂ)` using `hF.coeff_eq`.

If desired, a real-valued version for a real coefficient `a n` can follow by
rewriting `‖(a n : ℂ)‖ = a n` under `0 ≤ a n`.

### Optimized / Infimum Form

The optimized statement
\[
  [z^n] f \le \inf_{r>0} f(r) r^{-n}
\]
is a small second brick, not necessary for the first bound.

For Lean over `ℝ`, use `sInf`/`csInf`, not `iInf`, unless the target is moved
to a complete lattice such as `ℝ≥0∞`. Mathlib has:

- `.lake/packages/mathlib/Mathlib/Order/ConditionallyCompleteLattice/Basic.lean:197`:
  `le_csInf`.
- `.lake/packages/mathlib/Mathlib/Data/Real/Archimedean.lean:137`:
  `ConditionallyCompleteLinearOrder ℝ`.

Recommended shape:

```lean
def saddleBounds (F : PowerSeries ℂ) (n : ℕ) : Set ℝ :=
  {B | ∃ R : ℝ, 0 < R ∧
      B = (PowerSeries.analyticSum F (R : ℂ)).re * R⁻¹ ^ n}
```

Then prove:

```lean
theorem coeff_le_sInf_saddleBounds
    {F : PowerSeries ℂ} {n : ℕ} {c : ℝ}
    (hpointwise : ∀ B ∈ saddleBounds F n, c ≤ B)
    (hnonempty : (saddleBounds F n).Nonempty)
    (hboundedBelow : BddBelow (saddleBounds F n)) :
    c ≤ sInf (saddleBounds F n)
```

There is no reason to make the infimum form block the useful first theorem.

## B. Gaussian / Laplace Mathlib Inventory

### Gaussian Integral Values Exist

Mathlib has a real and complex Gaussian integral file:

- `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:14`
  to `:21`: file overview.
- Same file `:128` to `:160`:
  `integrable_exp_neg_mul_sq`, `integrable_cexp_neg_mul_sq`.
- Same file `:171` to `:193`:
  `integral_mul_cexp_neg_mul_sq`, `integral_gaussian_sq_complex`.
- Same file `:223` to `:235`: `integral_gaussian`.
- Same file `:250` to `:287`: `integral_gaussian_complex`.
- Same file `:289` to `:326`: half-line real/complex Gaussian integrals.

Stdin checks:

```lean
#check integral_gaussian
#check integral_gaussian_complex
#check integral_gaussian_Ioi
#check integrable_exp_neg_mul_sq
#check integrable_cexp_neg_mul_sq
```

This is useful for evaluating the final Gaussian factor
\(\sqrt{2\pi b(r)}^{-1}\), once the local integral has already been reduced
to a normalized Gaussian limit. It is not a Laplace method by itself.

### Dominated Convergence Exists

Mathlib has the standard dominated convergence infrastructure:

- `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:58`
  to `:74`: `MeasureTheory.tendsto_integral_of_dominated_convergence`,
  filter version.
- Same file `:217` to `:223`: interval version.
- Same file `:292` to `:298`:
  `intervalIntegral.continuousAt_of_dominated_interval`.

Stdin checks:

```lean
#check MeasureTheory.tendsto_integral_filter_of_dominated_convergence
#check MeasureTheory.tendsto_integral_of_dominated_convergence
```

This can support a hand-built central-arc proof after scaling
\(\theta \mapsto x / \sqrt{b(r)}\), but the uniform hypotheses and domination
will have to be supplied explicitly.

### Peak Function Machinery Exists, But Is Not Saddle-Point

Mathlib has a normalized-powers approximate-identity file:

- `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/PeakFunction.lean:11`
  to `:32`: overview.
- Same file `:371` to `:379`: normalized powers with unique maximum on compact.
- Same file `:394` to `:398`:
  `tendsto_integral_comp_smul_smul_of_integrable`.
- Same file `:452` to `:457`: shifted version.

Stdin checks:

```lean
#check tendsto_integral_comp_smul_smul_of_integrable
#check tendsto_integral_comp_smul_smul_of_integrable'
```

This is conceptually adjacent to Laplace asymptotics, but it is not a theorem
about \(e^{-t\phi(x)}\), not a complex contour theorem, and not immediately
usable for Hayman admissibility.

### No Laplace / Steepest Descent / Analytic Saddle Theorem Found

Searches for:

- `GaussianIntegral`
- `integral_gaussian`
- `∫ exp(-x^2)`
- `Laplace`
- `stationaryPhase`
- `steepest descent`
- `saddle`
- `Hayman`
- `H-admissible`
- `admissible`
- `a(r)`
- `b(r)`

found no analytic saddle-point method theorem and no Laplace-method theorem.

There is a file:

- `.lake/packages/mathlib/Mathlib/Order/SaddlePoint.lean:12`
  to `:21`

but it is about order-theoretic/minimax saddle points, not analytic
saddle-point asymptotics.

`Laplace` occurrences were for unrelated objects such as the Laplace operator
notation, not asymptotic integration.

## C. Full Saddle-Point Asymptotic: Wall Confirmed

The full theorem needs the following pieces.

### 1. H-Admissibility / Hayman Framework

Needed definitions:

```lean
def saddleA (f : ℂ → ℂ) (r : ℝ) : ℝ := ...
def saddleB (f : ℂ → ℂ) (r : ℝ) : ℝ := ...
structure HAdmissible (f : ℂ → ℂ) where
  positive_on_real : ...
  nonzero_on_real : ...
  radius_tendsto_top : ...
  central_width : ℝ → ℝ
  central_width_pos : ...
  central_width_tendsto_zero : ...
  b_tendsto_top : ...
  local_expansion : ...
  tail_decay : ...
```

Nothing like this exists locally or in Mathlib. The project's transfer
theorems have analogous estimate engineering, but for a fixed singularity
and delta domains, not moving radii.

Relevant local analogues:

- `AnalyticCombinatorics/Ch4/Analytic/KernelEstimate.lean:20`
  to `:58`: circle kernel norm square/lower bound.
- Same file `:91` to `:114`: `circleKernel_rpow_le_model`.
- Same file `:225` to `:240`: `modelKernel_integral_bound`.
- `AnalyticCombinatorics/Ch4/Analytic/DerivEstimate.lean:69`
  to `:79`: local derivative bound.
- Same file `:140` to `:150`: existence of derivative bound over a delta
  domain.
- `AnalyticCombinatorics/Ch4/Analytic/OTransfer.lean:28`
  to `:35`: `norm_coeff_le_integral_circle`.
- Same file `:172` to `:182`:
  `coeff_norm_isBigO_atTop_of_delta_bound_beta_gt_one`.
- Same file `:190` to `:213`: choice of `r = 1 - 1/n` and Cauchy plug.
- Same file `:222` to `:260`: circle integral bounded by kernel integral.
- `AnalyticCombinatorics/Ch4/Analytic/TransferTheorem.lean:78`
  to `:88`: `transfer_theorem_re_alpha_gt_one`.
- Same file `:108` to `:128`: error term and main term assembly.

These files are useful templates for proof style, but they do not provide the
new saddle-specific hypotheses.

### 2. Locating the Saddle

The saddle radius is usually defined by
\[
  a(r) = r f'(r) / f(r) = n.
\]

Lean needs:

- real differentiability of `r ↦ f(r)`,
- positivity/nonvanishing of `f(r)`,
- monotonicity or strict monotonicity of `a`,
- range/unboundedness of `a`,
- existence and often uniqueness of `r_n`,
- a usable sequence/function `n ↦ r_n`,
- asymptotic facts such as `r_n → ∞`, `b(r_n) → ∞`.

Mathlib has general analysis tools, but no ready saddle-selector theorem. This
must be built from scratch for the chosen class of admissible functions.

For `exp`, this is easy: `a(r)=r`, so `r_n=n`. For general
H-admissible functions, this is a real project.

### 3. Local Expansion

One needs a uniform expansion near the positive real axis:
\[
  \frac{f(r e^{i\theta})}{f(r)}
  =
  \exp\!\left(i\theta a(r) - \frac12\theta^2 b(r)\right)
  (1 + o(1))
\]
uniformly for \(|\theta| \le \delta(r)\).

Lean issues:

- choose a complex log branch or avoid log by making the expansion an
  admissibility axiom,
- express uniformity as a filter statement in `(r, θ)`,
- handle moving window `|θ| ≤ δ(r)`,
- ensure nonvanishing on the central arc if using logs,
- convert the local expansion into an integral asymptotic.

There is no existing project abstraction for this.

### 4. Central Gaussian Integral

After substituting \(x = \theta\sqrt{b(r)}\), the central arc becomes a
Gaussian integral. Mathlib can evaluate the Gaussian integral, but the theorem
that the scaled integral tends to it must be built.

Possible route:

1. Express the central integral as an `intervalIntegral`.
2. Scale by `Real.sqrt (b r)`.
3. Prove pointwise convergence to `fun x => Real.exp (-x^2 / 2)` or the
   corresponding complex exponential.
4. Produce an integrable dominating function.
5. Apply dominated convergence.
6. Use `integral_gaussian` / `integral_gaussian_complex`.

Every step except the last two is saddle-specific.

### 5. Tail Estimates

H-admissibility includes decay away from the saddle:
\[
  \sup_{\delta(r)\le |\theta|\le \pi}
  \left|
    \frac{f(r e^{i\theta})}{f(r)}
  \right|
  \sqrt{b(r)} \to 0
\]
or an equivalent tail condition.

This is the hardest analytic-estimate part. It is exactly the analogue of the
transfer theorem's “minor arc” estimate, but now the radius moves to infinity,
the peak is at `θ=0`, and the conditions are not encoded anywhere.

### 6. Assembly

The final assembly must combine:

- Cauchy coefficient formula on `|z|=r_n`,
- circle parameterization \(z = r_n e^{i\theta}\),
- cancellation of the \(e^{-in\theta}\) oscillation using
  `a(r_n)=n`,
- central Gaussian asymptotic,
- tail negligibility,
- algebraic normalization by `r_n^n`, `f(r_n)`, and
  `sqrt (2*pi*b(r_n))`,
- conversion to `Asymptotics.IsEquivalent`.

Mathlib has the general `IsEquivalent` API:

- `.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean:13`
  to `:44`: overview.
- Same file `:181` to `:219`:
  `isEquivalent_iff_exists_eq_mul`, `isEquivalent_iff_tendsto_one`.
- Same file `:264` to `:294`: multiplication/division rules.

But the analytic content is missing.

## D. Executable Architecture

### Brick 1: Nonnegative Coefficient Cauchy Bound

Status: **BOUNDED**.

Goal:

```lean
theorem PowerSeries.norm_coeff_le_analyticSum_of_nonneg
    {F : PowerSeries ℂ} (hF : NonnegRealCoeff F)
    {R : ℝ} (hR : 0 < R)
    (hball : 0 < F.toFMLS.radius)
    (hRmem : (R : ℂ) ∈ Metric.eball 0 F.toFMLS.radius)
    (hd :
      DifferentiableOn ℂ
        (PowerSeries.analyticSum F)
        (Metric.closedBall 0 R))
    (n : ℕ) :
    ‖PowerSeries.coeff n F‖ ≤
      (PowerSeries.analyticSum F (R : ℂ)).re * R⁻¹ ^ n
```

Implementation plan:

1. Add `NonnegRealCoeff`.
2. Prove the pointwise circle estimate:
   `‖PowerSeries.analyticSum F z‖ ≤
   (PowerSeries.analyticSum F (R : ℂ)).re` for `‖z‖ ≤ R`.
3. Specialize to `z ∈ Metric.sphere 0 R`.
4. Plug into `norm_coeff_le_of_circleIntegral`.
5. Add a convenience theorem for `PowerSeries.mk fun n => (a n : ℂ)`.

Risk: low. The `mk` version already passed stdin-check.

### Brick 2: Entire-Series Convenience Layer

Status: **BOUNDED / MEDIUM**.

Goal: remove repetitive radius/differentiability hypotheses for standard
entire power series.

For entire examples, prove a convenience lemma that replaces `hball`,
`hRmem`, and `hd` from Brick 1 by a single entire/radius-infinity hypothesis.
Do this only after inspecting the exact API around `F.toFMLS.radius`; I did
not stdin-check the final infinite-radius formulation.

Risk: medium only because the radius API may require some coercion work.

### Brick 3: Exponential Example

Status: **BOUNDED / MEDIUM**.

Target:

\[
  \frac{1}{n!} \le \frac{e^r}{r^n},\qquad r>0.
\]

Relevant checked Mathlib facts:

- `.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/Exp.lean:47`
  to `:55`: `PowerSeries.exp`, `PowerSeries.coeff_exp`.
- Same file `:69` to `:78`: derivative of `PowerSeries.exp`.
- `.lake/packages/mathlib/Mathlib/Analysis/Normed/Algebra/Exponential.lean:95`
  to `:107`: `NormedSpace.expSeries`.
- Same file `:250` to `:265`: `NormedSpace.exp_eq_tsum_div`.
- Same file `:451` to `:496`: `expSeries_radius_eq_top`,
  `exp_hasFPowerSeriesAt_zero`.
- `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Exponential.lean:210`
  to `:213`: `Complex.exp_eq_exp_ℂ`.

Stdin checks:

```lean
#check PowerSeries.exp
#check PowerSeries.coeff_exp
#check NormedSpace.exp_eq_tsum_div
#check NormedSpace.exp_eq_tsum
#check NormedSpace.exp_series_hasSum_exp'
#check NormedSpace.expSeries_eq_ofScalars
#check NormedSpace.expSeries_apply_eq_div
#check NormedSpace.exp_hasFPowerSeriesAt_zero
#check NormedSpace.expSeries_radius_eq_top
```

Expected statement:

```lean
theorem inv_factorial_le_exp_div_pow
    {n : ℕ} {r : ℝ} (hr : 0 < r) :
    (1 : ℝ) / Nat.factorial n ≤ Real.exp r / r ^ n
```

Then specialize to `r = n`:

```lean
theorem inv_factorial_le_exp_nat_div_pow_self
    {n : ℕ} (hn : 0 < n) :
    (1 : ℝ) / Nat.factorial n ≤ Real.exp n / (n : ℝ) ^ n
```

This is not Stirling, but it is a clean Stirling-type upper bound on
`1/n!`.

Risk: medium. The only nontrivial part is connecting the power-series analytic
sum to `Complex.exp` / `Real.exp` cleanly. The required facts exist.

Do **not** block this on proving that `r=n` is the global optimizer. Choosing
`r=n` is enough. Proving the optimization over all `r>0` is a separate real
calculus lemma about `r ↦ Real.exp r / r^n`.

### Brick 4: Optimized Bound

Status: **MEDIUM**.

Target:

\[
  \frac{1}{n!} \le \inf_{r>0} \frac{e^r}{r^n}
  = \frac{e^n}{n^n}.
\]

This requires:

- defining the admissible bound set,
- using `sInf`/`csInf`,
- proving the function is minimized at `r=n`,
- managing the `n=0` edge case separately.

This is useful but not structurally necessary for saddle-point foundations.

### Brick 5: Bell Number Bound

Status: **MEDIUM**.

Analytic target:

\[
  B_n/n! = [z^n]\exp(e^z-1)
  \le \frac{\exp(e^r-1)}{r^n}.
\]

Repository facts:

- `AnalyticCombinatorics/Ch2/EGF/Defs.lean:27`
  to `:40`: `egfSeq` and coefficient definition.
- Same file `:84` to `:88`:
  `CombClass.egf_setClass = PowerSeries.exp ℚ`.
- `AnalyticCombinatorics/Ch2/EGF/Applications.lean:21`
  to `:30`: `CombClass.egf_posInt`, `CombClass.egf_bell`.
- Same file `:32` to `:36`: surjection EGF.

Mathlib has Bell numbers:

- `.lake/packages/mathlib/Mathlib/Combinatorics/Enumerative/Bell.lean:179`
  to `:193`: `Nat.bell` definition/recurrence.
- Same file `:203` to `:212`: small values.
- Same file `:184` to `:185`: TODO noting missing connection to multiset
  partitions.

Assessment:

- Bound for the repository's `CombClass.posInt.set` counts is reachable.
- A theorem about `Nat.bell n` requires an additional combinatorial bridge.
  I did not find that bridge already present.
- The analytic side also needs a clean composition/evaluation bridge for
  `exp (exp z - 1)` and nonnegative coefficients.

### Brick 6: Stirling via Existing Mathlib

Status: **BOUNDED / MEDIUM**, but not a saddle proof.

Mathlib has:

- `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Stirling.lean:238`
  to `:245`: `Stirling.factorial_isEquivalent_stirling`.
- Same file `:268` to `:274`: `Stirling.le_factorial_stirling`.

Stdin checks:

```lean
#check Stirling.factorial_isEquivalent_stirling
#check Stirling.le_factorial_stirling
```

One can derive:
\[
  \frac1{n!} \sim
  \frac{1}{\sqrt{2\pi n}}\left(\frac{e}{n}\right)^n
\]
from the existing Stirling theorem plus asymptotic algebra. This is a useful
sanity target, but it does not establish the saddle-point method.

### Brick 7: General H-Admissible Saddle Asymptotic

Status: **WALL**.

This is a new theory layer:

1. define H-admissibility,
2. define `a(r)` and `b(r)`,
3. select `r_n`,
4. prove central expansion,
5. prove Gaussian central integral,
6. prove tail negligibility,
7. assemble coefficient asymptotics.

This should not be attempted until the bound bricks and at least one concrete
entire example are stable.

## E. Recommended Project Order

1. **First commit**: create a small file, probably under
   `AnalyticCombinatorics/Ch8/SaddlePoint/Bound.lean`, with
   `NonnegRealCoeff`, the pointwise circle bound, and the coefficient bound.
   This is the bounded foothold.

2. **Second commit**: add the `PowerSeries.mk` convenience theorem and possibly
   a theorem specialized to nonnegative real sequences.

3. **Third commit**: prove the exponential bound
   `1 / n! ≤ Real.exp r / r^n`. Then add the specialization
   `r = n`.

4. **Fourth commit**: decide whether to formalize the optimized infimum form.
   This is useful, but it is not needed for applications where the chosen
   radius is explicit.

5. **Fifth commit**: try the Bell bound for the repository EGF object, not
   immediately for Mathlib's `Nat.bell`. The `Nat.bell` bridge is a separate
   combinatorial project.

6. **Later**: only after the above is stable, start an H-admissibility design
   document and a toy full-asymptotic proof for `exp`, knowing that the
   general theorem is a wall.

## Final Honest Assessment

The saddle-point bound is a real, bounded, useful brick. The central estimate
was checked in Lean, and the existing Cauchy coefficient theorem is exactly the
right hook.

The full saddle-point asymptotic is not a near-term Lean theorem. Mathlib gives
Gaussian integrals and convergence tools, but the actual saddle method
framework is absent. A realistic plan is to first formalize the bound, then
prove concrete estimates for `exp` and Bell-type EGFs, and only then decide
whether to invest in a full H-admissibility theory.
