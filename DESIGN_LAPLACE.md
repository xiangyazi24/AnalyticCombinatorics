# Laplace / Saddle-Point Recon for the Hayman Asymptotic

Scope: Lean4/Mathlib v4.29.0, local project `AnalyticCombinatorics`.

No `.lean` files were edited for this recon. All theorem names below were checked with `lake env lean --stdin` unless explicitly marked as an absence/failure. Line references are from the local tree.

## Executive answer

The project is tractable only if split sharply.

1. The coefficient asymptotic should be decomposed into an assembly theorem plus verification theorems. The assembly theorem is BOUNDED once an exact parameterized Cauchy integral on `[-pi, pi]` is available.
2. The Gaussian central limit should be a reusable Laplace-core theorem using dominated convergence. This is BOUNDED/MEDIUM if pointwise convergence and domination are assumptions.
3. The `exp` testbed is the right first concrete saddle-point milestone. It is MEDIUM/HARD, not BOUNDED, because the local second-order expansion and tail estimates still need real-variable proof work. But it is much smaller than general Hayman.
4. General H-admissibility is absent from Mathlib and from this repo. The full Hayman theorem is WALL / multi-month.

Smartest path:

1. Prove the exact complex Cauchy coefficient parameterization and split on `[-pi, pi]`.
2. Prove the assembly theorem from central-plus-tail hypotheses.
3. Prove the Gaussian DCT/Laplace core with pointwise-plus-domination hypotheses.
4. Prove the `f = exp` saddle asymptotic from those bricks, cross-checked against Mathlib Stirling.
5. Only then define the general H-admissible interface and prove general verification.

## A. Mathlib Laplace / Gaussian / DCT inventory

### Gaussian integrals

Mathlib has the Gaussian value needed for the central integral, including complex-valued versions.

Checked names:

- `integrable_exp_neg_mul_sq` at `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:128`
- `integrable_exp_neg_mul_sq_iff` at `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:132`
- `integrable_cexp_neg_mul_sq` at `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:136`
- `norm_cexp_neg_mul_sq` at `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:140`
- `integral_mul_cexp_neg_mul_sq` at `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:171`
- `integral_gaussian_sq_complex` at `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:191`
- `integral_gaussian` at `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:223`
- `continuousAt_gaussian_integral` at `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:236`
- `integral_gaussian_complex` at `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:247`
- `integral_gaussian_complex_Ioi` at `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:288`
- `integral_gaussian_Ioi` at `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:323`

Useful exact target:

```lean
#check integral_gaussian_complex
-- integral_gaussian_complex :
--   integral (fun x : Real => Complex.exp (-(a * x ^ 2))) volume
--     = Complex.ofReal (Real.sqrt (Real.pi / a))
```

For the saddle core we need

```text
integral (fun x : Real => Complex.exp (-(x^2)/2)) = sqrt(2*pi)
```

This should be obtained from `integral_gaussian_complex` with `a = 1/2`. There will be routine but nonzero algebra for `Real.sqrt (Real.pi / (1/2)) = Real.sqrt (2 * Real.pi)`.

Also useful for tail/little-o estimates:

- `exp_neg_mul_rpow_isLittleO_exp_neg` at `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:34`
- `rpow_mul_exp_neg_mul_rpow_isLittleO_exp_neg` at `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:42`
- `exp_neg_mul_sq_isLittleO_exp_neg` at `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:50`
- `rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg` at `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:58`

These are directly relevant to estimates like `sqrt n * exp (-c * n^(1/5)) -> 0`.

### Dominated convergence

Mathlib has the dominated convergence theorem in the exact generality needed.

Checked names:

- `MeasureTheory.tendsto_integral_of_dominated_convergence` at `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:58`
- `MeasureTheory.tendsto_integral_filter_of_dominated_convergence` at `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:70`
- `MeasureTheory.tendsto_integral_filter_of_norm_le_const` at `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:165`
- `intervalIntegral.tendsto_integral_filter_of_dominated_convergence` at `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:217`

The filter version is the main one for `n -> infinity`. The interval version is useful for fixed finite intervals but the saddle central integral after scaling naturally lives on all of `Real`, with an indicator depending on `n`; the measure-theoretic integral over `volume` is cleaner.

### Peak-function / approximate-identity assets

Mathlib has "peak function" approximate-identity results, but they do not directly prove the Hayman saddle theorem.

Checked names:

- `tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto` at `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/PeakFunction.lean:184`
- `tendsto_integral_peak_smul_of_integrable_of_tendsto` at `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/PeakFunction.lean:222`
- `tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn` at `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/PeakFunction.lean:371`
- `tendsto_integral_comp_smul_smul_of_integrable` at `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/PeakFunction.lean:394`
- `tendsto_integral_comp_smul_smul_of_integrable'` at `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/PeakFunction.lean:452`

These are useful models for proof style, especially the `comp_smul` approximate-identity theorem. But the Hayman central window has a moving cutoff and complex oscillatory normalization. It is more straightforward to build a bespoke DCT theorem for the scaled integrand.

### Cauchy integral and parameterization

Local repo already has exact Cauchy coefficient formulas using `circleIntegral`.

Checked names:

- `coeff_eq_cauchy_circleIntegral_of_hasFPowerSeriesAt` at `AnalyticCombinatorics/Ch4/Analytic/CauchyCoeff.lean:9`
- `powerSeries_coeff_eq_cauchy_circleIntegral` at `AnalyticCombinatorics/Ch4/Analytic/CauchyCoeff.lean:29`
- `norm_coeff_le_of_circleIntegral` at `AnalyticCombinatorics/Ch4/Analytic/CauchyCoeff.lean:45`
- `norm_coeff_le_integral_circle` at `AnalyticCombinatorics/Ch4/Analytic/OTransfer.lean:28`

Mathlib has the circle integral definition and norm tools:

- `circleIntegral` definition at `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CircleIntegral.lean:357`
- `circleIntegral_def_Icc` at `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CircleIntegral.lean:364`
- `circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const` at `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CircleIntegral.lean:437`
- `norm_cauchyPowerSeries_le` at `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CircleIntegral.lean:556`

What is missing locally is the exact saddle-friendly parameterization:

```text
[z^n] f
  = (2*pi)^(-1) * integral theta in -pi..pi,
      f (r * exp (I*theta)) * r^(-n) * exp (-I*n*theta)
```

This should be a first brick. The local theorem gives the exact circleIntegral formula, but the assembly theorem wants an interval integral over real `theta` and then a central/tail split. Mathlib's `circleIntegral_def_Icc` gives the interval expression over the usual parameter range. Moving from `[0, 2*pi]` to `[-pi, pi]` will probably need periodicity.

Relevant interval-scaling and period tools:

- `intervalIntegral.integral_comp_mul_right` at `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:873`
- `intervalIntegral.smul_integral_comp_mul_right` at `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:885`
- `intervalIntegral.integral_comp_div` at `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:897`
- `intervalIntegral.inv_smul_integral_comp_div` at `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:908`
- `MeasureTheory.Measure.integral_comp_mul_left` at `.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean:151`
- `MeasureTheory.Measure.integral_comp_div` at `.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean:164`
- `Function.Periodic.intervalIntegral_add_eq` at `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Periodic.lean:346`

### Asymptotic equivalence algebra

Mathlib has the needed `IsEquivalent` and little-o algebra.

Checked names:

- `Asymptotics.isEquivalent_of_tendsto_one` at `.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean:186`
- `Asymptotics.isEquivalent_iff_tendsto_one` at `.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean:202`
- `Asymptotics.IsEquivalent.refl` at `.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean:89`
- `Asymptotics.IsEquivalent.mul` at `.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean:264`
- `Asymptotics.IsEquivalent.inv` at `.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean:280`
- `Asymptotics.IsEquivalent.div` at `.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean:290`
- `Asymptotics.IsEquivalent.add_isLittleO` at `.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean:147`
- `Asymptotics.IsLittleO.of_norm_left` at `.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:748`
- `Asymptotics.IsLittleO.trans_isBigO` at `.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean:396`
- `Asymptotics.isLittleO_iff` at `.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:199`

Local transfer code already demonstrates the exact final assembly pattern:

- `transfer_theorem` at `AnalyticCombinatorics/Ch4/Analytic/TransferGeneral.lean:71`
- final transfer assembly uses main equivalent plus little-o error at `AnalyticCombinatorics/Ch4/Analytic/TransferGeneral.lean:100`

That pattern should be reused: exact decomposition, prove main term equivalent, prove residual little-o, combine by `add_isLittleO`.

### Existing saddle and transfer toolkit

Current saddle files are useful but are upper-bound oriented, not full asymptotic.

Checked local names:

- `NonnegRealCoeff` at `AnalyticCombinatorics/Ch8/SaddlePoint/Bound.lean:8`
- `PowerSeries.norm_analyticSum_le_re_analyticSum_of_nonneg` at `AnalyticCombinatorics/Ch8/SaddlePoint/Bound.lean:15`
- `PowerSeries.norm_coeff_le_analyticSum_of_nonneg` at `AnalyticCombinatorics/Ch8/SaddlePoint/Bound.lean:37`
- `saddle_point_bound_mk` at `AnalyticCombinatorics/Ch8/SaddlePoint/Bound.lean:62`
- `expCarrier_coeff` at `AnalyticCombinatorics/Ch8/SaddlePoint/Exp.lean:11`
- `expCarrier_analyticSum_eq_exp` at `AnalyticCombinatorics/Ch8/SaddlePoint/Exp.lean:46`
- `expCarrier_analyticSum_re` at `AnalyticCombinatorics/Ch8/SaddlePoint/Exp.lean:56`
- `expCarrier_differentiableOn` at `AnalyticCombinatorics/Ch8/SaddlePoint/Exp.lean:61`
- `inv_factorial_le_exp_div_pow` at `AnalyticCombinatorics/Ch8/SaddlePoint/Exp.lean:73`
- `inv_factorial_le_exp_nat_div_pow_self` at `AnalyticCombinatorics/Ch8/SaddlePoint/Exp.lean:88`
- `bell_egf_coeff_le` at `AnalyticCombinatorics/Ch8/SaddlePoint/BellBridge.lean:8`

Transfer-estimate toolkit:

- `circleKernel_norm_sq` at `AnalyticCombinatorics/Ch4/Analytic/KernelEstimate.lean:20`
- `circleKernel_norm_sq_lower` at `AnalyticCombinatorics/Ch4/Analytic/KernelEstimate.lean:41`
- `circleKernel_rpow_le_model` at `AnalyticCombinatorics/Ch4/Analytic/KernelEstimate.lean:91`
- `modelKernel_integral_bound` at `AnalyticCombinatorics/Ch4/Analytic/KernelEstimate.lean:225`
- `modelKernel_integral_bound_nat` at `AnalyticCombinatorics/Ch4/Analytic/KernelEstimate.lean:340`
- `circleKernel_integral_bound_nat` at `AnalyticCombinatorics/Ch4/Analytic/KernelEstimate.lean:363`
- `closedBall_subset_deltaDomain` at `AnalyticCombinatorics/Ch4/Analytic/DeltaGeometry.lean:6`
- `local_disk_norm_comparable` at `AnalyticCombinatorics/Ch4/Analytic/DeltaGeometry.lean:47`
- `local_disk_subset_deltaDomain_deltaLocalKappa` at `AnalyticCombinatorics/Ch4/Analytic/DeltaGeometry.lean:168`
- `coeff_norm_isBigO_atTop_of_delta_bound_beta_gt_one` at `AnalyticCombinatorics/Ch4/Analytic/OTransfer.lean:172`
- `coeff_norm_isLittleO_atTop_of_delta_littleO_beta_gt_one` at `AnalyticCombinatorics/Ch4/Analytic/LittleOTransfer.lean:413`
- `ofReal_isEquivalent_iff` at `AnalyticCombinatorics/Ch4/Analytic/RealAsymptotics.lean:17`

These tools help with contour and tail estimates, especially if the future Hayman verification uses disk/arc geometry. They do not replace the central Gaussian theorem.

### `exp` / Stirling assets

For the `f = exp` testbed:

- `PowerSeries.exp` and `PowerSeries.coeff_exp` at `.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/Exp.lean:48`
- `NormedSpace.exp_eq_expSeries_sum` at `.lake/packages/mathlib/Mathlib/Analysis/Normed/Algebra/Exponential.lean:158`
- `NormedSpace.expSeries_radius_eq_top` at `.lake/packages/mathlib/Mathlib/Analysis/Normed/Algebra/Exponential.lean:451`
- local `expCarrier` bridge at `AnalyticCombinatorics/Ch8/SaddlePoint/Exp.lean:11`
- local `expCarrier_analyticSum_eq_exp` at `AnalyticCombinatorics/Ch8/SaddlePoint/Exp.lean:46`

Stirling exists:

- `Stirling.factorial_isEquivalent_stirling` at `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Stirling.lean:237`

Complex exponential/trigonometric facts:

- `Complex.exp_add` at `.lake/packages/mathlib/Mathlib/Analysis/Complex/Exponential.lean:107`
- `Complex.exp_sub` at `.lake/packages/mathlib/Mathlib/Analysis/Complex/Exponential.lean:164`
- `Complex.ofReal_exp` at `.lake/packages/mathlib/Mathlib/Analysis/Complex/Exponential.lean:187`
- `Complex.exp_mul_I` at `.lake/packages/mathlib/Mathlib/Analysis/Complex/Trigonometric.lean:519`
- `Complex.exp_re` at `.lake/packages/mathlib/Mathlib/Analysis/Complex/Trigonometric.lean:527`
- `Complex.norm_exp_ofReal_mul_I` at `.lake/packages/mathlib/Mathlib/Analysis/Complex/Trigonometric.lean:970`
- `Complex.norm_exp` at `.lake/packages/mathlib/Mathlib/Analysis/Complex/Trigonometric.lean:1003`

Tail-relevant real facts:

- `Real.cos_le_one_sub_mul_cos_sq` at `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean:137`
- `Real.tendsto_exp_atBot` at `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Exp.lean:230`
- `Real.exp_le_exp` at `.lake/packages/mathlib/Mathlib/Analysis/Complex/Exponential.lean:316`

### What is absent

I found no direct analytic Laplace-asymptotic theorem of the form

```text
integral exp (-t * phi x) psi x ~ ...
```

No usable steepest-descent / saddle-point / Hayman H-admissibility framework appears in Mathlib or this repo. Grep for `Laplace`, `laplace`, `steepest`, `saddle-point`, `saddle point`, `Hayman`, `HAdmissible`, and `H-admissible` found only unrelated material or prior design notes, not theorem infrastructure. Mathlib has an unrelated order-theoretic saddle-point file, not analytic saddle-point asymptotics.

Conclusion: the project should not search for a hidden one-shot Laplace theorem. Build the specific DCT brick.

## B. Assembly vs verification decomposition

### Strategic answer

Yes, split the project into:

1. Assembly theorem: assumes central Gaussian convergence, tail negligibility, exact Cauchy integral decomposition, and concludes coefficient asymptotic.
2. Verification theorem(s): prove those hypotheses for a concrete class/function.

The assembly theorem is BOUNDED, provided the exact parameterized Cauchy formula is already in hand. It is mostly interval splitting plus asymptotic algebra.

The hard work is not in assembly. The hard work is proving central expansion and tail decay.

### Recommended normalized notation

For a function `f : Complex -> Complex`, saddle radii `r n : Real`, scale `B n : Real`, and window `delta n : Real`, define the normalized phase integrand

```text
G n theta =
  f ((r n : Complex) * Complex.exp (Complex.I * theta))
    / f (r n)
  * Complex.exp (-Complex.I * (n : Real) * theta)
```

Then define

```text
Jc n = (1 / (2*pi)) * integral theta in -(delta n)..(delta n), G n theta

Jt n = (1 / (2*pi)) *
  (integral theta in -pi..-(delta n), G n theta
   + integral theta in delta n..pi, G n theta)

pref n = f (r n) / (r n)^n
scale n = pref n / sqrt (2*pi*B n)
```

Exact Cauchy split should state, eventually:

```text
coeff n = pref n * (Jc n + Jt n)
```

The saddle equation `a(r_n) = n` is not needed by the assembly theorem if `G` already contains the cancelled phase. It belongs in the verification theorem that proves the central hypothesis.

### Assembly hypotheses

Use one of two equivalent hypothesis packages.

Package 1, normalized integral limits:

```text
Hcentral :
  Tendsto (fun n => (Complex.ofReal (sqrt (2*pi*B n))) * Jc n)
    atTop (nhds 1)

Htail :
  Tendsto (fun n => (Complex.ofReal (sqrt (2*pi*B n))) * Jt n)
    atTop (nhds 0)

Hsplit :
  eventually, coeff n = pref n * (Jc n + Jt n)

Hnonzero :
  eventually, scale n != 0
```

Conclusion:

```text
Asymptotics.IsEquivalent atTop coeff scale
```

Proof skeleton:

```text
coeff n / scale n
  = pref n * (Jc n + Jt n) / (pref n / sqrt(2*pi*B n))
  = sqrt(2*pi*B n) * (Jc n + Jt n)
  -> 1 + 0
```

Then use `Asymptotics.isEquivalent_of_tendsto_one`.

Package 2, main-plus-error:

```text
main n = pref n * Jc n
err n = pref n * Jt n

Hmain : IsEquivalent atTop main scale
Herr  : IsLittleO atTop err scale
Hsplit : eventually, coeff n = main n + err n
```

Then use the transfer theorem pattern: `Hmain.add_isLittleO Herr`, plus eventual equality. This closely matches `AnalyticCombinatorics/Ch4/Analytic/TransferGeneral.lean:100`.

Package 1 is probably cleaner for saddle work because the central and tail hypotheses are naturally expressed after multiplication by `sqrt B_n`.

### Needed Mathlib for assembly

Assembly uses:

- `Asymptotics.isEquivalent_of_tendsto_one` at `.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean:186`
- `Asymptotics.IsEquivalent.add_isLittleO` at `.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean:147`
- `Asymptotics.isLittleO_iff` at `.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:199`
- standard `Tendsto` algebra for multiplication/addition in `Complex`
- local transfer pattern at `AnalyticCombinatorics/Ch4/Analytic/TransferGeneral.lean:100`

The only nontrivial non-asymptotic prerequisite is the exact Cauchy split. Local exact Cauchy exists as `circleIntegral` in `AnalyticCombinatorics/Ch4/Analytic/CauchyCoeff.lean:9`, but a saddle-friendly `[-pi, pi]` parameterization should be built explicitly.

### Difficulty

- Assembly from an assumed exact split: BOUNDED.
- Exact Cauchy parameterization and split into central/tail arcs: BOUNDED/MEDIUM.
- Proving central/tail hypotheses for a general H-admissible function: WALL.

## C. Gaussian-central Laplace-core brick

### The reusable theorem

After the substitution

```text
theta = x / sqrt (B n)
```

the normalized central term should become

```text
sqrt(2*pi*B n) * Jc n
  = (1 / sqrt(2*pi)) *
      integral x over Real, H n x
```

where

```text
L n = delta n * sqrt (B n)

H n x =
  if abs x <= L n then
    f (r_n * exp (I * x / sqrt(B n))) / f(r_n)
      * exp (-I * n * x / sqrt(B n))
  else
    0
```

The reusable DCT theorem should assume:

```text
HBpos    : eventually, 0 < B n
HL       : Tendsto L atTop atTop
Hpoint   : for almost every x,
             Tendsto (fun n => H n x) atTop
               (nhds (Complex.exp (-(x^2)/2)))
Hdom     : exists D : Real -> Real,
             Integrable D volume
             and eventually, for almost every x, norm (H n x) <= D x
```

Conclusion:

```text
Tendsto
  (fun n => integral x, H n x)
  atTop
  (nhds (integral x, Complex.exp (-(x^2)/2)))
```

and by `integral_gaussian_complex`,

```text
Tendsto
  (fun n => (1 / sqrt(2*pi)) * integral x, H n x)
  atTop
  (nhds 1)
```

This is the central hypothesis required by assembly.

### Why DCT is enough

There is no need for a full Laplace theorem if the central window is normalized externally. Mathlib's

- `MeasureTheory.tendsto_integral_filter_of_dominated_convergence` at `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:70`

is exactly designed for a sequence/filter of integrands. The moving interval is handled by building the cutoff into `H n x`.

The Gaussian value comes from:

- `integral_gaussian_complex` at `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:247`

The integrability of a Gaussian majorant comes from:

- `integrable_exp_neg_mul_sq` at `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:128`
- `integrable_cexp_neg_mul_sq` at `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:136`

### Substitution brick

Separate from DCT, prove the interval substitution:

```text
integral theta in -delta n..delta n, G n theta
  = (1 / sqrt(B n)) *
      integral x in -delta n * sqrt(B n)..delta n * sqrt(B n),
        G n (x / sqrt(B n))
```

Relevant checked names:

- `intervalIntegral.integral_comp_mul_right` at `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:873`
- `intervalIntegral.smul_integral_comp_mul_right` at `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:885`
- `intervalIntegral.integral_comp_div` at `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:897`
- `intervalIntegral.inv_smul_integral_comp_div` at `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:908`

This substitution/indicator packaging is MEDIUM because Lean interval integrals over reversed or signed bounds tend to require careful hypotheses (`0 < sqrt(B n)`, endpoint algebra, coercions).

### Difficulty

- DCT theorem assuming `Hpoint` and `Hdom`: BOUNDED.
- Add substitution from the theta-window and Gaussian normalization: MEDIUM.
- Derive `Hpoint` and `Hdom` from H-admissibility: WALL.

## D. The `e^z` saddle testbed

### Why `exp` is the right testbed

For `f(z) = exp z`,

```text
a(r) = r f'(r)/f(r) = r
b(r) = r a'(r) = r
```

so the saddle solving `a(r_n)=n` is `r_n = n`, and `B_n = n`.

The coefficient is known:

```text
[z^n] exp z = 1 / n!
```

Local repo already has:

- `expCarrier_coeff` at `AnalyticCombinatorics/Ch8/SaddlePoint/Exp.lean:11`
- `expCarrier_analyticSum_eq_exp` at `AnalyticCombinatorics/Ch8/SaddlePoint/Exp.lean:46`

Mathlib has Stirling for cross-check:

- `Stirling.factorial_isEquivalent_stirling` at `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Stirling.lean:237`

The saddle asymptotic becomes:

```text
1 / n! ~ exp n / (n^n * sqrt(2*pi*n)).
```

This is exactly Stirling in reciprocal form.

### Explicit normalized integrand

At `r_n = n`, the normalized Cauchy integrand is

```text
G_n(theta)
  = exp (n * exp(I*theta)) / exp n * exp(-I*n*theta)
  = exp (n * (exp(I*theta) - 1 - I*theta)).
```

Its norm is

```text
norm G_n(theta) = exp (n * (cos theta - 1)).
```

Relevant checked names:

- `Complex.exp_add` at `.lake/packages/mathlib/Mathlib/Analysis/Complex/Exponential.lean:107`
- `Complex.exp_sub` at `.lake/packages/mathlib/Mathlib/Analysis/Complex/Exponential.lean:164`
- `Complex.exp_mul_I` at `.lake/packages/mathlib/Mathlib/Analysis/Complex/Trigonometric.lean:519`
- `Complex.exp_re` at `.lake/packages/mathlib/Mathlib/Analysis/Complex/Trigonometric.lean:527`
- `Complex.norm_exp` at `.lake/packages/mathlib/Mathlib/Analysis/Complex/Trigonometric.lean:1003`
- `Complex.ofReal_exp` at `.lake/packages/mathlib/Mathlib/Analysis/Complex/Exponential.lean:187`

### Central scaling

Use a window

```text
delta_n = n^(-2/5)
```

or generally `delta_n = n^(-alpha)` with `1/3 < alpha < 1/2`. Then:

```text
delta_n -> 0
delta_n * sqrt n -> infinity
n * delta_n^3 -> 0
```

After `theta = x / sqrt n`,

```text
G_n(x/sqrt n)
  = exp (n * (exp(I*x/sqrt n) - 1 - I*x/sqrt n))
  -> exp (-(x^2)/2)
```

For domination, when `abs (x/sqrt n) <= pi`, use:

- `Real.cos_le_one_sub_mul_cos_sq` at `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean:137`

This yields a Gaussian majorant of the form

```text
norm G_n(x/sqrt n)
  = exp (n * (cos (x/sqrt n) - 1))
  <= exp (-c*x^2)
```

with some explicit `c > 0` on the needed range. Integrability follows from `integrable_exp_neg_mul_sq`.

The moving cutoff `abs x <= delta_n * sqrt n` tends to all of `Real`, so the indicator disappears pointwise.

### Tail

For `abs theta >= delta_n` inside `[-pi, pi]`, the same cosine bound gives

```text
norm G_n(theta) <= exp (-c * n * delta_n^2).
```

With `delta_n = n^(-2/5)`,

```text
n * delta_n^2 = n^(1/5),
```

so the normalized tail is bounded by

```text
C * sqrt n * exp (-c * n^(1/5)) -> 0.
```

Relevant checked names:

- `rpow_mul_exp_neg_mul_rpow_isLittleO_exp_neg` at `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:42`
- `Real.tendsto_exp_atBot` at `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Exp.lean:230`
- `Real.exp_le_exp` at `.lake/packages/mathlib/Mathlib/Analysis/Complex/Exponential.lean:316`

### Feasibility assessment

The `exp` testbed is reachable and should be done before general Hayman.

But it is not a trivial "assembly only" test. The following proof work remains:

1. Exact Cauchy parameterization for `expCarrier`.
2. Algebraic normalization of the `exp` integrand.
3. Pointwise second-order limit:

```text
n * (exp(I*x/sqrt n) - 1 - I*x/sqrt n) -> -x^2/2.
```

4. Gaussian domination using the cosine bound.
5. Tail little-o after multiplying by `sqrt n`.
6. Final conversion from coefficient form to reciprocal factorial form.

The pointwise second-order limit is the main local-analysis subproblem. I did not find a checked ready-made theorem for `1 - cos x ~ x^2/2` or `sin x ~ x` under the exact names guessed during recon. Do not cite those guessed names. The robust route is either:

- prove the needed Taylor expansions from Mathlib's Taylor/calculus tools, or
- prove the exact second-order real/complex exponential limit directly as a local lemma.

The second route is probably shorter for the `exp` testbed.

Using `Stirling.factorial_isEquivalent_stirling` alone would only check the final statement, not the saddle machinery. The meaningful milestone is to prove the saddle central/tail hypotheses explicitly for `exp`, then derive Stirling as a theorem. Mathlib Stirling should be used as a cross-check, not as the proof of the saddle result.

Difficulty: MEDIUM/HARD, but concrete and well-scoped.

## E. General H-admissibility architecture

### Absent framework

No H-admissibility definition/framework is present in Mathlib or in this repo. The local Ch8 saddle files currently give upper bounds and examples, not Hayman asymptotics.

The future interface should define:

```text
a(r) = r * f'(r) / f(r)
b(r) = r * a'(r)
```

for `r` approaching a radius of convergence, plus:

1. positivity/nonvanishing hypotheses on real positive radii,
2. existence of saddle radii `r_n` satisfying `a(r_n) = n`,
3. `B_n = b(r_n) -> infinity`,
4. a central width `delta(r)` with `delta(r) -> 0` and `delta(r)*sqrt(b(r)) -> infinity`,
5. uniform local expansion:

```text
f(r*exp(I*theta))/f(r)
  = exp(I*a(r)*theta - b(r)*theta^2/2) * (1 + o(1))
```

uniformly for `abs theta <= delta(r)`,

6. tail admissibility:

```text
sup_{delta(r) <= abs theta <= pi}
  norm (f(r*exp(I*theta))/f(r))
  = o(1 / sqrt(b(r)))
```

or an equivalent normalized tail bound strong enough after the Cauchy integral.

### General theorem target

The final theorem should look like:

```text
theorem coeff_isEquivalent_saddle
  (hf : HAdmissible f R ...)
  (hr : saddleSequence hf r)
  :
  IsEquivalent atTop
    (fun n => coeff f n)
    (fun n => f (r n) / ((r n)^n * sqrt (2*pi*b (r n))))
```

The theorem should be parametric over the saddle sequence rather than trying first to prove a canonical `r_n` exists. Existence/uniqueness of `r_n` from monotonicity of `a(r)` should be a separate theorem.

### Verification burden for general H-admissible functions

This is the wall:

1. Differentiability/analyticity and real-positive nonvanishing.
2. Definitions of `a` and `b` with coercion discipline between `Real` and `Complex`.
3. Uniform local expansion in a moving window.
4. Tail decay on the complement arc.
5. Measurability/integrability of all normalized integrands.
6. Saddle radius existence and `B_n -> infinity`.
7. Algebraic conversion from the abstract expansion to the DCT pointwise/domination hypotheses.

The transfer-project kernel and delta-geometry lemmas are useful for bounding arcs, but Hayman tail conditions are global on the circle and need their own interface.

### Ordered bricks

#### Brick 1: Cauchy parameterization and split

Difficulty: BOUNDED/MEDIUM.

Goal:

```text
coeff n =
  f(r_n) / r_n^n *
    ((1/(2*pi))*integral over central G_n
     + (1/(2*pi))*integral over tail G_n)
```

Dependencies:

- local Cauchy theorem at `AnalyticCombinatorics/Ch4/Analytic/CauchyCoeff.lean:9`
- `circleIntegral_def_Icc` at `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CircleIntegral.lean:364`
- `Function.Periodic.intervalIntegral_add_eq` at `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Periodic.lean:346`

This should be the first Lean brick.

#### Brick 2: Assembly theorem

Difficulty: BOUNDED.

Assume exact split, central normalized convergence, tail normalized convergence, and nonzero scale. Conclude `IsEquivalent`.

Dependencies:

- `Asymptotics.isEquivalent_of_tendsto_one` at `.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean:186`
- local transfer assembly pattern at `AnalyticCombinatorics/Ch4/Analytic/TransferGeneral.lean:100`

This is the first theorem that proves the architecture works.

#### Brick 3: Gaussian DCT core

Difficulty: BOUNDED/MEDIUM.

Assume scaled integrands converge pointwise a.e. to `exp(-x^2/2)` and are dominated by an integrable Gaussian. Conclude central normalized convergence.

Dependencies:

- `MeasureTheory.tendsto_integral_filter_of_dominated_convergence` at `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:70`
- `integral_gaussian_complex` at `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:247`
- `integrable_exp_neg_mul_sq` at `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:128`
- interval substitution lemmas at `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:873-908`

#### Brick 4: `exp` saddle testbed

Difficulty: MEDIUM/HARD.

Prove the saddle theorem for `f = exp`:

```text
[z^n] exp z ~ exp n / (n^n * sqrt(2*pi*n)).
```

Then convert to:

```text
1 / n! ~ exp n / (n^n * sqrt(2*pi*n)).
```

Use Mathlib Stirling only as a check:

- `Stirling.factorial_isEquivalent_stirling` at `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Stirling.lean:237`

This milestone validates every architectural layer with a fully explicit function.

#### Brick 5: Abstract H-admissible typeclass/structure

Difficulty: MEDIUM to design, WALL to fully prove useful theorems.

Recommended structure fields:

```text
structure HAdmissible (f : Complex -> Complex) where
  analytic_on_disk : ...
  positive_on_real : ...
  nonzero_on_real : ...
  a_def : Real -> Real
  b_def : Real -> Real
  saddle_width : Real -> Real
  b_tendsto_at_boundary : ...
  width_tendsto_zero : ...
  width_sqrt_b_tendsto_top : ...
  local_expansion_uniform : ...
  tail_bound_uniform : ...
```

Avoid putting saddle sequence existence into this first structure. Make saddle sequences separate:

```text
structure SaddleSequence (hf : HAdmissible f) where
  r : Nat -> Real
  r_pos : ...
  saddle_eq : ...
  b_tendsto : ...
```

This separation keeps the assembly theorem reusable and prevents the first general theorem from getting stuck on monotonicity/existence.

#### Brick 6: General Hayman theorem

Difficulty: WALL / multi-month.

Derive the assembly hypotheses from `HAdmissible` and `SaddleSequence`, then invoke assembly. This is the actual F&S Ch VIII theorem.

#### Brick 7: Concrete H-admissible examples

Difficulty: WALL individually, but easier after the interface stabilizes.

Start with `exp`; then Bell/exponential generating functions already touched by `BellBridge`; only then move to broader classes.

### First brick recommendation

Do not start with the general `HAdmissible` structure. It will invite months of interface churn before any asymptotic theorem works.

Start with:

```text
Exact Cauchy parameterization on [-pi, pi]
  +
Saddle assembly theorem from assumed central/tail limits
```

Then immediately test that architecture on `exp`.

Reason: this produces a working executable theorem stack early:

```text
Cauchy split
  -> assembly
  -> Gaussian DCT core
  -> explicit exp estimates
  -> Stirling via saddle
```

Once this chain works, the general Hayman theorem becomes a verification/interface project instead of an open-ended Laplace-method project.

### Honest timeline

Estimated effort:

- Cauchy parameterization/split: days to 1 week.
- Assembly theorem: 1-3 days after split.
- Gaussian DCT core with substitution: 1-2 weeks.
- `exp` testbed: 2-5 weeks, depending on Taylor/trig asymptotic friction.
- General H-admissible interface and theorem: several months.
- Nontrivial examples beyond `exp`: additional weeks/months per class.

The project is therefore not one hard theorem; it is a theorem stack. The stack should be built from the bottom up, with `exp` as the first full vertical slice.
