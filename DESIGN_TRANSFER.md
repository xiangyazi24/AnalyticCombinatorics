# F&S VI.3 Transfer Theorem Recon / Architecture

Date: 2026-06-01.  Repo: `~/repos/AnalyticCombinatorics`.  Mathlib: local `.lake/packages/mathlib/Mathlib`, checked with `lake env lean --stdin`.

## Executive verdict

The Cauchy coefficient extraction entry point is available.  There is no single Mathlib lemma named "coefficient equals Cauchy integral", but it is a small wrapper from:

- `cauchyPowerSeries_apply`;
- `DifferentiableOn.hasFPowerSeriesOnBall`;
- `HasFPowerSeriesAt.eq_formalMultilinearSeries`;
- `FormalMultilinearSeries.coeff`;
- `PowerSeries.coeff_toFMLS`.

Contour deformation to a Hankel/keyhole contour is not available as a ready theorem.  Mathlib has strong primitives: circle integrals, Cauchy on disks, rectangles, annuli, and a new `curveIntegral`/C2-homotopy theorem for closed 1-forms.  But there is no ready "deform this closed contour through a holomorphic region" theorem, and no bridge between `circleIntegral` and `curveIntegral`.

The proposed naive O-transfer by full-circle sup bound is off by one power.  It gives `O(n^Re(alpha))`, not `O(n^(Re(alpha)-1))`.  A real O/little-o transfer without Hankel is still plausible by a Darboux route:

1. prove the circle integral estimate for exponent `beta > 1`;
2. use Cauchy local derivative estimates in Delta-domains to reduce arbitrary `beta` to `beta + k > 1`;
3. divide coefficient bounds for `f^(k)` back by the polynomial factor.

This is the smartest incremental path.  If Xiang insists on the classical Hankel proof with a deformed contour and reciprocal-Gamma Hankel integral, that is a multi-month project.

## Existing project anchors

- `PowerSeries.toFMLS` is already the bridge from `PowerSeries C` to `FormalMultilinearSeries C C C`: `AnalyticCombinatorics/Ch4/Analytic/Bridge.lean:15`.
- `PowerSeries.coeff_toFMLS` identifies FMLS coeffs with power-series coeffs: `AnalyticCombinatorics/Ch4/Analytic/Bridge.lean:26`.
- Existing standard scale:
  `coeff_oneDivOneSubCpow_isEquivalent`, i.e. coeffs of `(1-z)^(-alpha)` are equivalent to `n^(alpha-1)/Gamma alpha`: `AnalyticCombinatorics/Ch4/Analytic/SingularityGeneral.lean:141`.
- Existing Delta-domain definition:
  `DeltaDomainArg R phi = { z | ||z|| < R /\ z != 1 /\ phi < |arg (z - 1)| }`: `AnalyticCombinatorics/Ch4/Analytic/DeltaDomain.lean:13`.
- Existing analyticity of `(1-z)^(-alpha)` on the Delta-domain: `analyticOnNhd_one_sub_cpow_deltaDomain`: `AnalyticCombinatorics/Ch4/Analytic/DeltaDomain.lean:102`.

## A. Cauchy coefficient extraction

### Available APIs

`circleIntegral` is defined as the circle path integral over `circleMap`: `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CircleIntegral.lean:357`.

`cauchyPowerSeries` is exactly the FMLS whose coefficients are circle integrals:

- definition: `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CircleIntegral.lean:545`;
- coefficient evaluation: `cauchyPowerSeries_apply`: `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CircleIntegral.lean:549`;
- coefficient norm bound: `norm_cauchyPowerSeries_le`: `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CircleIntegral.lean:556`;
- radius lower bound: `le_radius_cauchyPowerSeries`: `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CircleIntegral.lean:576`;
- Cauchy series sums to the Cauchy integral: `hasSum_cauchyPowerSeries_integral`: `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CircleIntegral.lean:623`.

Analyticity with Cauchy coefficients is available:

- `hasFPowerSeriesOnBall_of_differentiable_off_countable`: `.lake/packages/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean:594`;
- `DifferentiableOn.hasFPowerSeriesOnBall`: `.lake/packages/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean:623`.

Uniqueness is available:

- `HasFPowerSeriesAt.eq_formalMultilinearSeries`: `.lake/packages/mathlib/Mathlib/Analysis/Analytic/Uniqueness.lean:113`.

FMLS coefficient mechanics:

- `FormalMultilinearSeries.coeff p n = p n 1`: `.lake/packages/mathlib/Mathlib/Analysis/Calculus/FormalMultilinearSeries.lean:304`;
- `FormalMultilinearSeries.coeff_ofScalars`: `.lake/packages/mathlib/Mathlib/Analysis/Analytic/OfScalars.lean:89`.

### Stdin-checked wrapper

This theorem was checked successfully with `lake env lean --stdin`:

```lean
example {f : Complex -> Complex} {p : FormalMultilinearSeries Complex Complex Complex}
    {R : Real} (hR : 0 < R)
    (hp : HasFPowerSeriesAt f p 0)
    (hd : DifferentiableOn Complex f (Metric.closedBall 0 R)) (n : Nat) :
    p.coeff n =
      (2 * Real.pi * Complex.I : Complex)^(-1) •
        circleIntegral
          (fun z => ((1 : Complex) / (z - 0)) ^ n • (z - 0)^(-1) • f z)
          0 R := by
  have hq : HasFPowerSeriesAt f (cauchyPowerSeries f 0 R) 0 := by
    have hnn : 0 < ((⟨R, hR.le⟩ : NNReal)) := by exact_mod_cast hR
    exact (hd.hasFPowerSeriesOnBall hnn).hasFPowerSeriesAt
  have hpq : p = cauchyPowerSeries f 0 R := hp.eq_formalMultilinearSeries hq
  calc
    p.coeff n = (cauchyPowerSeries f 0 R).coeff n := by rw [hpq]
    _ = (cauchyPowerSeries f 0 R n fun _ => (1 : Complex)) := by rfl
    _ = _ := by exact cauchyPowerSeries_apply f 0 R n 1
```

The analogous `PowerSeries` wrapper also checked:

```lean
PowerSeries.coeff n F = same_circle_integral
```

using `PowerSeries.coeff_toFMLS`.

Verdict: BOUNDED.  First brick should be a clean wrapper file, probably `Ch6/Analytic/CauchyCoeff.lean` or a Ch4 analytic support file.

## B. Contour deformation inventory

### Circle and disk Cauchy API

- Disk Cauchy integral formula with countable exceptional set:
  `Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable`: `.lake/packages/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean:501`.
- Disk circle integral zero:
  `Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable`: `.lake/packages/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean:445`.
- Closed-disc differentiable version:
  `DifferentiableOn.circleIntegral_sub_inv_smul`: `.lake/packages/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean:568`.
- Scalar division form:
  `Complex.circleIntegral_div_sub_of_differentiable_on_off_countable`: `.lake/packages/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean:577`.
- Higher derivative Cauchy formula:
  `Complex.circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable`: `.lake/packages/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean:721`.
- Circle integral norm bound:
  `circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const`: `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CircleIntegral.lean:437`.

### Rectangle and annulus primitives

- Rectangle Cauchy-Goursat with countable exceptional set:
  `integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`: `.lake/packages/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean:271`.
- Simpler rectangle differentiable-on version:
  `integral_boundary_rect_eq_zero_of_differentiableOn`: `.lake/packages/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean:300`.
- Annulus equality for concentric circle integrals:
  `Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable`: `.lake/packages/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean:356`.
- Annulus equality for `(z-c)^(-1) • f z`:
  `Complex.circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable`: `.lake/packages/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean:320`.

These are useful but not enough for Hankel deformation.  The annulus theorem only compares concentric circles.  A Hankel/keyhole contour is not a concentric circle.

### Path and curve integral API

Topological path homotopy exists:

- `Path.Homotopy` and `Path.Homotopic`: `.lake/packages/mathlib/Mathlib/Topology/Homotopy/Path.lean:15`;
- actual type definition: `.lake/packages/mathlib/Mathlib/Topology/Homotopy/Path.lean:48`.

Curve integral exists:

- `curveIntegral` definition and notation: `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CurveIntegral/Basic.lean:123`;
- interval-integral expansion: `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CurveIntegral/Basic.lean:145`;
- reverse path: `curveIntegral_symm`: `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CurveIntegral/Basic.lean:214`;
- concatenation: `curveIntegral_trans`: `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CurveIntegral/Basic.lean:274`;
- segment formula: `curveIntegral_segment`: `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CurveIntegral/Basic.lean:303`;
- segment norm bound: `norm_curveIntegral_segment_le`: `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CurveIntegral/Basic.lean:318`;
- C1 path integrability from continuity of the 1-form: `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CurveIntegral/Basic.lean:331`.

C2 homotopy theorem for closed 1-forms exists:

- file states this goal explicitly: `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean:22`;
- theorem with countable exceptional set:
  `ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable`: `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean:230`;
- non-exceptional version:
  `ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt`: `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean:255`;
- `DiffContOnCl` version:
  `ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_diffContOnCl`: `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean:273`.

### Missing for Hankel

No grep hit for a ready theorem of the form:

- `circleIntegral = curveIntegral` for a circle path;
- "integral invariant under homotopy in holomorphic region" for arbitrary closed contours;
- "deform closed contour to piecewise contour";
- generic polygon/keyhole contour API;
- reciprocal-Gamma Hankel contour evaluation.

Honest verdict:

- Buildable from primitives? Yes, but not as a small wrapper.
- From-scratch? For the actual Hankel proof, mostly yes: one must build the contour/path layer, bridge it to existing circle integrals, prove deformation via either C2 `curveIntegral` homotopy or rectangle tiling, then do asymptotic estimates.
- Best primitive for a modern approach: `curveIntegral` + Poincare C2 homotopy.  But it requires proving the holomorphic integrand as a closed 1-form and constructing smooth homotopies for piecewise paths.  This is a real wall.

## C. O-transfer shortcut

### Correction: full-circle sup bound is too weak

Let `r_n = 1 - 1/n`.  Cauchy gives

```text
|a_n| <= r_n^(-n) * average_circle |f|
```

If one uses only `max |f|` on the circle and `|1-z| >= 1/n`, then

```text
max |f| <= M n^beta
r_n^(-n) = O(1)
```

so the result is `a_n = O(n^beta)`, not `O(n^(beta-1))`.  The missing factor is not cosmetic.  It is exactly the arc-length/integrability gain near `z=1`.

The theorem `Real.tendsto_one_add_div_pow_exp` is available and checked:
`.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/LogBounds.lean:447` for the real Nat version, and stdin `#check Real.tendsto_one_add_div_pow_exp`.

### What works without Hankel

For `beta > 1`, use the integrated bound, not the sup bound:

```text
|a_n| <= O(1) * integral_0^(2*pi) |1 - r_n exp(i theta)|^(-beta) dtheta
       = O(n^(beta-1)).
```

This needs a new real-analysis lemma.  Mathlib has the raw ingredients:

- interval integral norm bound: `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:737`;
- real `rpow` integral over intervals: `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean:147`;
- improper `Ioi` rpow integral for exponent `< -1`: `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean:174`;
- trig bounds such as `cos_le_one_sub_mul_cos_sq`: `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean:137`;
- `Complex.norm_cpow_real`, `Complex.norm_cpow_le`, `Complex.norm_cpow_eq_rpow_re_of_pos` checked by stdin; source around `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:307`.

Expected proof shape for the kernel lemma:

```text
rho = 1/n
r = 1 - rho
|1 - r e^{i theta}|^2 = rho^2 + 2r(1 - cos theta)
>= c * (rho^2 + theta^2)   on theta in [-pi, pi]
integral (rho^2 + theta^2)^(-beta/2) dtheta
<= C rho^(1-beta)          if beta > 1
```

This is MEDIUM, not bounded.

### Derivative bootstrap: the smarter no-Hankel route

Once the `beta > 1` O/little-o transfer exists, arbitrary `beta` can likely be handled without Hankel:

1. Choose `k` with `beta + k > 1`.
2. Prove a local Cauchy derivative estimate in a narrower Delta-domain:

   ```text
   f = O(|1-z|^(-beta))  ==>  f^(k) = O(|1-z|^(-beta-k)).
   f = o(|1-z|^(-beta))  ==>  f^(k) = o(|1-z|^(-beta-k)).
   ```

   This uses local disks `ball z (c*|1-z|)` contained in the original Delta-domain and Cauchy's derivative formula.

3. Apply the `beta+k > 1` coefficient transfer to `f^(k)`.
4. Use coefficient relation:

   ```text
   [z^n] f^(k) = (n+k)(n+k-1)...(n+1) * [z^(n+k)] f.
   ```

   Then divide by `~ n^k`.

Available derivative/coefficient APIs:

- higher derivative Cauchy formula: `.lake/packages/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean:721`;
- `HasFPowerSeriesOnBall.fderiv`: `.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:211`;
- `FormalMultilinearSeries.derivSeries_coeff_one`: `.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:803`;
- `PowerSeries.coeff_derivative`: `.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/Derivative.lean:115`;
- `FormalMultilinearSeries.coeff_iterate_fslope` for dslope, maybe useful but not the scalar derivative: `.lake/packages/mathlib/Mathlib/Analysis/Calculus/FormalMultilinearSeries.lean:345`.

This route is not the classical Hankel proof, but it may prove the actual one-term transfer theorem:

```text
f(z) ~ C (1-z)^(-alpha) in Delta
==> [z^n]f ~ C n^(alpha-1)/Gamma(alpha)
```

because the singular model coefficient asymptotic is already in Ch4, and the error is `o(|1-z|^(-Re alpha))` in norm.  The hard part is the little-o transfer for the error.

Verdict:

- naive sup-bound O-transfer: BOUNDED but only gives the wrong `O(n^beta)`;
- correct circle-only transfer for `beta > 1`: MEDIUM;
- derivative-bootstrapped O/little-o transfer for all real `beta`: MEDIUM to MEDIUM-WALL, but still far below Hankel;
- full classical Hankel proof: WALL.

## D. Ordered architecture bricks

### Brick 1: Cauchy coefficient wrappers

Label: BOUNDED.  Effort: 0.5-1 day.

Deliverables:

- `coeff_eq_cauchy_circleIntegral_of_hasFPowerSeriesAt`;
- `powerSeries_coeff_eq_cauchy_circleIntegral`;
- norm-bound wrapper using `norm_cauchyPowerSeries_le` or `circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const`.

Dependencies:

- `cauchyPowerSeries_apply`;
- `DifferentiableOn.hasFPowerSeriesOnBall`;
- `HasFPowerSeriesAt.eq_formalMultilinearSeries`;
- `PowerSeries.coeff_toFMLS`.

### Brick 2: Delta-domain geometry for circles and local disks

Label: BOUNDED/MEDIUM.  Effort: 2-4 days.

Deliverables:

- `closedBall 0 r subset DeltaDomainArg R phi` for `r < 1`, `1 < R`, `phi < pi/2`;
- `sphere 0 r subset DeltaDomainArg R phi`;
- local disk lemma: for a narrower Delta-domain point `z`, `ball z (kappa * ||1-z||) subset DeltaDomainArg R phi`;
- comparability: on that local disk, `||1-w||` is within constant factors of `||1-z||`;
- circle inequalities: on `|z| = 1 - 1/n`, `||1-z|| >= 1/n`.

Dependencies:

- existing geometric Delta-domain equivalence: `delta_arg_eq_geom`: `AnalyticCombinatorics/Ch4/Analytic/DeltaDomain.lean:45`;
- open Delta-domain: `isOpen_deltaDomainArg`: `AnalyticCombinatorics/Ch4/Analytic/DeltaDomain.lean:69`.

### Brick 3: Circle kernel integral estimate

Label: MEDIUM.  Effort: 4-7 days.

Statement target:

```text
for beta > 1:
  integral_0^(2*pi) ||1 - (1 - 1/n) exp(i theta)||^(-beta) dtheta
    = O(n^(beta-1)).
```

This is the first real analytic estimate brick.  It is reusable and avoids contour deformation.

### Brick 4: O/little-o transfer for beta > 1

Label: MEDIUM.  Effort: 3-5 days after Brick 3.

Statement target:

```text
if f analytic in Delta and ||f z|| <= M ||1-z||^(-beta), beta > 1,
then coeff f n = O(n^(beta-1)).

if ||f z|| = o(||1-z||^(-beta)),
then coeff f n = o(n^(beta-1)).
```

Use Brick 1 Cauchy wrappers, Brick 2 circle containment, Brick 3 integral estimate.

### Brick 5: Cauchy derivative estimates in Delta-domains

Label: MEDIUM.  Effort: 1-2 weeks.

Deliverables:

- Big-O derivative estimate;
- little-o derivative estimate;
- versions for `iteratedDeriv k f`.

Dependencies:

- local disk geometry from Brick 2;
- Cauchy derivative formula `.lake/packages/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean:721`;
- circle norm bounds `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CircleIntegral.lean:430`.

### Brick 6: Derivative-coefficient descent

Label: MEDIUM.  Effort: 4-7 days.

Deliverables:

- coefficients of scalar derivative in FMLS/PowerSeries form;
- iterated version:

```text
coeff_n(f^(k)) = falling/rising polynomial in n * coeff_(n+k)(f).
```

Dependencies:

- `HasFPowerSeriesOnBall.fderiv`: `.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:211`;
- `FormalMultilinearSeries.derivSeries_coeff_one`: `.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:803`;
- `PowerSeries.coeff_derivative`: `.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/Derivative.lean:115`.

### Brick 7: General no-Hankel O/little-o transfer

Label: MEDIUM-WALL.  Effort: 1-2 weeks after Bricks 3-6.

This combines:

- choose `k` with `beta+k > 1`;
- apply derivative estimates;
- apply `beta+k > 1` transfer;
- descend coefficient bounds.

This is the key strategic brick.  If it works cleanly, the project can avoid Hankel for VI.3's one-term theorem.

### Brick 8: One-term transfer theorem from existing singular model

Label: MEDIUM.  Effort: 3-7 days after Brick 7.

Statement:

```text
f(z) ~ C * (1-z)^(-alpha) in Delta
==> coeff f n ~ C * n^(alpha-1)/Gamma(alpha)
```

Proof:

```text
g = f - C * (1-z)^(-alpha)
coeff(g) = o(n^(Re alpha - 1))       by Brick 7
coeff(model) ~ n^(alpha-1)/Gamma(alpha) by Ch4
```

Need to align:

- norm little-o with complex asymptotic equivalent;
- `Gamma alpha != 0` under `alpha notin {0,-1,-2,...}`;
- existing `coeff_oneDivOneSubCpow_isEquivalent`: `AnalyticCombinatorics/Ch4/Analytic/SingularityGeneral.lean:141`.

### Brick 9: Restricted theorem first

Label: BOUNDED/MEDIUM once previous bricks exist.  Effort: 3-5 days.

Recommended first theorem variant:

- real `alpha > 0`;
- `C : Complex`;
- Delta-domain with `R > 1`, `0 < phi < pi/2`;
- asymptotic along `z -> 1` within a slightly larger Delta-domain;
- coefficients expressed through an FMLS/PowerSeries expansion at 0.

Then generalize to complex `alpha`.

### Brick 10: Hankel contour infrastructure

Label: WALL.  Effort: 4-8 weeks minimum.

Deliverables if pursuing classical proof:

- define piecewise paths for arcs, radial segments, small circle, keyhole/Hankel pieces;
- bridge circle parameterizations to `curveIntegral`;
- prove integrability and norm bounds for all pieces;
- build deformation theorem for these specific contours, probably via C2 homotopy or rectangle tiling;
- handle endpoint/corner concatenation and cancellation.

Dependencies:

- `curveIntegral` API from `MeasureTheory/Integral/CurveIntegral/Basic.lean`;
- C2 homotopy theorem from `CurveIntegral/Poincare.lean`;
- many new path geometry lemmas.

### Brick 11: Hankel asymptotic and reciprocal Gamma

Label: WALL.  Effort: 4-8 weeks minimum, likely more.

Deliverables:

- scaled contour `z = 1 + t/n`;
- convergence of the scaled integrand to Hankel kernel;
- dominated estimates on truncated/unbounded Hankel pieces;
- formal reciprocal-Gamma Hankel formula.

Mathlib has Gamma/Beta machinery, but the reciprocal-Gamma Hankel contour formula is not present in the searched files.  Existing Gamma support is real-integral based, e.g. Ch4 uses `Complex.GammaSeq_tendsto_Gamma` via `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean` and project file `SingularityGeneral.lean`.

## E. Overall recommendation

If the goal is "prove VI.3 in Lean by any defensible proof", do not start with Hankel.  Start:

1. Cauchy coefficient wrappers.
2. Delta circle/local-disk geometry.
3. Kernel integral estimate for `beta > 1`.
4. O/little-o transfer for `beta > 1`.
5. Derivative bootstrap.
6. Combine with the existing singular model scale.

This path is still a major project, but it is plausible in several weeks to a couple of months, with useful intermediate theorems after each brick.

If the goal is specifically "formalize the classical Hankel proof", call it months.  The genuine walls are:

- contour deformation infrastructure;
- `circleIntegral`/`curveIntegral` bridges;
- piecewise Hankel path API;
- reciprocal-Gamma Hankel integral and dominated convergence.

The first executable brick should be Cauchy coefficient extraction, immediately followed by the corrected O-transfer path.  Do not build Hankel until the no-Hankel Darboux route is exhausted.
