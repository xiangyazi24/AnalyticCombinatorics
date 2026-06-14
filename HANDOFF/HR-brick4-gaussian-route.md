═══ BRIDGE ac | b300851a | 16248 chars 2360 words 477 lines | 485s | prov=network | OK ═══
═══ BRIDGE ac | b300851a | 16248 chars 2360 words 477 lines | 485s | prov=network | OK ═══
The theorem should be stated without an outer `{s : ℝ} (hs : 0 < s)`. That binder is shadowed by the `fun s : ℝ => ...` inside `Tendsto`. Use:

```lean
lemma gaussianTail_asymp :
    Tendsto
      (fun s : ℝ =>
        (∫ v in Set.Ioi (1 : ℝ),
            Real.exp (-s * (v - Erdos.C / (2 * s)) ^ 2) / v)
          / ((2 * Real.sqrt Real.pi / Erdos.C) * Real.sqrt s))
      (𝓝[>] (0 : ℝ)) (𝓝 1)
```

I recommend the **interval route**, not a direct `MeasurePreserving`/`map` proof on `Set.Ioi`. Your repo already uses the exact interval APIs needed for improper integrals: `intervalIntegral.integral_comp_mul_deriv'` for finite-interval substitutions, and `intervalIntegral_tendsto_integral_Ioi` to pass `B → ∞`. `ModelSaddleIntegral.lean` uses `intervalIntegral.integral_comp_mul_deriv'` for the `u = v²` substitution and then uses `intervalIntegral_tendsto_integral_Ioi` to lift it to `Set.Ioi`. fileciteturn156file0L142-L164 fileciteturn157file0L56-L70

For DCT, use the exact theorem already used in your repo:

```lean
MeasureTheory.tendsto_integral_filter_of_dominated_convergence
```

The repo calls it with `(μ := volume) (bound := D) Hmeas Hdom hDint Hpoint`. fileciteturn155file0L22-L26

For the Gaussian value, the confirmed Mathlib theorem is:

```lean
integral_gaussian_complex
```

Your repo wraps it as:

```lean
gaussian_integral_half :
  (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2)) =
    (Real.sqrt (2 * Real.pi) : ℂ)
```

fileciteturn154file0L18-L40

I would not try the whole moving-lower-limit integral at once. Split at half the saddle:
\[
v_0(s)=\frac{C}{2s},\qquad q(s)=\frac{C}{4s}.
\]
For small \(s\), \(1\le q(s)\). Then
\[
\int_{1}^{\infty}\frac{e^{-s(v-v_0)^2}}{v}\,dv
=
\int_{1}^{q(s)}\frac{e^{-s(v-v_0)^2}}{v}\,dv
+
\int_{q(s)}^{\infty}\frac{e^{-s(v-v_0)^2}}{v}\,dv.
\]
The left part is exponentially negligible:
\[
0\le
\int_{1}^{q(s)}\frac{e^{-s(v-v_0)^2}}{v}\,dv
\le
\frac{C}{4s}\exp\!\left(-\frac{C^2}{16s}\right).
\]
The right part has a clean substitution
\[
u=\sqrt{s}\,(v-v_0).
\]
At \(v=q(s)=v_0/2\), the lower limit is
\[
\alpha(s)=-\frac{C}{4\sqrt{s}}.
\]
On this central/right region the denominator is bounded away from zero:
\[
1+\frac{2\sqrt{s}}{C}u \ge \frac12,
\]
so DCT is clean with dominating function \(2e^{-u^2}\).

## The proof decomposition I would commit

Put this in a new file, e.g. `GaussianTail.lean`.

```lean
import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.ModelSaddleIntegral
import AnalyticCombinatorics.Ch8.SaddlePoint.GaussianCore

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators MeasureTheory Real
open AnalyticCombinatorics.Ch8.Partitions.Erdos
open scoped Topology BigOperators Interval

noncomputable section

noncomputable def gaussianTailIntegral (s : ℝ) : ℝ :=
  ∫ v in Set.Ioi (1 : ℝ),
    Real.exp (-s * (v - C / (2 * s)) ^ 2) / v

noncomputable def gaussianTailCut (s : ℝ) : ℝ :=
  C / (4 * s)

noncomputable def gaussianTailAlpha (s : ℝ) : ℝ :=
  -C / (4 * Real.sqrt s)

noncomputable def gaussianTailBeta (s : ℝ) : ℝ :=
  2 * Real.sqrt s / C

noncomputable def gaussianTailKernel (s u : ℝ) : ℝ :=
  Set.indicator
    (Set.Ioi (gaussianTailAlpha s))
    (fun u : ℝ =>
      Real.exp (-(u ^ 2)) / (1 + gaussianTailBeta s * u)) u
```

### 1. Gaussian integral wrapper

This is the clean real wrapper around the confirmed complex API.

```lean
lemma integral_exp_neg_sq :
    (∫ u : ℝ, Real.exp (-(u ^ 2))) = Real.sqrt Real.pi := by
  have h :=
    integral_gaussian_complex (b := (1 : ℂ))
      (by norm_num : 0 < Complex.re (1 : ℂ))
  -- `h` says:
  -- ∫ x, Complex.exp (-(1 : ℂ) * (x : ℂ)^2) = (π / 1)^(1/2)
  -- Turn both sides into real values.
  have hfun :
      (fun x : ℝ => Complex.exp (-(1 : ℂ) * (x : ℂ) ^ 2))
        =
      (fun x : ℝ => (Real.exp (-(x ^ 2)) : ℂ)) := by
    funext x
    rw [Complex.ofReal_exp]
    congr 1
    norm_num
    ring
  rw [hfun] at h
  have hcast :
      ((∫ u : ℝ, Real.exp (-(u ^ 2))) : ℂ)
        = ∫ u : ℝ, (Real.exp (-(u ^ 2)) : ℂ) := by
    exact (ofReal_integral_eq_integral_ofReal
      (by
        exact (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).integrableOn)).symm
  -- If `ofReal_integral_eq_integral_ofReal` is not in namespace under this exact name,
  -- use Mathlib's `Complex.ofReal_integral_eq_integral_ofReal`; the theorem exists in
  -- the Bochner integral API.
  rw [← hcast] at h
  rw [Complex.ofReal_inj] at h
  simpa using h
```

Name caveat: I am confident `integral_gaussian_complex` exists because your repo uses it. I am less confident about the exact namespace of the real-to-complex integral cast theorem; in recent Mathlib it is usually available as `ofReal_integral_eq_integral_ofReal` or `Complex.ofReal_integral_eq_integral_ofReal`. If this name misses, keep the wrapper as a tiny local porting target.

### 2. Central transformed kernel tends to \(\sqrt\pi\)

This is the DCT lemma. The moving lower limit is handled by defining an indicator on all of `ℝ`.

```lean
lemma gaussianTailAlpha_tendsto_atBot :
    Tendsto gaussianTailAlpha (𝓝[>] (0 : ℝ)) atBot := by
  unfold gaussianTailAlpha
  have hsqrt :
      Tendsto (fun s : ℝ => Real.sqrt s) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    exact Real.tendsto_sqrt_nhdsWithin_zero
  have hinv :
      Tendsto (fun s : ℝ => 1 / Real.sqrt s) (𝓝[>] (0 : ℝ)) atTop := by
    simpa [one_div] using tendsto_inv_nhdsGT_zero.comp hsqrt
  have hmul :
      Tendsto (fun s : ℝ => -(C / 4) * (1 / Real.sqrt s))
        (𝓝[>] (0 : ℝ)) atBot := by
    have hconst : -(C / 4) < 0 := by positivity
    exact tendsto_const_mul_atBot_of_neg hconst hinv
  simpa [div_eq_mul_inv, mul_assoc] using hmul

lemma gaussianTailBeta_tendsto_zero :
    Tendsto gaussianTailBeta (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  unfold gaussianTailBeta
  have hsqrt0 :
      Tendsto (fun s : ℝ => Real.sqrt s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    exact Real.tendsto_sqrt_nhdsWithin_zero.mono_right nhdsWithin_le_nhds
  simpa using hsqrt0.const_mul (2 / C)

lemma gaussianTailKernel_pointwise :
    ∀ᵐ u : ℝ,
      Tendsto (fun s : ℝ => gaussianTailKernel s u)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Real.exp (-(u ^ 2)))) := by
  refine ae_of_all _ ?_
  intro u
  have hα_event :
      ∀ᶠ s in 𝓝[>] (0 : ℝ), gaussianTailAlpha s < u :=
    gaussianTailAlpha_tendsto_atBot.eventually_lt_atTop u
  have hden :
      Tendsto (fun s : ℝ => 1 + gaussianTailBeta s * u)
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hb := gaussianTailBeta_tendsto_zero
    simpa using tendsto_const_nhds.add (hb.mul tendsto_const_nhds)
  have hquot :
      Tendsto
        (fun s : ℝ =>
          Real.exp (-(u ^ 2)) / (1 + gaussianTailBeta s * u))
        (𝓝[>] (0 : ℝ))
        (𝓝 (Real.exp (-(u ^ 2)) / 1)) := by
    exact tendsto_const_nhds.div hden (by norm_num : (1 : ℝ) ≠ 0)
  refine hquot.congr' ?_
  filter_upwards [hα_event] with s hs
  simp [gaussianTailKernel, hs]
```

The only Mathlib-name risk here is `Real.tendsto_sqrt_nhdsWithin_zero`; if it is absent in v4.29.0, prove the two sqrt facts from `Real.continuousAt_sqrt` and `Tendsto.mono_left`. The repo already uses many `Real.sqrt` tendsto facts, for example `Real.tendsto_sqrt_atTop`. fileciteturn71file0L161-L164

Dominating function:

```lean
lemma gaussianTailKernel_dom :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᵐ u : ℝ,
      ‖gaussianTailKernel s u‖ ≤ 2 * Real.exp (-(u ^ 2)) := by
  have hsmall :
      ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧ s ≤ 1 := by
    filter_upwards
      [self_mem_nhdsWithin,
       mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
      with s hs0 hs1
    exact ⟨hs0, le_of_lt hs1⟩
  filter_upwards [hsmall] with s hs
  refine ae_of_all _ ?_
  intro u
  by_cases hu : gaussianTailAlpha s < u
  · have hspos : 0 < s := hs.1
    have hsqrtpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
    have hden_lb : (1 : ℝ) / 2 ≤ 1 + gaussianTailBeta s * u := by
      unfold gaussianTailBeta gaussianTailAlpha at hu
      have hCpos : 0 < C := C_pos
      have hmul := mul_lt_mul_of_pos_left hu (2 * Real.sqrt s / C) (by positivity)
      -- `(2√s/C) * (-C/(4√s)) = -1/2`.
      have hleft :
          (2 * Real.sqrt s / C) * (-C / (4 * Real.sqrt s)) = -(1 / 2 : ℝ) := by
        field_simp [C_pos.ne', hsqrtpos.ne']
        ring
      rw [hleft] at hmul
      unfold gaussianTailBeta
      linarith
    have hden_pos : 0 < 1 + gaussianTailBeta s * u := by linarith
    simp [gaussianTailKernel, hu, Real.norm_eq_abs]
    rw [abs_div, abs_of_pos hden_pos]
    calc
      Real.exp (-(u ^ 2)) / (1 + gaussianTailBeta s * u)
          ≤ Real.exp (-(u ^ 2)) / ((1 : ℝ) / 2) := by
            exact div_le_div_of_nonneg_left (Real.exp_pos _).le
              (by norm_num) hden_lb
      _ = 2 * Real.exp (-(u ^ 2)) := by ring
  · simp [gaussianTailKernel, hu]
    positivity

lemma integrable_gaussian_dom :
    Integrable (fun u : ℝ => 2 * Real.exp (-(u ^ 2))) := by
  have hbase : Integrable (fun u : ℝ => Real.exp (-(1 : ℝ) * u ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
  refine hbase.const_mul 2 |>.congr ?_
  intro u
  ring
```

DCT:

```lean
lemma gaussianTailKernel_integral_tendsto :
    Tendsto
      (fun s : ℝ => ∫ u : ℝ, gaussianTailKernel s u)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt Real.pi)) := by
  have Hmeas :
      ∀ᶠ s in 𝓝[>] (0 : ℝ),
        AEStronglyMeasurable (gaussianTailKernel s) volume := by
    refine Eventually.of_forall ?_
    intro s
    unfold gaussianTailKernel
    measurability
  have Hpoint := gaussianTailKernel_pointwise
  have Hdom := gaussianTailKernel_dom
  have hD := integrable_gaussian_dom
  have hlim :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := volume)
      (bound := fun u : ℝ => 2 * Real.exp (-(u ^ 2)))
      Hmeas Hdom hD Hpoint
  rw [integral_exp_neg_sq]
  simpa using hlim
```

This DCT proof is the cleanest way to handle the moving lower limit.

### 3. Exact central change of variables

Use the interval route. The finite-interval identity is the robust primitive:

```lean
lemma gaussianTail_central_interval_change
    {s B : ℝ} (hs : 0 < s)
    (hB : gaussianTailCut s ≤ B) :
    (∫ v in gaussianTailCut s..B,
        Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
      =
    (2 * Real.sqrt s / C) *
      ∫ u in gaussianTailAlpha s..(Real.sqrt s * (B - C / (2 * s))),
        Real.exp (-(u ^ 2)) / (1 + gaussianTailBeta s * u) := by
  -- Recommended proof:
  -- use `intervalIntegral.integral_comp_mul_deriv'` with
  --   φ u = C/(2*s) + u / Real.sqrt s
  --   φ' u = 1 / Real.sqrt s
  -- over `u ∈ [alpha, betaB]`.
  --
  -- This is the same API already used in `modelSaddleInterval_substitution`.
  -- The repo call is:
  --   intervalIntegral.integral_comp_mul_deriv'
  -- in `ModelSaddleIntegral.lean`. fileciteturn156file0L142-L164
  --
  -- The algebra:
  --   v = C/(2s) + u/√s
  --   s(v-C/(2s))² = u²
  --   1/v * dv = (2√s/C) * 1/(1+(2√s/C)u) du.
  --
  -- This lemma is the one finite-interval change-of-variable brick I recommend
  -- implementing and keeping local.
  ...
```

I am not filling this with invented Lean term-code because this is exactly the API-sensitive part: it depends on how your local v4.29.0 elaborates `intervalIntegral.integral_comp_mul_deriv'` for the affine map. The lemma name is confirmed by your repo’s existing use. The theorem is straightforward once the finite interval substitution is accepted.

Then pass `B → ∞` using the same pattern as `modelSaddleIoi_substitution`:

```lean
lemma gaussianTail_central_change {s : ℝ} (hs : 0 < s) :
    (∫ v in Set.Ioi (gaussianTailCut s),
        Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
      =
    (2 * Real.sqrt s / C) *
      ∫ u : ℝ, gaussianTailKernel s u := by
  -- Use:
  --   intervalIntegral_tendsto_integral_Ioi
  -- on the `v` side, lower `gaussianTailCut s`;
  -- on the `u` side, lower `gaussianTailAlpha s`.
  --
  -- The right set integral is expressed as an integral over all ℝ of an indicator,
  -- `gaussianTailKernel`.
  --
  -- This is exactly the `B → ∞` pattern in:
  --   modelSaddleIoi_substitution
  -- where the repo uses
  --   intervalIntegral_tendsto_integral_Ioi
  -- twice and `tendsto_nhds_unique`.
  -- fileciteturn157file0L56-L70
  ...
```

Again, the exact theorem names are confirmed:
```lean
intervalIntegral_tendsto_integral_Ioi
tendsto_nhds_unique
```
both used in `modelSaddleIoi_substitution`. fileciteturn157file0L56-L70

### 4. Far-left strip is negligible

```lean
lemma gaussianTail_left_negligible :
    Tendsto
      (fun s : ℝ =>
        (∫ v in Set.Ioc (1 : ℝ) (gaussianTailCut s),
            Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
          / Real.sqrt s)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  -- Bound eventually:
  --   0 ≤ integral ≤ (C/(4s)) * exp(-C^2/(16s)).
  --
  -- Reason:
  -- for `1 ≤ v ≤ C/(4s)`, `v ≤ v0/2`, so
  -- `|v-v0| ≥ v0/2 = C/(4s)`, hence
  -- `exp(-s(v-v0)^2) ≤ exp(-C^2/(16s))`,
  -- and `1/v ≤ 1`.
  --
  -- Then
  --   integral / sqrt s ≤ (C/4) * s^(-3/2) * exp(-C^2/(16s)) → 0.
  --
  -- Use the repo/Mathlib lemma already used elsewhere:
  --   tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
  -- after substituting `x = 1/s`.
  -- This lemma is used in `ErdosKernel.lean` for polynomial-times-exponential decay.
  -- fileciteturn71file0L150-L164
  ...
```

### 5. Assemble the Gaussian tail ratio

```lean
lemma gaussianTail_asymp :
    Tendsto
      (fun s : ℝ =>
        (∫ v in Set.Ioi (1 : ℝ),
            Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
          / ((2 * Real.sqrt Real.pi / C) * Real.sqrt s))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hcentral :
      Tendsto
        (fun s : ℝ =>
          (∫ v in Set.Ioi (gaussianTailCut s),
              Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
            / ((2 * Real.sqrt Real.pi / C) * Real.sqrt s))
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hG := gaussianTailKernel_integral_tendsto
    -- use `gaussianTail_central_change`
    -- central integral = `(2√s/C) * ∫ gaussianTailKernel s`
    -- divide by `(2√π/C)√s`, getting `(∫ kernel)/√π → 1`.
    ...

  have hleft :=
    gaussianTail_left_negligible

  -- Split `Set.Ioi 1` into `Set.Ioc 1 (gaussianTailCut s) ∪ Set.Ioi (gaussianTailCut s)`
  -- eventually, when `1 ≤ gaussianTailCut s`.
  --
  -- APIs:
  --   Set.Ioc_union_Ioi_eq_Ioi
  --   MeasureTheory.setIntegral_union
  --
  -- This is the same set-integral union API your repo uses in `MassRateIntegral`.
  -- fileciteturn150file0L12-L28
  ...
```

## Answers to the exact API questions

### (a) Linear change of variables on `Set.Ioi`

I recommend **intervals then \(B\to\infty\)**.

Use:

```lean
intervalIntegral.integral_comp_mul_deriv'
intervalIntegral_tendsto_integral_Ioi
tendsto_nhds_unique
```

The first is confirmed by the current file’s `modelSaddleInterval_substitution`; the second and third are confirmed by `modelSaddleIoi_substitution`. fileciteturn156file0L142-L164 fileciteturn157file0L56-L70

Do not use a direct `MeasurePreserving` affine-map proof unless you already have a local lemma for affine images of `volume` ready. It is more abstract and usually more painful than the interval route in this project.

### (b) Moving-lower-limit DCT

Use:

```lean
MeasureTheory.tendsto_integral_filter_of_dominated_convergence
```

with functions on all of `ℝ`:
```lean
gaussianTailKernel s u =
  Set.indicator (Set.Ioi (gaussianTailAlpha s))
    (fun u => exp(-u^2)/(1 + gaussianTailBeta s * u)) u
```

Confirmed usage in repo: `GaussianCore.lean` uses this theorem exactly for dominated convergence to a Gaussian. fileciteturn155file0L22-L26

### (c) Gaussian integral

Use:

```lean
integral_gaussian_complex
```

or the repo wrapper `gaussian_integral_half` if your exponent is `-x²/2`. For this lemma you need `∫ exp(-x²) = √π`, so add a tiny wrapper around `integral_gaussian_complex (b := 1)`. The confirmed use of `integral_gaussian_complex` is in `GaussianCore.lean`. fileciteturn154file0L18-L40

## Practical implementation note

The only genuinely API-sensitive helper is:

```lean
gaussianTail_central_interval_change
```

Do that first on finite intervals using `intervalIntegral.integral_comp_mul_deriv'`. Once that compiles, the rest is standard: `intervalIntegral_tendsto_integral_Ioi`, DCT with `2 * exp(-u^2)`, and the exponentially small left strip.
