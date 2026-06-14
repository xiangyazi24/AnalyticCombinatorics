═══ BRIDGE ac | 9ab8bfb2 | 17946 chars 2587 words 474 lines | 283s | prov=network | OK ═══
═══ BRIDGE ac | 9ab8bfb2 | 17946 chars 2587 words 474 lines | 283s | prov=network | OK ═══
I checked the current files at `00a3d9e`. The key black boxes you list are present with the shapes you need:

`modelSaddle`, `summable_modelSaddleTerm`, and `modelSaddle_pos` are in `ErdosConstant.lean`; note that `modelSaddle` is currently in namespace `AnalyticCombinatorics.Ch8.Partitions`, not inside the `Erdos` namespace. fileciteturn165file0L54-L97

`modelSaddleIoi_substitution` and `vIntegral_eq_gaussianForm` are in `ModelSaddleIntegral.lean`, giving the chain from the \(x\)-density to the \(v\)-Gaussian form. fileciteturn157file0L56-L87

`gaussianTailKernel_integral_tendsto` and `modelGaussCut_eq` are already proved in `GaussianTail.lean`; the DCT uses `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`. fileciteturn163file0L123-L136 fileciteturn164file0L85-L140

`modelSaddle_sub_integral_bound` is present and gives the Riemann-sum error bound in terms of the shifted derivative integral plus `exp(C√3)`. fileciteturn167file0L23-L29

The honest state is: **(1) is now almost closed from committed black boxes plus one left-strip estimate; (2) still needs a real estimate not yet among the listed black boxes; (3) is clean once (1) and (2) are supplied.** I would not claim a no-sorry full proof of (2) from the current committed facts alone, because the derivative-error integral needs either a `v = sqrt (x+1)` substitution for the derivative-weighted integrand or an equivalent new comparison lemma.

Below is the clean patch structure I recommend.

---

## 1. Gaussian tail asymptotic

Add this to a file after `GaussianTail.lean`.

```lean
import AnalyticCombinatorics.Ch8.Partitions.GaussianTail

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators MeasureTheory Real
open AnalyticCombinatorics.Ch8.Partitions.Erdos
open scoped Topology Interval

noncomputable section

/-- The full Gaussian tail integral appearing after completing the square. -/
noncomputable def gaussianTailFull (s : ℝ) : ℝ :=
  ∫ v in Set.Ioi (1 : ℝ),
    Real.exp (-s * (v - C / (2 * s)) ^ 2) / v
```

First prove the easy central/cut part. This one uses only your committed `modelGaussCut_eq` and `gaussianTailKernel_integral_tendsto`.

```lean
lemma gaussianTail_cut_ratio_tendsto :
    Tendsto
      (fun s : ℝ =>
        (∫ v in Set.Ioi (gaussianTailCut s),
            Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
          / ((2 * Real.sqrt Real.pi / C) * Real.sqrt s))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hK :
      Tendsto
        (fun s : ℝ => (∫ u : ℝ, gaussianTailKernel s u) / Real.sqrt Real.pi)
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hsqrtpi : Real.sqrt Real.pi ≠ 0 := by positivity
    have h := gaussianTailKernel_integral_tendsto.div_const (Real.sqrt Real.pi)
    simpa [hsqrtpi] using h

  refine hK.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hspos : 0 < s := hs
  have hCpos : 0 < C := C_pos
  have hsqrtpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
  have hden :
      ((2 * Real.sqrt Real.pi / C) * Real.sqrt s) ≠ 0 := by positivity
  rw [modelGaussCut_eq hspos]
  field_simp [hden, hCpos.ne', hsqrtpos.ne']
  ring
```

Now add the missing left-strip lemma. This is a **small but real estimate**. It is independent of DCT.

```lean
/--
The left strip `1 < v ≤ C/(4s)` is exponentially negligible after dividing
by the Gaussian main scale.
-/
lemma gaussianTail_left_ratio_tendsto_zero :
    Tendsto
      (fun s : ℝ =>
        (∫ v in Set.Ioc (1 : ℝ) (gaussianTailCut s),
            Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
          / ((2 * Real.sqrt Real.pi / C) * Real.sqrt s))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  /-
  Proof outline:
  eventually `1 ≤ gaussianTailCut s`;
  on `v ∈ Ioc 1 (C/(4s))`,
    `v ≤ C/(4s) = v₀/2`,
  hence `|v - v₀| ≥ C/(4s)` and
    `s * (v-v₀)^2 ≥ C^2/(16s)`.
  Also `1/v ≤ 1`.
  Therefore
    ‖∫_{Ioc 1 cut} ...‖
      ≤ (volume (Ioc 1 cut)).toReal * exp(-C^2/(16s))
      ≤ (C/(4s)) * exp(-C^2/(16s)).
  After division by `(2√π/C)√s`, this is
      const * s^(-3/2) * exp(-C^2/(16s)) → 0.
  Use:
    MeasureTheory.norm_setIntegral_le_of_norm_le_const
    Real.volume_Ioc
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    tendsto_inv_nhdsGT_zero
  -/
```

I am not filling this with a fake proof term. The exact proof is mechanical but lengthy; the lemma is the correct missing brick. The API names here are stable in your repo: `norm_setIntegral_le_of_norm_le_const` is already used for near-zero set-integral bounds, and `Real.volume_Ioc` is used there too. fileciteturn150file0L30-L33 The exponential-polynomial decay lemma `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero` is used elsewhere in the project for exactly this kind of estimate.

With that strip lemma, the full asymptotic is clean:

```lean
lemma gaussianTail_asymp :
    Tendsto
      (fun s : ℝ =>
        gaussianTailFull s / ((2 * Real.sqrt Real.pi / C) * Real.sqrt s))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hcut :
      ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), 1 ≤ gaussianTailCut s := by
    -- `gaussianTailCut s = C/(4s) → ∞`.
    have hto :
        Tendsto gaussianTailCut (𝓝[>] (0 : ℝ)) atTop := by
      unfold gaussianTailCut
      have hinv : Tendsto (fun s : ℝ => 1 / s) (𝓝[>] (0 : ℝ)) atTop := by
        simpa [one_div] using tendsto_inv_nhdsGT_zero (𝕜 := ℝ)
      have hC4 : 0 < C / 4 := by positivity
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (Tendsto.const_mul_atTop hC4 hinv)
    exact hto.eventually_ge_atTop 1

  have hsplit :
      (fun s : ℝ =>
        gaussianTailFull s / ((2 * Real.sqrt Real.pi / C) * Real.sqrt s))
        =ᶠ[𝓝[>] (0 : ℝ)]
      (fun s : ℝ =>
        ((∫ v in Set.Ioc (1 : ℝ) (gaussianTailCut s),
              Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
          / ((2 * Real.sqrt Real.pi / C) * Real.sqrt s))
        +
        ((∫ v in Set.Ioi (gaussianTailCut s),
              Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
          / ((2 * Real.sqrt Real.pi / C) * Real.sqrt s))) := by
    filter_upwards [self_mem_nhdsWithin, hcut] with s hs hcut1
    have hspos : 0 < s := hs
    have hden : ((2 * Real.sqrt Real.pi / C) * Real.sqrt s) ≠ 0 := by
      positivity

    have hfun_int :
        IntegrableOn
          (fun v : ℝ => Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
          (Set.Ioi (1 : ℝ)) := by
      -- dominated by the global shifted Gaussian on the tail `v > 1`
      -- If you already have this in the file, use it directly.
      exact (integrable_gaussShift hspos).integrableOn.mono_set (by
        intro v hv
        trivial)

    have hIoc :
        IntegrableOn
          (fun v : ℝ => Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
          (Set.Ioc (1 : ℝ) (gaussianTailCut s)) :=
      hfun_int.mono_set (by intro v hv; exact hv.1)

    have hIoi :
        IntegrableOn
          (fun v : ℝ => Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
          (Set.Ioi (gaussianTailCut s)) :=
      hfun_int.mono_set (by intro v hv; exact lt_of_le_of_lt hcut1 hv)

    have hdisj : Disjoint (Set.Ioc (1 : ℝ) (gaussianTailCut s))
        (Set.Ioi (gaussianTailCut s)) := by
      refine Set.disjoint_left.mpr ?_
      intro v hv1 hv2
      exact not_lt_of_ge hv1.2 hv2

    have hsets :
        Set.Ioc (1 : ℝ) (gaussianTailCut s) ∪ Set.Ioi (gaussianTailCut s)
          = Set.Ioi (1 : ℝ) :=
      Set.Ioc_union_Ioi_eq_Ioi hcut1

    have hunion :=
      MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hIoc hIoi

    unfold gaussianTailFull
    rw [← hsets] at hunion
    rw [hunion]
    field_simp [hden]
    ring

  have hsum :=
    gaussianTail_left_ratio_tendsto_zero.add gaussianTail_cut_ratio_tendsto
  exact hsum.congr' hsplit.symm
```

The set-integral split uses the same `MeasureTheory.setIntegral_union` API already used elsewhere in the repo. fileciteturn150file0L12-L28

---

## 2. Riemann-error / derivative integral is `o(main)`

Your proposed statement should be given a name and proved as a separate theorem:

```lean
/--
The mesh-1 Riemann error in `modelSaddle_sub_integral_bound` is negligible
relative to the saddle main scale.
-/
lemma modelSaddle_riemann_error_negligible :
    Tendsto
      (fun s : ℝ =>
        ((∫ x in Set.Ioi (0 : ℝ),
            |saddleDensity s (x + 1) *
              (C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹)|)
          + Real.exp (C * Real.sqrt 3))
          / (Real.sqrt s * Real.exp (A / s)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  /-
  This is the real remaining estimate. The clean proof is:

  1. Change variables `x+1 = y^2`, as in `modelSaddleIoi_substitution`,
     but for the derivative-weighted integrand:
       D(s) =
         ∫_{y>1} 2 e^{Cy-sy²}/y *
           |C/(2y) - s - 1/y²| dy.

  2. Split at `gaussianTailCut s = C/(4s)` in the `y` variable.

  3. Left strip `1 < y ≤ C/(4s)`:
       exponentially negligible, same as `gaussianTail_left_ratio_tendsto_zero`,
       with an extra polynomial factor.

  4. Right strip `y ≥ C/(4s)`:
       |C/(2y) - s - 1/y²| ≤ K*s   eventually.
     Indeed `C/(2y) ≤ 2s`, `1/y² ≤ 16s²/C² ≤ const*s`.
     Hence
       D_right(s) ≤ K*s * ∫_{y≥cut} 2e^{Cy-sy²}/y dy.
     By `vIntegral_eq_gaussianForm` + `gaussianTail_asymp`,
       ∫_{y≥cut} 2e^{Cy-sy²}/y = O(√s e^{A/s}).
     Therefore
       D_right(s)/(√s e^{A/s}) = O(s) → 0.

  5. The fixed constant `exp(C√3)/(√s e^{A/s}) → 0`
     by `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`
     composed with `s ↦ 1/s`.

  Required additional helper lemma:
  - derivative-weighted `x+1 = y²` substitution, analogous to
    `modelSaddleIoi_substitution`, using the same finite-interval
    `intervalIntegral.integral_comp_mul_deriv'` + `intervalIntegral_tendsto_integral_Ioi`
    route already committed for the unweighted case.
  -/
```

This is the piece I cannot honestly replace with a one-screen proof. The proof needs one new substitution lemma for the derivative-weighted integral. The unweighted substitution is already in your repo (`modelSaddleIoi_substitution`), but it does not apply directly to the absolute-value/bracket integrand. fileciteturn157file0L56-L70

The sharp right-strip bound you want to prove after substitution is:

```lean
lemma saddleDerivativeFactor_right_bound :
    ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
      ∀ y : ℝ, gaussianTailCut s ≤ y →
        |C / (2 * y) - s - 1 / y ^ 2| ≤
          (3 + 16 / C ^ 2) * s := by
  -- since y ≥ C/(4s):
  -- C/(2y) ≤ 2s,
  -- 1/y² ≤ 16s²/C² ≤ 16s/C² for s≤1.
```

Then the rest is Tendsto plumbing.

---

## 3. Main integral ratio and `modelSaddle_log_asymp`

Once you have `gaussianTail_asymp` and `modelSaddle_riemann_error_negligible`, the final proof is relatively short.

First add a translation lemma. I recommend the **interval route**, not a direct measure-preserving set lemma. The direct `MeasurePreserving` name for translations is not one I would rely on without checking the environment. The interval API is already used in your repo.

```lean
lemma saddleDensity_shift_integral_eq_Ioi1 {s : ℝ} (hs : 0 < s) :
    (∫ x in Set.Ioi (0 : ℝ), saddleDensity s (x + 1))
      =
    ∫ x in Set.Ioi (1 : ℝ), saddleDensity s x := by
  /-
  Recommended proof:
  prove finite interval identity
    ∫ x in (0)..B, saddleDensity s (x+1)
      = ∫ y in (1)..(B+1), saddleDensity s y
  using `intervalIntegral.integral_comp_add_right` or the equivalent
  affine substitution lemma.

  Then pass `B → ∞` on both sides using
    intervalIntegral_tendsto_integral_Ioi

  This is exactly the pattern already used by `modelSaddleIoi_substitution`.
  -/
```

Name note: `intervalIntegral.integral_comp_add_right` is the name I expect, but I would flag it as **uncertain in v4.29.0**. If it is absent, use `intervalIntegral.integral_comp_mul_deriv'` with the affine map `fun x => x + 1`; that lemma is definitely present because your repo uses it in `modelSaddleInterval_substitution`. fileciteturn156file0L142-L164

Now prove the continuous integral asymptotic:

```lean
lemma saddleDensity_Ioi1_ratio_asymp :
    Tendsto
      (fun s : ℝ =>
        (∫ x in Set.Ioi (1 : ℝ), saddleDensity s x)
          / ((4 * Real.sqrt Real.pi / C) * Real.sqrt s * Real.exp (A / s)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have htail := gaussianTail_asymp
  have hmain :
      Tendsto
        (fun s : ℝ =>
          (2 * Real.exp (A / s) * gaussianTailFull s)
            / ((4 * Real.sqrt Real.pi / C) * Real.sqrt s * Real.exp (A / s)))
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    refine htail.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos : 0 < s := hs
    have hCpos : 0 < C := C_pos
    have hsqrtpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
    have hexpne : Real.exp (A / s) ≠ 0 := Real.exp_ne_zero _
    unfold gaussianTailFull
    field_simp [hCpos.ne', hsqrtpos.ne', hexpne]
    ring

  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hspos : 0 < s := hs
  rw [modelSaddleIoi_substitution hspos, vIntegral_eq_gaussianForm hspos]
  rfl
```

Then the sum/integral comparison:

```lean
lemma modelSaddle_ratio_asymp :
    Tendsto
      (fun s : ℝ =>
        modelSaddle s /
          ((4 * Real.sqrt Real.pi / C) * Real.sqrt s * Real.exp (A / s)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hI1 := saddleDensity_Ioi1_ratio_asymp

  have hshift :
      Tendsto
        (fun s : ℝ =>
          (∫ x in Set.Ioi (0 : ℝ), saddleDensity s (x + 1))
            / ((4 * Real.sqrt Real.pi / C) * Real.sqrt s * Real.exp (A / s)))
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    refine hI1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [saddleDensity_shift_integral_eq_Ioi1 hs]

  have herr := modelSaddle_riemann_error_negligible

  have hone_term :
      Tendsto
        (fun s : ℝ =>
          saddleDensity s 1 /
            ((4 * Real.sqrt Real.pi / C) * Real.sqrt s * Real.exp (A / s)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    /-
    `saddleDensity s 1 = exp(C-s)`.
    Divide by `√s * exp(A/s)`; since `A>0`, this tends to 0 by
    exponential dominance.
    Use `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`
    after `x = 1/s`.
    -/
```

Now use the committed absolute error bound:

```lean
  have hdiff :
      Tendsto
        (fun s : ℝ =>
          (modelSaddle s
            - saddleDensity s 1
            - ∫ x in Set.Ioi (0 : ℝ), saddleDensity s (x + 1))
            / ((4 * Real.sqrt Real.pi / C) * Real.sqrt s * Real.exp (A / s)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hscale_pos :
        ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
          0 < (4 * Real.sqrt Real.pi / C) * Real.sqrt s * Real.exp (A / s) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      positivity
    -- `modelSaddle_sub_integral_bound` plus `modelSaddle_riemann_error_negligible`.
    -- Since `4√π/C` is a positive constant, `herr` gives the same limit after
    -- division by the full scale.
```

This last `hdiff` proof is routine but lengthy: apply `modelSaddle_sub_integral_bound hs`, divide by the positive main scale, and use `herr.const_mul (C/(4√π))`. The absolute bound source is exactly the committed lemma. fileciteturn167file0L23-L29

Finally assemble:

```lean
  -- modelSaddle/main =
  --   shiftIntegral/main + oneTerm/main + diff/main.
  have hsum := (hshift.add hone_term).add hdiff
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hden : (4 * Real.sqrt Real.pi / C) * Real.sqrt s * Real.exp (A / s) ≠ 0 := by
    positivity
  field_simp [hden]
  ring
```

The logarithmic theorem then follows:

```lean
theorem modelSaddle_log_asymp :
    Tendsto
      (fun s : ℝ =>
        Real.log (modelSaddle s)
          - A / s
          - (1 / 2 : ℝ) * Real.log s
          - Real.log (4 * Real.sqrt Real.pi / C))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hratio := modelSaddle_ratio_asymp

  have hlog :
      Tendsto
        (fun s : ℝ =>
          Real.log
            (modelSaddle s /
              ((4 * Real.sqrt Real.pi / C) * Real.sqrt s * Real.exp (A / s))))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto
    simpa using hcont.comp hratio

  refine hlog.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hspos : 0 < s := hs
  have hMSpos : 0 < modelSaddle s := modelSaddle_pos hspos
  have hKpos : 0 < 4 * Real.sqrt Real.pi / C := by
    exact div_pos (by positivity) C_pos
  have hsqrtpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
  have hdenpos :
      0 < (4 * Real.sqrt Real.pi / C) * Real.sqrt s * Real.exp (A / s) := by
    positivity

  rw [Real.log_div hMSpos.ne' hdenpos.ne']
  rw [Real.log_mul hKpos.ne' (mul_ne_zero hsqrtpos.ne' (Real.exp_ne_zero _))]
  rw [Real.log_mul hsqrtpos.ne' (Real.exp_ne_zero _)]
  rw [Real.log_exp]
  rw [Real.log_sqrt hspos.le]
  ring
```

This final theorem’s algebra is standard and uses the same log APIs already present in `ErdosConstant.lean`: `Real.log_div`, `Real.log_mul`, `Real.log_exp`, `Real.log_sqrt`. fileciteturn165file0L131-L146

---

## Exact translation lemma answer

For
```lean
∫ x in Set.Ioi 0, f (x + 1) = ∫ x in Set.Ioi 1, f x
```
I recommend **not** using a direct set-level `MeasurePreserving` lemma unless you already know the exact name in your local Mathlib. The robust route is:

1. finite interval identity with affine substitution,
2. pass to `Ioi` by `intervalIntegral_tendsto_integral_Ioi`.

Use:

```lean
intervalIntegral.integral_comp_mul_deriv'
intervalIntegral_tendsto_integral_Ioi
tendsto_nhds_unique
```

These exact names are confirmed by the repo: `integral_comp_mul_deriv'` is used in `modelSaddleInterval_substitution`, and `intervalIntegral_tendsto_integral_Ioi` is used in `modelSaddleIoi_substitution`. fileciteturn156file0L142-L164 fileciteturn157file0L56-L70

The name `intervalIntegral.integral_comp_add_right` may exist, but I would flag it as **uncertain** for v4.29.0. The affine `integral_comp_mul_deriv'` route is confirmed in your repo and avoids relying on a direct translation theorem.
