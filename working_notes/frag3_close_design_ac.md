Yes: build a **new narrow-window `SecondOrderHAdmissible`** over `fragPermThirdWindowHAdmissible`, reusing the wide-window proof everywhere except the new narrow tail. The saddle sequence and the correction constants stay the same.

## 1. Narrow `local_second_L1` from wide `local_second_L1`

This part should be a monotonicity lemma.

Let

```lean
δ₃ n ≤ δ₂ n
κ₃ n := δ₃ n * Real.sqrt (b n)
κ₂ n := δ₂ n * Real.sqrt (b n)
```

where `δ₂ ≈ s^(6/5)` is the existing wide window and `δ₃ ≈ s^(29/20)` is the new narrow window. Since `s → 0` and `29/20 > 6/5`, eventually

```lean
δ₃ n ≤ δ₂ n
```

so also

```lean
κ₃ n ≤ κ₂ n
```

provided `0 ≤ sqrt (b n)`.

If the second-order local field is shaped like

```lean
local_second_L1 :
  (fun n =>
    (∫ x in Set.Icc (-κ n) (κ n),
      ‖gauss x * (localRatio n x - secondPoly n x)‖)
      / corrScale2 n)
    =o[atTop] fun _ => 1
```

then the narrow version follows from the wide version because the integrand is nonnegative.

Useful reusable lemma:

```lean
lemma local_second_L1_of_subwindow
    (hκ : ∀ᶠ n in atTop, κ₃ n ≤ κ₂ n)
    (hκ₃_nonneg : ∀ᶠ n in atTop, 0 ≤ κ₃ n)
    (hwide :
      (fun n =>
        (∫ x in Set.Icc (-(κ₂ n)) (κ₂ n), F n x)
          / corrScale2 n)
        =o[atTop] fun _ : ℕ => 1)
    (hF_nonneg : ∀ᶠ n in atTop, ∀ x, 0 ≤ F n x)
    (hcorr_pos : ∀ᶠ n in atTop, 0 < corrScale2 n) :
      (fun n =>
        (∫ x in Set.Icc (-(κ₃ n)) (κ₃ n), F n x)
          / corrScale2 n)
        =o[atTop] fun _ : ℕ => 1 := by
  -- eventually:
  --   Set.Icc (-κ₃) κ₃ ⊆ Set.Icc (-κ₂) κ₂
  -- and `F ≥ 0`, so the integral over the small interval is ≤ wide integral.
  --
  -- Then apply squeeze / `isLittleO_of_le`.
  sorry
```

Depending on whether your file uses `setIntegral` or `intervalIntegral`, the core monotonicity lemma should be one of:

```lean
MeasureTheory.setIntegral_mono_on
MeasureTheory.integral_mono_ae
intervalIntegral.integral_mono_on
intervalIntegral.integral_mono_interval
```

If those exact names are awkward, the robust route is to rewrite the small integral as an integral of an indicator over the large set:

```lean
∫ x in Set.Icc (-κ₃) κ₃, F n x
=
∫ x in Set.Icc (-κ₂) κ₂,
  Set.indicator (Set.Icc (-κ₃) κ₃) (F n) x
```

then use

```lean
MeasureTheory.integral_mono_ae
```

with

```lean
0 ≤ Set.indicator small F x ≤ F x.
```

There is no conceptual pitfall if

```lean
corrScale2
```

is the second-order correction scale of the function/saddle, not of the window. It should be window-independent. For fragmented permutations,

```lean
corrScale2 n ≍ s n
```

or whatever your existing second-order scale is; changing the window does not change `b`, `b₃`, `b₄`, or `δ₁`.

So yes: narrow `local_second_L1` should be inherited from wide `local_second_L1` by domain monotonicity.

---

## 2. Narrow `tail_second_uniform`

The wide tail does **not** imply the narrow tail, because

```lean
{θ | δ₃ n ≤ |θ| ∧ |θ| ≤ π}
```

is larger than

```lean
{θ | δ₂ n ≤ |θ| ∧ |θ| ≤ π}.
```

Split the narrow tail:

```lean
δ₃ ≤ |θ| ≤ π
=
(δ₃ ≤ |θ| ∧ |θ| ≤ δ₂)
∪
(δ₂ ≤ |θ| ∧ |θ| ≤ π).
```

The second piece is the old wide tail. The first piece is the “sliver” and should be killed by the local quadratic drop, because it still lies inside the wide local window.

Prove a lemma like:

```lean
lemma tail_narrow_of_tail_wide_and_sliver
    (hδ_le : ∀ᶠ n in atTop, δ₃ n ≤ δ₂ n)
    (hwideTail :
      tailBound δ₂ =o[atTop] corrScale2)
    (hsliver :
      sliverBound δ₃ δ₂ =o[atTop] corrScale2) :
      tailBound δ₃ =o[atTop] corrScale2 := by
  -- split domain, use triangle / integral over union
  -- tail_narrow ≤ sliver + tail_wide
  -- then `isLittleO.add`
  sorry
```

For the sliver, use the local quadratic estimate. For fragmented permutations with

```lean
s n := 1 - r n
b n ≍ 2 * (s n)^(-3)
δ₃ n := (s n)^(29/20)
```

we have

```lean
b n * (δ₃ n)^2
  ≍ s^(-3) * s^(29/10)
  = s^(-1/10) → ∞.
```

So the sliver is exponentially small:

```lean
sliverRatio n ≤ C * exp (-c * b n * (δ₃ n)^2).
```

This beats any polynomial scale in `s`.

A Lean lemma to isolate:

```lean
lemma exp_neg_b_delta3_sq_isLittleO_corrScale2
    (hb : (fun n => b n) ~[atTop] fun n => 2 * (s n)^(-3 : ℤ))
    (hδ₃ : ∀ᶠ n in atTop, δ₃ n = (s n) ^ (29 / 20 : ℝ))
    (hs : Tendsto s atTop (𝓝[>] 0))
    (hcorr_poly : corrScale2 =O[atTop] fun n => (s n) ^ (1 : ℝ)) :
    (fun n => Real.exp (-c * b n * (δ₃ n)^2))
      =o[atTop] corrScale2 := by
  -- reduce exponent to `exp (-c' * s^(-1/10))`
  -- use `exp_neg_inv_power_isLittleO_power`
  sorry
```

You may want a generic version:

```lean
lemma exp_neg_inv_power_isLittleO_power
    {s : ℕ → ℝ} {α β c : ℝ}
    (hs_pos : ∀ᶠ n in atTop, 0 < s n)
    (hs_zero : Tendsto s atTop (𝓝 0))
    (hα : 0 < α)
    (hβ : 0 < β)
    (hc : 0 < c) :
    (fun n => Real.exp (-c * (s n)^(-α)))
      =o[atTop] fun n => (s n)^β := by
  -- standard: exponential beats powers
  sorry
```

Then the sliver proof has this shape:

```lean
lemma frag_sliver_tail_second_narrow
    (hquad :
      ∀ᶠ n in atTop,
        ∀ θ, δ₃ n ≤ |θ| → |θ| ≤ δ₂ n →
          localModRatio n θ ≤ Real.exp (-c * b n * θ^2)) :
    sliverBound δ₃ δ₂ =o[atTop] corrScale2 := by
  -- On the sliver:
  --   exp(-c*b*θ²) ≤ exp(-c*b*δ₃²).
  -- Length is ≤ 2π or ≤ 2δ₂; either is harmless.
  -- Therefore:
  --   sliverBound ≤ C * exp(-c*b*δ₃²).
  exact exp_neg_b_delta3_sq_isLittleO_corrScale2 ...
```

So the narrow second-order tail should be:

```lean
tail_narrow ≤ tail_wide + sliver
```

with

```lean
tail_wide = o(corrScale2)
sliver = o(corrScale2).
```

The existing second-order tail argument extends only if it exposes an exponential estimate or a reusable local quadratic estimate. If the old theorem states merely

```lean
tail_wide = o(corrScale2),
```

then it does not cover the sliver; you need this one new sliver lemma.

---

## 3. Same saddle sequence and same `δ₁`, `δ₂`

The saddle radius is independent of the window. For fragmented permutations it is still defined by

```lean
r n / (1 - r n)^2 = n
```

or your existing `SaddleSequence`.

The window only changes the proof decomposition of the contour integral:

```text
local region + tail region.
```

It does not change:

```lean
b n
b₃ n
b₄ n
b₅ n
b₆ n
δ₁ n
δ₂ n
scale n
corrScale2 n
corrScale3 n
```

So the narrow-window instance gives the **same asymptotic theorem** as the wide-window instance would, but with enough Taylor control for third order.

In Lean, it is worth making these definitions fields of `hf` only if they are genuinely window-dependent. Ideally:

```lean
hf.saddleRadius
hf.b
hf.b3
hf.b4
hf.b5
hf.b6
```

depend on the function and saddle sequence, while

```lean
hf.window
```

is a proof parameter. Then the identity proof is just `rfl`.

If your structures bundle `δ₁` and `δ₂` through the `HAdmissible` object, add bridge lemmas:

```lean
lemma frag_delta1_thirdWindow_eq_wide :
    delta1 fragPermThirdWindowHAdmissible hr
      =
    delta1 fragPermWideWindowHAdmissible hr := by
  rfl

lemma frag_delta2_thirdWindow_eq_wide :
    delta2 fragPermThirdWindowHAdmissible hr
      =
    delta2 fragPermWideWindowHAdmissible hr := by
  rfl
```

If not `rfl`, prove by unfolding `delta1`, `delta2`, and the `b_k` definitions.

---

## 4. Minimal new lemmas, dependency order

Here is the leanest dependency list.

### A. Window comparison

```lean
lemma frag_third_window_le_second_window :
    ∀ᶠ n in atTop, δ₃ n ≤ δ₂ n := by
  -- δ₃ = s^(29/20), δ₂ = s^(6/5), 0 < s < 1 eventually,
  -- and 29/20 > 6/5.
  sorry
```

Also:

```lean
lemma frag_kappa_third_le_second :
    ∀ᶠ n in atTop,
      δ₃ n * Real.sqrt (b n) ≤ δ₂ n * Real.sqrt (b n) := by
  filter_upwards [frag_third_window_le_second_window, hb_pos] with n hδ hb
  exact mul_le_mul_of_nonneg_right hδ (Real.sqrt_nonneg _)
```

### B. Local L1 restriction lemma, generic

```lean
lemma local_second_L1_restrict_window
    (hκ : ∀ᶠ n in atTop, κsmall n ≤ κbig n)
    (hsmall_nonneg : ∀ᶠ n in atTop, 0 ≤ κsmall n)
    (hF_nonneg : ∀ᶠ n in atTop, ∀ x, 0 ≤ F n x)
    (hbig :
      (fun n =>
        (∫ x in Set.Icc (-(κbig n)) (κbig n), F n x)
          / corr n)
        =o[atTop] fun _ : ℕ => 1)
    (hcorr_pos : ∀ᶠ n in atTop, 0 < corr n) :
      (fun n =>
        (∫ x in Set.Icc (-(κsmall n)) (κsmall n), F n x)
          / corr n)
        =o[atTop] fun _ : ℕ => 1 := by
  -- monotonicity of nonnegative set integrals + squeeze
  sorry
```

Use this to fill the narrow `local_second_L1`.

### C. Sliver decomposition

```lean
lemma tail_narrow_le_sliver_add_tail_wide :
    ∀ᶠ n in atTop,
      tail δ₃ n ≤ sliver δ₃ δ₂ n + tail δ₂ n := by
  -- set inclusion / split:
  -- {δ₃ ≤ |θ| ≤ π}
  --   ⊆ {δ₃ ≤ |θ| ≤ δ₂} ∪ {δ₂ ≤ |θ| ≤ π}
  sorry
```

### D. Sliver exponential estimate

```lean
lemma frag_sliver_bound :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ᶠ n in atTop,
        sliver δ₃ δ₂ n
          ≤ C * Real.exp (-c * b n * (δ₃ n)^2) := by
  -- local quadratic drop on the wide local window
  -- and length bound for the sliver
  sorry
```

### E. Exponential beats third/second scales

For second-order structure over the narrow window, prove it against `corrScale2`.

```lean
lemma frag_exp_sliver_isLittleO_corrScale2 :
    (fun n => Real.exp (-c * b n * (δ₃ n)^2))
      =o[atTop] corrScale2 := by
  -- b δ₃² ≍ s^(-1/10)
  -- exponential beats powers
  sorry
```

For third-order tail, you will also need the same with `corrScale3`:

```lean
lemma frag_exp_sliver_isLittleO_corrScale3 :
    (fun n => Real.exp (-c * b n * (δ₃ n)^2))
      =o[atTop] corrScale3 := by
  -- same proof; corrScale3 is still polynomial in s
  sorry
```

### F. Narrow second-order tail

```lean
lemma frag_tail_second_narrow :
    tail_second fragPermThirdWindowHAdmissible
      =o[atTop] corrScale2 := by
  have hsplit := tail_narrow_le_sliver_add_tail_wide
  have hwide := FragmentedPermSecondOrder.tail_second_uniform
  have hsliver := frag_sliver_bound + frag_exp_sliver_isLittleO_corrScale2
  -- squeeze and add little-o terms
  sorry
```

### G. Construct the narrow second-order instance

```lean
def FragmentedPermSecondOrderThirdWindow :
    SecondOrderHAdmissible fragPermThirdWindowHAdmissible := by
  refine
  { local_second_L1 := ?_
    tail_second_uniform := ?_
    -- all algebraic derivative fields reused from wide instance
    -- all scale/correction fields by rfl or copied
  }
  · exact local_second_L1_restrict_window ...
  · exact frag_tail_second_narrow
```

### H. Third-order local and tail for narrow window

The third-order local proof uses the narrow window directly:

```lean
lemma frag_local_third_L1_narrow :
    local_third_L1 fragPermThirdWindowHAdmissible
      =o[atTop] corrScale3 := by
  -- Taylor remainder through order 6.
  -- Need:
  --   s^(-8) * δ₃^7 = o(corrScale3)
  -- For δ₃ = s^(29/20), this is s^(43/20).
  -- If corrScale3 = s^2, then s^(43/20) = o(s^2).
  sorry
```

Third-order tail:

```lean
lemma frag_tail_third_narrow :
    tail_third fragPermThirdWindowHAdmissible
      =o[atTop] corrScale3 := by
  -- same split as second-order:
  -- wide tail + sliver.
  -- If wide tail theorem is only second-order, use the explicit old
  -- exponential tail bound, not merely `o(corrScale2)`.
  sorry
```

Then:

```lean
def FragmentedPermThirdOrder :
    ThirdOrderHAdmissible
      fragPermThirdWindowHAdmissible
      FragmentedPermSecondOrderThirdWindow := by
  refine
  { local_third_L1 := frag_local_third_L1_narrow
    tail_third_uniform := frag_tail_third_narrow
    -- derivative/correction identities
  }
```

### I. Final theorem

```lean
theorem fragmentedPerm_coeff_third :
    coeffRatioFragPerm n
      - (1 + δ₁ n + δ₂ n)
      =o[atTop] corrScale3 := by
  exact
    coeff_thirdOrder_saddle
      (hf := fragPermThirdWindowHAdmissible)
      (h2 := FragmentedPermSecondOrderThirdWindow)
      (h3 := FragmentedPermThirdOrder)
      (hr := fragmentedPermSaddleSequence)
```

## Main takeaways

The strategy is:

```text
wide second-order local  -> narrow second-order local by monotonicity
wide second-order tail   -> narrow tail = wide tail + local sliver
local sliver             -> exponential via quadratic drop
third-order local        -> new narrow Taylor proof
third-order tail         -> same exponential tail/sliver machinery
same saddle              -> same δ₁, δ₂
```

The only genuinely new finite-radius analytic lemma is the sliver estimate:

```lean
sliver(δ₃, δ₂) ≤ C * exp(-c * b * δ₃^2),
```

plus the elementary fact that this exponential is `o(corrScale2)` and `o(corrScale3)`.
