import AnalyticCombinatorics.Ch8.Partitions.ErdosFinal

/-!
# Discharging the mesh-1 Riemann error (`RiemannErrorNegligible`)

The last hypothesis of `erdos_limit_constant`. We show the bracket-weighted error
integral is `o(mainScale)` by splitting `(0,∞)` at the saddle cutoff `x+1 = (C/4s)²`:

* on the right (`x+1 ≥ (C/4s)²`) the bracket `C/(2√(x+1)) − s − (x+1)⁻¹` is `≤ 2s`;
* on the left (`x+1 ≤ (C/4s)²`) the bracket is bounded by `C/2+s+1`, and the bulk
  `∫ saddleDensity` over that strip is `o(mainScale)` (same complete-square + the
  already-proved `gaussianTail_left_ratio_tendsto_zero`).
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators MeasureTheory Real
open AnalyticCombinatorics.Ch8.Partitions.Erdos
open scoped Topology Interval

noncomputable section

/-- Pointwise bracket bound on the whole shifted ray `x > 0`: `|bracket| ≤ C/2+s+1`. -/
lemma abs_bracket_le_const {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    |C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹| ≤ C / 2 + s + 1 := by
  have hCpos : 0 < C := C_pos
  have hx1 : (1 : ℝ) ≤ x + 1 := by linarith
  have hxpos : (0 : ℝ) < x + 1 := by linarith
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (x + 1) := by
    nlinarith [Real.sq_sqrt hxpos.le, Real.sqrt_nonneg (x + 1), hx1]
  have hsqrtpos : 0 < Real.sqrt (x + 1) := by positivity
  have hterm_le : C / (2 * Real.sqrt (x + 1)) ≤ C / 2 := by
    gcongr <;> nlinarith [hsqrt1, hCpos]
  have hterm_pos : 0 ≤ C / (2 * Real.sqrt (x + 1)) := by positivity
  have hinv_le : (x + 1)⁻¹ ≤ 1 := by
    rw [← one_div]; exact (div_le_one hxpos).mpr hx1
  have hinv_pos : 0 ≤ (x + 1)⁻¹ := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- Pointwise bracket bound on the right region `x+1 ≥ (C/4s)²`: `|bracket| ≤ 2s`
(needs `16s ≤ C²`, eventually true as `s→0⁺`). -/
lemma abs_bracket_le_two_s {s x : ℝ} (hs : 0 < s) (hsmall : 16 * s ≤ C ^ 2)
    (hx : (gaussianTailCut s) ^ 2 - 1 ≤ x) :
    |C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹| ≤ 2 * s := by
  have hCpos : 0 < C := C_pos
  have hcutpos : 0 < C / (4 * s) := by positivity
  have hcutle : (C / (4 * s)) ^ 2 ≤ x + 1 := by
    have h2 : (gaussianTailCut s) ^ 2 ≤ x + 1 := by linarith [hx]
    rwa [show gaussianTailCut s = C / (4 * s) from rfl] at h2
  have hxpos : 0 < x + 1 := by nlinarith [hcutpos, hcutle]
  have hsqrtpos : 0 < Real.sqrt (x + 1) := Real.sqrt_pos.mpr hxpos
  have hsqrtcut : C / (4 * s) ≤ Real.sqrt (x + 1) := by
    nlinarith [Real.sq_sqrt hxpos.le, Real.sqrt_nonneg (x + 1), hcutle, hcutpos]
  have hcleared : C ≤ 4 * s * Real.sqrt (x + 1) := by
    have h := hsqrtcut
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * s)] at h
    linarith [h]
  have hupper : C / (2 * Real.sqrt (x + 1)) ≤ 2 * s := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt (x + 1))]
    nlinarith [hcleared]
  have hterm_pos : 0 ≤ C / (2 * Real.sqrt (x + 1)) := by positivity
  have hmul : C ^ 2 ≤ 16 * s ^ 2 * (x + 1) := by
    have h := hcutle
    rw [show (C / (4 * s)) ^ 2 = C ^ 2 / (16 * s ^ 2) by ring,
      div_le_iff₀ (by positivity : (0 : ℝ) < 16 * s ^ 2)] at h
    linarith [h]
  have hinv_le : (x + 1)⁻¹ ≤ s := by
    rw [← one_div, div_le_iff₀ hxpos]
    nlinarith [hmul, hsmall, hs]
  have hinv_pos : 0 ≤ (x + 1)⁻¹ := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- The bracket-weighted error integrand is integrable on `(0,∞)` (dominated by
`(C/2+s+1)·saddleDensity s (·+1)`). -/
lemma integrableOn_errIntegrand {s : ℝ} (hs : 0 < s) :
    IntegrableOn
      (fun x => |saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹)|)
      (Set.Ioi (0 : ℝ)) := by
  have hCpos : 0 < C := C_pos
  have hmeas : AEStronglyMeasurable
      (fun x => |saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹)|)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    apply Measurable.aestronglyMeasurable; unfold saddleDensity; fun_prop
  have hdom : IntegrableOn (fun x => (C / 2 + s + 1) * saddleDensity s (x + 1)) (Set.Ioi 0) :=
    (integrableOn_saddleDensity_shift hs).const_mul _
  refine hdom.mono' hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with x hx
  have hx0 : 0 < x := hx
  have hxpos : 0 < x + 1 := by linarith
  have hsd : 0 ≤ saddleDensity s (x + 1) := by rw [saddleDensity]; positivity
  rw [Real.norm_eq_abs, abs_abs, abs_mul, abs_of_nonneg hsd]
  calc saddleDensity s (x + 1) * |C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹|
      ≤ saddleDensity s (x + 1) * (C / 2 + s + 1) :=
        mul_le_mul_of_nonneg_left (abs_bracket_le_const hs hx0) hsd
    _ = (C / 2 + s + 1) * saddleDensity s (x + 1) := by ring

/-- The left bulk `∫_{Ioc 0 (cut²−1)} saddleDensity s (·+1)` equals
`2 e^{A/s}·∫_{Ioc 1 cut} e^{-s(v-v₀)²}/v` (translation + `x=v²` + complete square). -/
lemma leftBulk_eq {s : ℝ} (hs : 0 < s) (hcut : 1 ≤ gaussianTailCut s) :
    (∫ x in Set.Ioc (0 : ℝ) ((gaussianTailCut s) ^ 2 - 1), saddleDensity s (x + 1))
      = 2 * Real.exp (Partitions.A / s) *
          ∫ v in Set.Ioc (1 : ℝ) (gaussianTailCut s),
            Real.exp (-s * (v - C / (2 * s)) ^ 2) / v := by
  set cut := gaussianTailCut s with hcutdef
  have hxc0 : (0 : ℝ) ≤ cut ^ 2 - 1 := by nlinarith [hcut]
  rw [← intervalIntegral.integral_of_le hxc0,
    intervalIntegral.integral_comp_add_right (saddleDensity s) 1,
    show (0 : ℝ) + 1 = 1 by norm_num, show cut ^ 2 - 1 + 1 = cut ^ 2 by ring,
    modelSaddleInterval_substitution hcut]
  have hcong : (∫ v in (1 : ℝ)..cut, 2 * Real.exp (C * v - s * v ^ 2) / v)
      = ∫ v in (1 : ℝ)..cut,
          2 * Real.exp (Partitions.A / s) * (Real.exp (-s * (v - C / (2 * s)) ^ 2) / v) := by
    apply intervalIntegral.integral_congr
    intro v _
    dsimp only
    rw [saddle_complete_square hs v, show Partitions.A / s - s * (v - C / (2 * s)) ^ 2
        = Partitions.A / s + -s * (v - C / (2 * s)) ^ 2 by ring, Real.exp_add]
    ring
  rw [hcong, intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hcut]

/-- Domain-split bound: the error integral `≤ (C/2+s+1)·LeftBulk + 2s·shiftIntegral`. -/
lemma errIntegral_le {s : ℝ} (hs : 0 < s) (hsmall : 16 * s ≤ C ^ 2)
    (hcut : 1 ≤ gaussianTailCut s) :
    (∫ x in Set.Ioi (0 : ℝ),
        |saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹)|)
      ≤ (C / 2 + s + 1) *
          (∫ x in Set.Ioc (0 : ℝ) ((gaussianTailCut s) ^ 2 - 1), saddleDensity s (x + 1))
        + 2 * s * (∫ x in Set.Ioi (0 : ℝ), saddleDensity s (x + 1)) := by
  have hCpos : 0 < C := C_pos
  set xc := (gaussianTailCut s) ^ 2 - 1 with hxcdef
  have hxc0 : (0 : ℝ) ≤ xc := by nlinarith [hcut]
  have hsub_Ioc : Set.Ioc (0 : ℝ) xc ⊆ Set.Ioi 0 := fun x hx => hx.1
  have hsub_Ioi : Set.Ioi xc ⊆ Set.Ioi (0 : ℝ) := fun x hx => lt_of_le_of_lt hxc0 hx
  have hF := integrableOn_errIntegrand hs
  have hFIoc := hF.mono_set hsub_Ioc
  have hFIoi := hF.mono_set hsub_Ioi
  have hsd := integrableOn_saddleDensity_shift hs
  have hsdIoc := hsd.mono_set hsub_Ioc
  have hsdIoixc := hsd.mono_set hsub_Ioi
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) xc) (Set.Ioi xc) := by
    refine Set.disjoint_left.mpr (fun y hy1 hy2 => ?_)
    exact absurd (Set.mem_Ioi.mp hy2) (not_lt.mpr hy1.2)
  have hunion := setIntegral_union hdisj measurableSet_Ioi hFIoc hFIoi
  rw [Set.Ioc_union_Ioi_eq_Ioi hxc0] at hunion
  -- sd union for the monotonicity step
  have hunion_sd := setIntegral_union hdisj measurableSet_Ioi hsdIoc hsdIoixc
  rw [Set.Ioc_union_Ioi_eq_Ioi hxc0] at hunion_sd
  have hLBnn : 0 ≤ ∫ x in Set.Ioc (0 : ℝ) xc, saddleDensity s (x + 1) :=
    setIntegral_nonneg measurableSet_Ioc (fun x hx => by
      have hpos : 0 < x + 1 := by linarith [hx.1]
      rw [saddleDensity]; positivity)
  have hmono : (∫ x in Set.Ioi xc, saddleDensity s (x + 1))
      ≤ ∫ x in Set.Ioi (0 : ℝ), saddleDensity s (x + 1) := by
    rw [hunion_sd]; linarith [hLBnn]
  rw [hunion]
  have hleft : (∫ x in Set.Ioc (0 : ℝ) xc,
        |saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹)|)
      ≤ (C / 2 + s + 1) * ∫ x in Set.Ioc (0 : ℝ) xc, saddleDensity s (x + 1) := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on hFIoc (hsdIoc.const_mul _) measurableSet_Ioc
    intro x hx
    have hx0 : 0 < x := hx.1
    have hsdnn : 0 ≤ saddleDensity s (x + 1) := by rw [saddleDensity]; positivity
    rw [abs_mul, abs_of_nonneg hsdnn]
    calc saddleDensity s (x + 1) * |C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹|
        ≤ saddleDensity s (x + 1) * (C / 2 + s + 1) :=
          mul_le_mul_of_nonneg_left (abs_bracket_le_const hs hx0) hsdnn
      _ = (C / 2 + s + 1) * saddleDensity s (x + 1) := by ring
  have hright : (∫ x in Set.Ioi xc,
        |saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹)|)
      ≤ 2 * s * ∫ x in Set.Ioi (0 : ℝ), saddleDensity s (x + 1) := by
    have hstep : (∫ x in Set.Ioi xc,
          |saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹)|)
        ≤ 2 * s * ∫ x in Set.Ioi xc, saddleDensity s (x + 1) := by
      rw [← integral_const_mul]
      apply setIntegral_mono_on hFIoi (hsdIoixc.const_mul _) measurableSet_Ioi
      intro x hx
      have hxxc : xc ≤ x := le_of_lt (Set.mem_Ioi.mp hx)
      have hx0 : 0 < x := lt_of_le_of_lt hxc0 (Set.mem_Ioi.mp hx)
      have hsdnn : 0 ≤ saddleDensity s (x + 1) := by rw [saddleDensity]; positivity
      rw [abs_mul, abs_of_nonneg hsdnn]
      calc saddleDensity s (x + 1) * |C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹|
          ≤ saddleDensity s (x + 1) * (2 * s) :=
            mul_le_mul_of_nonneg_left (abs_bracket_le_two_s hs hsmall hxxc) hsdnn
        _ = 2 * s * saddleDensity s (x + 1) := by ring
    calc (∫ x in Set.Ioi xc,
          |saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹)|)
        ≤ 2 * s * ∫ x in Set.Ioi xc, saddleDensity s (x + 1) := hstep
      _ ≤ 2 * s * ∫ x in Set.Ioi (0 : ℝ), saddleDensity s (x + 1) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
  linarith [hleft, hright]

/-- `LeftBulk / mainScale → 0` (the substituted strip ratio, via
`gaussianTail_left_ratio_tendsto_zero`). -/
lemma leftBulk_div_mainScale_tendsto_zero :
    Tendsto (fun s : ℝ =>
        (∫ x in Set.Ioc (0 : ℝ) ((gaussianTailCut s) ^ 2 - 1), saddleDensity s (x + 1))
          / mainScale s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  refine gaussianTail_left_ratio_tendsto_zero.congr' ?_
  filter_upwards [self_mem_nhdsWithin, eventually_one_le_cut] with s hs hcut
  have hspos : 0 < s := hs
  have hCpos : 0 < C := C_pos
  have hsqrtpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
  have hsqrtpi : (0 : ℝ) < Real.sqrt Real.pi := by positivity
  have hexpne : Real.exp (Partitions.A / s) ≠ 0 := Real.exp_ne_zero _
  have hCne : C ≠ 0 := ne_of_gt hCpos
  rw [leftBulk_eq hspos hcut]
  unfold mainScale
  set I := ∫ v in Set.Ioc (1 : ℝ) (gaussianTailCut s),
    Real.exp (-s * (v - C / (2 * s)) ^ 2) / v with hI
  field_simp
  ring

/-- The bracket-weighted error integral over `mainScale` tends to `0`. -/
lemma errIntegral_div_mainScale_tendsto_zero :
    Tendsto (fun s : ℝ =>
        (∫ x in Set.Ioi (0 : ℝ),
            |saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹)|)
          / mainScale s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hCpos : 0 < C := C_pos
  have hT1 := shiftIntegral_div_mainScale_tendsto_one
  have hLB := leftBulk_div_mainScale_tendsto_zero
  have hconst : Tendsto (fun s : ℝ => C / 2 + s + 1) (𝓝[>] (0 : ℝ)) (𝓝 (C / 2 + 0 + 1)) :=
    ((tendsto_const_nhds (x := C / 2)).add (tendsto_id.mono_left nhdsWithin_le_nhds)).add
      (tendsto_const_nhds (x := (1 : ℝ)))
  have hL : Tendsto (fun s : ℝ => (C / 2 + s + 1) *
      ((∫ x in Set.Ioc (0 : ℝ) ((gaussianTailCut s) ^ 2 - 1), saddleDensity s (x + 1))
        / mainScale s)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := hconst.mul hLB; simpa using this
  have h2s : Tendsto (fun s : ℝ => 2 * s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun s : ℝ => 2 * s) (𝓝 (0 : ℝ)) (𝓝 (2 * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hR : Tendsto (fun s : ℝ => 2 * s *
      ((∫ x in Set.Ioi (0 : ℝ), saddleDensity s (x + 1)) / mainScale s))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [zero_mul] using h2s.mul hT1
  have hupper := hL.add hR
  rw [add_zero] at hupper
  have hsmall_ev : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), 16 * s ≤ C ^ 2 := by
    have h16 : Tendsto (fun s : ℝ => 16 * s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h : Tendsto (fun s : ℝ => 16 * s) (𝓝 (0 : ℝ)) (𝓝 (16 * 0)) :=
        tendsto_const_nhds.mul tendsto_id
      rw [mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    exact h16.eventually_le_const (pow_pos hCpos 2)
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hms := mainScale_pos hs
    exact div_nonneg (setIntegral_nonneg measurableSet_Ioi (fun x _ => abs_nonneg _)) hms.le
  · filter_upwards [self_mem_nhdsWithin, eventually_one_le_cut, hsmall_ev] with s hs hcut hsmall
    have hspos : 0 < s := hs
    have hms : 0 < mainScale s := mainScale_pos hspos
    rw [div_le_iff₀ hms]
    have hexpand : ((C / 2 + s + 1) *
          ((∫ x in Set.Ioc (0 : ℝ) ((gaussianTailCut s) ^ 2 - 1), saddleDensity s (x + 1))
            / mainScale s)
        + 2 * s * ((∫ x in Set.Ioi (0 : ℝ), saddleDensity s (x + 1)) / mainScale s)) * mainScale s
        = (C / 2 + s + 1) *
            (∫ x in Set.Ioc (0 : ℝ) ((gaussianTailCut s) ^ 2 - 1), saddleDensity s (x + 1))
          + 2 * s * (∫ x in Set.Ioi (0 : ℝ), saddleDensity s (x + 1)) := by
      field_simp
    rw [hexpand]
    exact errIntegral_le hspos hsmall hcut

/-- **The mesh-1 Riemann error is negligible** — discharges the last hypothesis. -/
theorem riemannError_negligible : RiemannErrorNegligible := by
  have hCpos : 0 < C := C_pos
  have herr := errIntegral_div_mainScale_tendsto_zero
  have hexp : Tendsto (fun s : ℝ => Real.exp (C * Real.sqrt 3) / mainScale s)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_const_nhds.div_atTop mainScale_tendsto_atTop
  have hsum := herr.add hexp
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [add_div]

/-- **Erdős–Hardy–Ramanujan limit constant, unconditional in the Riemann error.**
Given only the renewal/Tauberian input `u n → a` (`a > 0`), the constant is `1/(4√3)`. -/
theorem erdos_limit_constant_of_renewal {a : ℝ} (ha : 0 < a)
    (hlim : Tendsto Erdos.u atTop (𝓝 a)) :
    a = 1 / (4 * Real.sqrt 3) :=
  erdos_limit_constant ha hlim riemannError_negligible

end

end AnalyticCombinatorics.Ch8.Partitions
