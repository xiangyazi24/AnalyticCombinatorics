import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentOneAsymp
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentTwo
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentTwoAsymp
import AnalyticCombinatorics.Ch8.Partitions.MassRateRiemannGeneral
import AnalyticCombinatorics.Ch8.Partitions.MassRateIntegral
import AnalyticCombinatorics.Ch8.Partitions.MassRateDerivInt

/-!
# Mass-rate campaign: the **two-term** moment-one asymptotic

The weak version (`sigmaMoment_one_asymp_weak`) gives only the leading term
`M₁(t) = 2(π²/6)/t³ + O(1/t²)`.  Here we extract the next order:

  `M₁(t) = 2(π²/6)/t³ − 1/(2t²) + O(1/t)`,  i.e.  `|M₁(t) − (2(π²/6)/t³ − 1/(2t²))| ≤ K/t`.

The `−1/(2t²)` term is **not** a pointwise singularity of `boseKernel2`; it is the
Riemann-sum main term of the regularized derivative.  Writing
`M₁(t) = 2(π²/6)/t³ − Σ_{k≥1} k·boseReg0′(tk)` (the weak split), the remainder sum is
`(1/t)·Σ_{k≥1} G(tk)` with `G(x) = x·boseReg0′(x)`, and the general Riemann estimate
(`riemann_sum_Ioi_sub_integral_bound`) gives `Σ_{k≥1} G(tk) = (1/t)·∫₀^∞ G + O(1)`.
The integral is `∫₀^∞ x·boseReg0′(x) dx = 1/2`, computed via `G = (x·boseReg0)′ − boseReg0`
and `∫₀^∞ boseReg0 = −1/2` with vanishing boundary terms.  Hence
`Σ_{k≥1} k·boseReg0′(tk) = 1/(2t²) + O(1/t)`.  Opus-authored (ChatGPT R14 route, repo-verified).
-/

set_option maxHeartbeats 1600000

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `G(x) = x · boseReg0′(x)`: the integrand whose Riemann sum carries the `−1/(2t²)` term. -/
noncomputable def Gw (x : ℝ) : ℝ := x * boseReg0Deriv x

/-- The derivative `G′(x) = boseReg0′(x) + x·(boseKernel3 x − 6/x⁴)`. -/
noncomputable def GwDeriv (x : ℝ) : ℝ :=
  boseReg0Deriv x + x * (boseKernel3 x - 6 / x ^ 4)

/-- Auxiliary integrability: `x·e^{−b x}` is integrable on `(1,∞)` for `b > 0`
(it is `O(e^{−(b/2)x})` at `∞`). -/
lemma id_mul_exp_neg_integrableOn_Ioi1 {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => x * Real.exp (-b * x)) (Set.Ioi (1:ℝ)) := by
  apply integrable_of_isBigO_exp_neg (b := b / 2) (by positivity)
  · exact (continuous_id.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).continuousOn
  · -- `x e^{−b x} =o e^{−(b/2) x}` ⟹ `=O`
    have hlit : (fun x : ℝ => x * Real.exp (-b * x))
        =o[atTop] (fun x : ℝ => Real.exp (-(b / 2) * x)) := by
      rw [Asymptotics.isLittleO_iff_tendsto (fun x hx => absurd hx (Real.exp_ne_zero _))]
      have hker := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (b / 2) (by positivity)
      refine hker.congr' ?_
      filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
      rw [Real.rpow_one, eq_div_iff (Real.exp_ne_zero _), mul_assoc, ← Real.exp_add,
        show -(b / 2) * x + -(b / 2) * x = -b * x from by ring]
    exact hlit.isBigO

/-- `Gw` is globally measurable. -/
lemma Gw_measurable : Measurable Gw := by
  unfold Gw
  exact measurable_id.mul boseReg0Deriv_measurable

/-- `GwDeriv` is globally measurable. -/
lemma GwDeriv_measurable : Measurable GwDeriv := by
  unfold GwDeriv boseReg0Deriv boseKernel3
  measurability

/-- `|Gw x| ≤ 32` on `(0,1]`. -/
lemma Gw_bdd_unit {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) : |Gw x| ≤ 32 := by
  rw [Gw, abs_mul, abs_of_pos hx0]
  have hb := boseReg0Deriv_bdd_near_zero hx0 hx1
  nlinarith [abs_nonneg (boseReg0Deriv x), hb, hx0.le, hx1]

/-- Integrability of `Gw` on `(0,1]`. -/
lemma Gw_integrableOn_Ioc01 : IntegrableOn Gw (Set.Ioc 0 1) := by
  have hmeas : MeasurableSet (Set.Ioc (0:ℝ) 1) := measurableSet_Ioc
  apply Measure.integrableOn_of_bounded (M := 32)
  · rw [Real.volume_Ioc]; norm_num
  · exact Gw_measurable.aestronglyMeasurable
  · rw [ae_restrict_iff' hmeas]
    filter_upwards with x hx
    rw [Real.norm_eq_abs]
    exact Gw_bdd_unit hx.1 hx.2

/-- Integrability of `Gw` on `(1,∞)`: dominated by `16·(x e^{−x/2}) + 2·(1/x²)`. -/
lemma Gw_integrableOn_Ioi1 : IntegrableOn Gw (Set.Ioi 1) := by
  have hmeas : MeasurableSet (Set.Ioi (1:ℝ)) := measurableSet_Ioi
  have hg1 : IntegrableOn (fun x : ℝ => 16 * (x * Real.exp (-(1/2) * x))) (Set.Ioi 1) :=
    (id_mul_exp_neg_integrableOn_Ioi1 (by norm_num : (0:ℝ) < 1/2)).const_mul 16
  have hg2 : IntegrableOn (fun x : ℝ => 1 / x ^ 2) (Set.Ioi 1) := by
    have hr := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) (by norm_num : (0:ℝ) < 1)
    refine hr.congr_fun (fun x hx => ?_) hmeas
    have hxpos : (0:ℝ) < x := lt_trans zero_lt_one hx
    rw [Real.rpow_neg hxpos.le, one_div,
      show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hg2' := hg2.const_mul (2 : ℝ)
  have hg := hg1.add hg2'
  apply Integrable.mono' hg Gw_measurable.aestronglyMeasurable
  rw [ae_restrict_iff' hmeas]
  filter_upwards with x hx
  rw [Real.norm_eq_abs, Gw, abs_mul]
  have hxpos : (0:ℝ) < x := lt_trans zero_lt_one hx
  rw [abs_of_pos hxpos]
  have hb := boseReg0Deriv_tail_bound hx.le
  -- x·|bRD x| ≤ x·(16 e^{−x/2} + 2/x³) = 16·(x e^{−x/2}) + 2·(1/x²)
  have hxnn : (0:ℝ) ≤ x := hxpos.le
  have hstep : x * |boseReg0Deriv x| ≤ x * (16 * Real.exp (-x / 2) + 2 / x ^ 3) :=
    mul_le_mul_of_nonneg_left hb hxnn
  have hrw : x * (16 * Real.exp (-x / 2) + 2 / x ^ 3)
      = 16 * (x * Real.exp (-(1/2) * x)) + 2 * (1 / x ^ 2) := by
    have hx3 : x ^ 3 ≠ 0 := pow_ne_zero 3 hxpos.ne'
    field_simp
  simp only [Pi.add_apply]
  rw [← hrw]
  exact hstep

/-- **Integrability of `Gw` on `(0,∞)`.** -/
lemma Gw_integrable_Ioi : IntegrableOn Gw (Set.Ioi 0) := by
  have hsplit : Set.Ioc (0:ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 :=
    Set.Ioc_union_Ioi_eq_Ioi zero_le_one
  rw [← hsplit]
  exact Gw_integrableOn_Ioc01.union Gw_integrableOn_Ioi1

/-- `|GwDeriv x| ≤ 3632` on `(0,1]`. -/
lemma GwDeriv_bdd_unit {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) : |GwDeriv x| ≤ 3632 := by
  rw [GwDeriv]
  have hbrd := boseReg0Deriv_bdd_near_zero hx0 hx1
  have hreg := reg3_bdd_near_zero hx0 hx1
  have hxr : |x * (boseKernel3 x - 6 / x ^ 4)| ≤ 3600 := by
    rw [abs_mul, abs_of_pos hx0]
    nlinarith [abs_nonneg (boseKernel3 x - 6 / x ^ 4), hreg, hx0.le, hx1]
  calc |boseReg0Deriv x + x * (boseKernel3 x - 6 / x ^ 4)|
      ≤ |boseReg0Deriv x| + |x * (boseKernel3 x - 6 / x ^ 4)| := abs_add_le _ _
    _ ≤ 32 + 3600 := by linarith
    _ = 3632 := by norm_num

/-- Integrability of `GwDeriv` on `(0,1]`. -/
lemma GwDeriv_integrableOn_Ioc01 : IntegrableOn GwDeriv (Set.Ioc 0 1) := by
  have hmeas : MeasurableSet (Set.Ioc (0:ℝ) 1) := measurableSet_Ioc
  apply Measure.integrableOn_of_bounded (M := 3632)
  · rw [Real.volume_Ioc]; norm_num
  · exact GwDeriv_measurable.aestronglyMeasurable
  · rw [ae_restrict_iff' hmeas]
    filter_upwards with x hx
    rw [Real.norm_eq_abs]
    exact GwDeriv_bdd_unit hx.1 hx.2

/-- Integrability of `x·(boseKernel3 x − 6/x⁴)` on `(1,∞)`. -/
lemma id_mul_reg3_integrableOn_Ioi1 :
    IntegrableOn (fun x : ℝ => x * (boseKernel3 x - 6 / x ^ 4)) (Set.Ioi 1) := by
  have hmeas : MeasurableSet (Set.Ioi (1:ℝ)) := measurableSet_Ioi
  set C : ℝ := 6 / (1 - Real.exp (-1)) ^ 4 with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]
    have hpos : (0:ℝ) < 1 - Real.exp (-1) := by
      have h := Real.exp_lt_one_iff.mpr (show (-1:ℝ) < 0 by norm_num); linarith
    exact div_pos (by norm_num) (pow_pos hpos 4)
  have hg1 : IntegrableOn (fun x : ℝ => C * (x * Real.exp (-(1/2) * x))) (Set.Ioi 1) :=
    (id_mul_exp_neg_integrableOn_Ioi1 (by norm_num : (0:ℝ) < 1/2)).const_mul C
  have hg2 : IntegrableOn (fun x : ℝ => 1 / x ^ 3) (Set.Ioi 1) := by
    have hr := integrableOn_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) (by norm_num : (0:ℝ) < 1)
    refine hr.congr_fun (fun x hx => ?_) hmeas
    have hxpos : (0:ℝ) < x := lt_trans zero_lt_one hx
    rw [Real.rpow_neg hxpos.le, one_div,
      show ((3:ℝ)) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hg2' := hg2.const_mul (3600 : ℝ)
  have hg := hg1.add hg2'
  have hmeasfun : Measurable (fun x : ℝ => x * (boseKernel3 x - 6 / x ^ 4)) := by
    have h3 : Measurable boseKernel3 := by unfold boseKernel3; measurability
    exact measurable_id.mul (h3.sub ((measurable_const).div (measurable_id.pow_const 4)))
  apply Integrable.mono' hg hmeasfun.aestronglyMeasurable
  rw [ae_restrict_iff' hmeas]
  filter_upwards with x hx
  rw [Real.norm_eq_abs, abs_mul]
  have hxpos : (0:ℝ) < x := lt_trans zero_lt_one hx
  rw [abs_of_pos hxpos]
  have hreg := reg3_global_bound hxpos
  -- |reg3 x| ≤ C e^{−x/2} + 3600/x⁴
  have hstep : x * |boseKernel3 x - 6 / x ^ 4|
      ≤ x * (C * Real.exp (-x / 2) + 3600 / x ^ 4) :=
    mul_le_mul_of_nonneg_left (by rw [hCdef]; exact hreg) hxpos.le
  have hrw : x * (C * Real.exp (-x / 2) + 3600 / x ^ 4)
      = C * (x * Real.exp (-(1/2) * x)) + 3600 * (1 / x ^ 3) := by
    have hx4 : x ^ 4 ≠ 0 := pow_ne_zero 4 hxpos.ne'
    field_simp
  simp only [Pi.add_apply]
  rw [← hrw]
  exact hstep

/-- Integrability of `GwDeriv` on `(1,∞)`. -/
lemma GwDeriv_integrableOn_Ioi1 : IntegrableOn GwDeriv (Set.Ioi 1) := by
  have h := boseReg0Deriv_integrableOn_Ioi1.add id_mul_reg3_integrableOn_Ioi1
  simpa only [GwDeriv] using h

/-- **Integrability of `GwDeriv` on `(0,∞)`.** -/
lemma GwDeriv_integrable_Ioi : IntegrableOn GwDeriv (Set.Ioi 0) := by
  have hsplit : Set.Ioc (0:ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 :=
    Set.Ioc_union_Ioi_eq_Ioi zero_le_one
  rw [← hsplit]
  exact GwDeriv_integrableOn_Ioc01.union GwDeriv_integrableOn_Ioi1

/-- The derivative `boseReg0′` itself: `boseReg0′′(x) = boseKernel3 x − 6/x⁴`. -/
lemma boseReg0Deriv_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt boseReg0Deriv (boseKernel3 x - 6 / x ^ 4) x := by
  -- `boseReg0Deriv y = 2/y³ − boseKernel2 y` near `x`; differentiate that.
  have hcube : HasDerivAt (fun y : ℝ => 2 / y ^ 3) (-6 / x ^ 4) x := by
    have h1 : HasDerivAt (fun y : ℝ => y ^ 3) ((3:ℕ) * x ^ (3 - 1)) x := hasDerivAt_pow 3 x
    have h2 := h1.inv (pow_ne_zero 3 hx.ne')
    have h3 := h2.const_mul (2:ℝ)
    have heq : (2:ℝ) * (-((3:ℕ) * x ^ (3 - 1)) / (x ^ 3) ^ 2) = -6 / x ^ 4 := by
      push_cast; field_simp; ring
    rw [heq] at h3
    convert h3 using 2 with y
  have hk2 : HasDerivAt boseKernel2 (-boseKernel3 x) x := boseKernel2_hasDerivAt hx
  have hsub := hcube.sub hk2
  have hval : (-6 / x ^ 4 - (-boseKernel3 x)) = boseKernel3 x - 6 / x ^ 4 := by ring
  rw [hval] at hsub
  have hev : boseReg0Deriv =ᶠ[𝓝 x] (fun y => 2 / y ^ 3 - boseKernel2 y) := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioi hx] with y hy
    have hk := boseKernel2_eq_inv_cube_sub_deriv hy
    linarith [hk]
  exact hsub.congr_of_eventuallyEq hev

/-- `Gw` has derivative `GwDeriv` on `(0,∞)`. -/
lemma Gw_hasDerivAt {x : ℝ} (hx : 0 < x) : HasDerivAt Gw (GwDeriv x) x := by
  have hbase := (hasDerivAt_id x).mul (boseReg0Deriv_hasDerivAt hx)
  simp only [id_eq, one_mul] at hbase
  have hval : boseReg0Deriv x + x * (boseKernel3 x - 6 / x ^ 4) = GwDeriv x := by rw [GwDeriv]
  rw [hval] at hbase
  exact hbase

/-- The improper-FTC auxiliary `H(x) = x·boseReg0(x)` tends to `0` at `∞`. -/
lemma id_mul_boseReg0_tendsto_atTop :
    Tendsto (fun x : ℝ => x * boseReg0 x) atTop (𝓝 0) := by
  have hbound : ∀ᶠ x : ℝ in atTop,
      ‖x * boseReg0 x‖ ≤ 4 * (x * Real.exp (-x)) + 1 / x := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    have hxpos : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hxpos]
    have hb := boseReg0_tail_bound hx
    have hstep : x * |boseReg0 x| ≤ x * (4 * Real.exp (-x) + 1 / x ^ 2) :=
      mul_le_mul_of_nonneg_left hb hxpos.le
    have hrw : x * (4 * Real.exp (-x) + 1 / x ^ 2) = 4 * (x * Real.exp (-x)) + 1 / x := by
      have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hxpos.ne'
      field_simp
    rw [hrw] at hstep
    exact hstep
  have hlim : Tendsto (fun x : ℝ => 4 * (x * Real.exp (-x)) + 1 / x) atTop (𝓝 0) := by
    have ht1 : Tendsto (fun x : ℝ => 4 * (x * Real.exp (-x))) atTop (𝓝 0) := by
      have hk := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
      have hk' : Tendsto (fun x : ℝ => x * Real.exp (-x)) atTop (𝓝 0) := by
        refine hk.congr (fun x => ?_); rw [pow_one]
      have := hk'.const_mul (4:ℝ)
      simpa using this
    have ht2 : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
      simpa [one_div] using (tendsto_inv_atTop_zero (𝕜 := ℝ))
    simpa using ht1.add ht2
  exact squeeze_zero_norm' hbound hlim

/-- **`∫_{(0,∞)} Gw = 1/2`.** -/
theorem integral_Gw_Ioi : ∫ x in Set.Ioi (0:ℝ), Gw x = 1 / 2 := by
  -- `H = (·)·boseReg0` has derivative `boseReg0 + Gw`, `H(0) = 0`, `H → 0`.
  have hcontW : ContinuousWithinAt (fun x : ℝ => x * boseReg0 x) (Set.Ici 0) 0 := by
    have hbound : ∀ᶠ x : ℝ in 𝓝[Set.Ici 0] (0:ℝ),
        ‖x * boseReg0 x‖ ≤ 4 * |x| := by
      have hmem : Set.Iic (1:ℝ) ∈ 𝓝[Set.Ici 0] (0:ℝ) :=
        nhdsWithin_le_nhds (Iic_mem_nhds (by norm_num))
      filter_upwards [hmem, self_mem_nhdsWithin] with x hx1 hx0
      have hx0' : (0:ℝ) ≤ x := hx0
      have hx1' : x ≤ 1 := hx1
      rw [Real.norm_eq_abs, abs_mul]
      rcases eq_or_lt_of_le hx0' with hx | hx
      · simp [← hx]
      · have hb := boseReg0_bdd_near_zero hx hx1'
        have hxabs : |x| ≤ 1 := by rw [abs_of_pos hx]; exact hx1'
        nlinarith [abs_nonneg x, abs_nonneg (boseReg0 x), hb, hxabs]
    have hlim : Tendsto (fun x : ℝ => 4 * |x|) (𝓝[Set.Ici 0] (0:ℝ)) (𝓝 0) := by
      have habs : Tendsto (fun x : ℝ => |x|) (𝓝[Set.Ici 0] (0:ℝ)) (𝓝 0) := by
        have := (continuous_abs.tendsto (0:ℝ)).mono_left
          (nhdsWithin_le_nhds (s := Set.Ici (0:ℝ)))
        simpa using this
      simpa using habs.const_mul (4:ℝ)
    have key : Tendsto (fun x : ℝ => x * boseReg0 x) (𝓝[Set.Ici 0] (0:ℝ)) (𝓝 0) :=
      squeeze_zero_norm' hbound hlim
    have hH0 : (fun x : ℝ => x * boseReg0 x) (0:ℝ) = 0 := by simp
    show Tendsto (fun x : ℝ => x * boseReg0 x) (𝓝[Set.Ici 0] (0:ℝ))
      (𝓝 ((fun x : ℝ => x * boseReg0 x) (0:ℝ)))
    rw [hH0]; exact key
  have hderivW : ∀ x ∈ Set.Ioi (0:ℝ), HasDerivAt (fun x : ℝ => x * boseReg0 x)
      (boseReg0 x + Gw x) x := by
    intro x hx
    have hx' : 0 < x := hx
    have hb := (hasDerivAt_id x).mul (boseReg0_hasDerivAt hx')
    simp only [id_eq, one_mul] at hb
    have hval : boseReg0 x + x * boseReg0Deriv x = boseReg0 x + Gw x := by rw [Gw]
    rw [hval] at hb
    exact hb
  have hint : IntegrableOn (fun x : ℝ => boseReg0 x + Gw x) (Set.Ioi 0) :=
    boseReg0_integrable_Ioi.add Gw_integrable_Ioi
  have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    hcontW hderivW hint id_mul_boseReg0_tendsto_atTop
  -- `∫(boseReg0 + Gw) = 0 − H 0 = 0`
  have hzero : ∫ x in Set.Ioi (0:ℝ), (boseReg0 x + Gw x) = 0 := by rw [hftc]; simp
  -- split the integral
  have hsplit : ∫ x in Set.Ioi (0:ℝ), (boseReg0 x + Gw x)
      = (∫ x in Set.Ioi (0:ℝ), boseReg0 x) + ∫ x in Set.Ioi (0:ℝ), Gw x :=
    MeasureTheory.integral_add boseReg0_integrable_Ioi Gw_integrable_Ioi
  rw [hsplit, integral_boseReg0_Ioi] at hzero
  linarith [hzero]

/-- The Riemann-sum estimate for `G`: `|Σ_{k≥1} G(tk) − 1/(2t)| ≤ K` with
`K = ∫_{(0,∞)}|GwDeriv| + 32`, for `0 < t < 1`. -/
theorem riemann_Gw_bound :
    ∀ t : ℝ, 0 < t → t < 1 →
      |(∑' k : ℕ, if k = 0 then 0 else Gw (t * (k : ℝ)))
        - (1 / t) * (1 / 2)| ≤ (∫ x in Set.Ioi (0:ℝ), |GwDeriv x|) + 32 := by
  have hbase := riemann_sum_Ioi_sub_integral_bound
    (f := Gw) (f' := GwDeriv) (M := 32) (η := 1)
    (by norm_num) (by norm_num)
    (fun x hx => Gw_hasDerivAt hx)
    GwDeriv_integrable_Ioi Gw_integrable_Ioi
    (fun x hx0 hx1 => Gw_bdd_unit hx0 hx1)
  intro t ht ht1
  have h := hbase t ht ht1
  rwa [integral_Gw_Ioi] at h

/-- **Moment-one two-term asymptotic.**
`|M₁(t) − (2(π²/6)/t³ − 1/(2t²))| ≤ K/t` for `0 < t < 1`. -/
theorem sigmaMoment_one_two_term :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 < t → t < 1 →
      |sigmaMoment 1 t - (2 * (Real.pi ^ 2 / 6) / t ^ 3 - 1 / (2 * t ^ 2))| ≤ K / t := by
  classical
  refine ⟨(∫ x in Set.Ioi (0:ℝ), |GwDeriv x|) + 32, by positivity, ?_⟩
  intro t ht ht1
  -- the weak decomposition: `M₁ = 2(π²/6)/t³ − Σ hrem`, `hrem = guarded k·boseReg0′(tk)`
  set hrem : ℕ → ℝ := fun k => if k = 0 then (0:ℝ)
    else (k : ℝ) * boseReg0Deriv (t * (k : ℝ)) with hremdef
  set hmain : ℕ → ℝ := fun k => if k = 0 then (0:ℝ)
    else (2 / t ^ 3) * (1 / ((k : ℝ)) ^ 2) with hmaindef
  have hML := sigmaMoment_one_lambert ht
  have hrem_summ : Summable hrem := by
    apply Summable.of_norm
    have habs := summable_weighted_absDeriv ht
    refine habs.congr fun k => ?_
    simp only [hremdef]
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, if_neg hk, Real.norm_eq_abs, abs_mul, Nat.abs_cast]
  have hmain_summ : Summable hmain := by
    have hb : Summable (fun k : ℕ => if k = 0 then (0:ℝ) else 1 / ((k : ℝ)) ^ 2) := by
      have h0 : Summable (fun n : ℕ => 1 / ((n : ℝ)) ^ 2) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
      apply Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) h0
      · by_cases hk : k = 0
        · simp [hk]
        · rw [if_neg hk]; positivity
      · by_cases hk : k = 0
        · simp [hk]
        · rw [if_neg hk]
    have := hb.mul_left (2 / t ^ 3)
    refine this.congr fun k => ?_
    simp only [hmaindef]
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, if_neg hk]
  have hterm : ∀ k : ℕ,
      (if k = 0 then (0:ℝ) else (k : ℝ) * boseKernel2 (t * (k : ℝ)))
        = hmain k - hrem k := by
    intro k
    simp only [hmaindef, hremdef]
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, if_neg hk, if_neg hk]
      have hkpos : (0:ℝ) < (k : ℝ) := by
        have : 0 < k := Nat.pos_of_ne_zero hk; exact_mod_cast this
      have htkpos : 0 < t * (k : ℝ) := by positivity
      rw [boseKernel2_eq_inv_cube_sub_deriv htkpos]
      have htne : t ≠ 0 := ht.ne'
      have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
      field_simp
  have hM1_eq : sigmaMoment 1 t = (∑' k, hmain k) - (∑' k, hrem k) := by
    rw [hML, tsum_congr hterm, hmain_summ.tsum_sub hrem_summ]
  have hmain_eq : (∑' k, hmain k) = 2 * (Real.pi ^ 2 / 6) / t ^ 3 := by
    have : (∑' k, hmain k)
        = (2 / t ^ 3) * ∑' k : ℕ, (if k = 0 then (0:ℝ) else 1 / ((k : ℝ)) ^ 2) := by
      rw [← tsum_mul_left]
      apply tsum_congr; intro k
      simp only [hmaindef]
      by_cases hk : k = 0
      · simp [hk]
      · rw [if_neg hk, if_neg hk]
    rw [this, tsum_if_inv_sq]; ring
  -- connect `Σ hrem` to the Riemann sum of `Gw`: `Σ (guarded Gw(tk)) = t · Σ hrem`
  have hGwsum_eq : (∑' k : ℕ, if k = 0 then (0:ℝ) else Gw (t * (k : ℝ)))
      = t * ∑' k, hrem k := by
    rw [← tsum_mul_left]
    apply tsum_congr; intro k
    simp only [hremdef]
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, if_neg hk, Gw]
      ring
  -- the Riemann bound, transported
  have hRie := riemann_Gw_bound t ht ht1
  rw [hGwsum_eq] at hRie
  -- `|t·Σhrem − 1/(2t)| ≤ K`, and `t·Σhrem − 1/(2t) = t·(Σhrem − 1/(2t²))`
  set K : ℝ := (∫ x in Set.Ioi (0:ℝ), |GwDeriv x|) + 32 with hKdef
  have hfactor : t * (∑' k, hrem k) - (1 / t) * (1 / 2)
      = t * ((∑' k, hrem k) - 1 / (2 * t ^ 2)) := by
    have htne : t ≠ 0 := ht.ne'
    field_simp
  rw [hfactor, abs_mul, abs_of_pos ht] at hRie
  have hrem_bound : |(∑' k, hrem k) - 1 / (2 * t ^ 2)| ≤ K / t := by
    rw [le_div_iff₀ ht, mul_comm]
    exact hRie
  -- assemble
  rw [hM1_eq, hmain_eq]
  have harr : (2 * (Real.pi ^ 2 / 6) / t ^ 3 - ∑' k, hrem k)
      - (2 * (Real.pi ^ 2 / 6) / t ^ 3 - 1 / (2 * t ^ 2))
      = -((∑' k, hrem k) - 1 / (2 * t ^ 2)) := by ring
  rw [harr, abs_neg]
  exact hrem_bound

end AnalyticCombinatorics.Ch8.Partitions.Erdos
