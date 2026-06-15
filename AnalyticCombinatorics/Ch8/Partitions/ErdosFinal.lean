import AnalyticCombinatorics.Ch8.Partitions.GaussianTailAsymp
import AnalyticCombinatorics.Ch8.Partitions.ErdosAbelian

/-!
# HR constant final assembly (brick 4 ratio → log → discharge → `a = 1/(4√3)`)

`modelSaddle s ~ (4√π/C)·√s·e^{A/s}` (= `mainScale`), assembled from the riemann
comparison + main term (`gaussianTail_asymp`) + the o()-error `hO`; gives
`modelSaddle_log_asymp` and `modelSaddle_tendsto_atTop`, which discharge bricks 3,4,5
into `a = 1/(4√3)`.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators MeasureTheory Real
open AnalyticCombinatorics.Ch8.Partitions.Erdos
open scoped Topology Interval

noncomputable section

/-- The saddle main scale `(4√π/C)·√s·e^{A/s}`. -/
noncomputable def mainScale (s : ℝ) : ℝ :=
  (4 * Real.sqrt Real.pi / C) * Real.sqrt s * Real.exp (Partitions.A / s)

lemma mainScale_pos {s : ℝ} (hs : 0 < s) : 0 < mainScale s := by
  have hCpos : 0 < C := C_pos
  unfold mainScale; positivity

/-- `mainScale → ∞` as `s → 0⁺` (lower-bounded by `const·s^{-1/2}`). -/
lemma mainScale_tendsto_atTop : Tendsto mainScale (𝓝[>] (0 : ℝ)) atTop := by
  have hCpos : 0 < C := C_pos
  have hApos : 0 < Partitions.A := Partitions.A_pos
  -- bound: mainScale s ≥ (4√π·A/C)·s⁻¹^{1/2} = (4√π·A/C)/√s
  have hlow : Tendsto (fun s : ℝ => (4 * Real.sqrt Real.pi * Partitions.A / C) * (Real.sqrt s)⁻¹)
      (𝓝[>] (0 : ℝ)) atTop := by
    have hinv : Tendsto (fun s : ℝ => (Real.sqrt s)⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
      tendsto_inv_nhdsGT_zero.comp sqrt_tendsto_nhdsGT_zero
    exact Tendsto.const_mul_atTop (by positivity) hinv
  refine tendsto_atTop_mono' _ ?_ hlow
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hspos : 0 < s := hs
  have hsqrtpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
  have hexp : Partitions.A / s ≤ Real.exp (Partitions.A / s) := by
    have := Real.add_one_le_exp (Partitions.A / s); linarith
  have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hspos.le
  have hid : (4 * Real.sqrt Real.pi * Partitions.A / C) * (Real.sqrt s)⁻¹
      = (4 * Real.sqrt Real.pi / C) * Real.sqrt s * (Partitions.A / s) := by
    field_simp
    linear_combination -hss
  rw [mainScale, hid]
  exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-- `T1`: `(∫_{Ioi 0} sd(·+1)) / mainScale → 1`. -/
lemma shiftIntegral_div_mainScale_tendsto_one :
    Tendsto (fun s : ℝ => (∫ x in Set.Ioi (0 : ℝ), saddleDensity s (x + 1)) / mainScale s)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  refine gaussianTail_asymp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hspos : 0 < s := hs
  have hCpos : 0 < C := C_pos
  have hsqrtpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
  have hsqrtpi : (0 : ℝ) < Real.sqrt Real.pi := by positivity
  have hexpne : Real.exp (Partitions.A / s) ≠ 0 := Real.exp_ne_zero _
  have hfold : (∫ v in Set.Ioi (1 : ℝ), Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
      = gaussianTailFull s := rfl
  rw [saddleDensity_shift_integral_eq_Ioi1 hs, modelSaddleIoi_substitution hs,
    vIntegral_eq_gaussianForm hs, hfold]
  unfold mainScale
  field_simp
  ring

/-- The o()-error hypothesis: the mesh-1 Riemann error is negligible vs `mainScale`. -/
def RiemannErrorNegligible : Prop :=
  Tendsto
    (fun s : ℝ =>
      ((∫ x in Set.Ioi (0 : ℝ),
          |saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹)|)
        + Real.exp (C * Real.sqrt 3)) / mainScale s)
    (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- `T2`: `saddleDensity s 1 / mainScale → 0`. -/
lemma sd1_div_mainScale_tendsto_zero :
    Tendsto (fun s : ℝ => saddleDensity s 1 / mainScale s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hconst : Tendsto (fun s : ℝ => Real.exp C / mainScale s) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (tendsto_const_nhds (x := Real.exp C)).div_atTop mainScale_tendsto_atTop
  refine squeeze_zero' ?_ ?_ hconst
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have := mainScale_pos hs; rw [saddleDensity]; positivity
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos : 0 < s := hs
    have hMSpos : 0 < mainScale s := mainScale_pos hspos
    have hsd1 : saddleDensity s 1 ≤ Real.exp C := by
      rw [saddleDensity, Real.sqrt_one, show C * 1 - s * 1 = C - s by ring, div_one]
      exact Real.exp_le_exp.mpr (by linarith)
    gcongr

/-- **Brick 4 ratio**: `modelSaddle s / mainScale s → 1` (given `hO`). -/
theorem modelSaddle_ratio_asymp (hO : RiemannErrorNegligible) :
    Tendsto (fun s : ℝ => modelSaddle s / mainScale s) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hT1 := shiftIntegral_div_mainScale_tendsto_one
  have hT2 := sd1_div_mainScale_tendsto_zero
  have hCpos : 0 < C := C_pos
  have hO2 : Tendsto
      (fun s : ℝ =>
        ((∫ x in Set.Ioi (0 : ℝ),
            |saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹)|)
          + Real.exp (C * Real.sqrt 3)) / mainScale s) (𝓝[>] (0 : ℝ)) (𝓝 0) := hO
  have hg : Tendsto
      (fun s : ℝ =>
        ((∫ x in Set.Ioi (0 : ℝ),
            |saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹)|)
          + Real.exp (C * Real.sqrt 3)) / mainScale s + saddleDensity s 1 / mainScale s)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by simpa using hO2.add hT2
  have hrest : Tendsto
      (fun s : ℝ =>
        (modelSaddle s - ∫ x in Set.Ioi (0 : ℝ), saddleDensity s (x + 1)) / mainScale s)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos : 0 < s := hs
    have hMSpos : 0 < mainScale s := mainScale_pos hspos
    have hsd1 : 0 ≤ saddleDensity s 1 := by rw [saddleDensity]; positivity
    have hb := modelSaddle_sub_integral_bound hspos
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hMSpos, ← add_div]
    gcongr
    calc |modelSaddle s - ∫ x in Set.Ioi (0 : ℝ), saddleDensity s (x + 1)|
        = |(modelSaddle s - saddleDensity s 1 - ∫ x in Set.Ioi (0 : ℝ), saddleDensity s (x + 1))
            + saddleDensity s 1| := by ring_nf
      _ ≤ |modelSaddle s - saddleDensity s 1 - ∫ x in Set.Ioi (0 : ℝ), saddleDensity s (x + 1)|
          + |saddleDensity s 1| := abs_add_le _ _
      _ ≤ ((∫ x in Set.Ioi (0 : ℝ),
              |saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - (x + 1)⁻¹)|)
            + Real.exp (C * Real.sqrt 3)) + saddleDensity s 1 := by
          rw [abs_of_nonneg hsd1]; linarith [hb]
  have hcomb := hrest.add hT1
  rw [zero_add] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hMSpos : 0 < mainScale s := mainScale_pos hs
  rw [← add_div]
  congr 1
  ring

/-- **Brick 4 (atTop)**: `modelSaddle → ∞` as `s → 0⁺`. -/
theorem modelSaddle_tendsto_atTop (hO : RiemannErrorNegligible) :
    Tendsto modelSaddle (𝓝[>] (0 : ℝ)) atTop := by
  have hratio := modelSaddle_ratio_asymp hO
  have hms := mainScale_tendsto_atTop
  have hhalf : ∀ᶠ s in 𝓝[>] (0 : ℝ), (1 / 2 : ℝ) ≤ modelSaddle s / mainScale s :=
    hratio.eventually (eventually_ge_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  refine tendsto_atTop_mono' _ ?_
    (Tendsto.const_mul_atTop (show (0 : ℝ) < 1 / 2 by norm_num) hms)
  filter_upwards [hhalf, self_mem_nhdsWithin] with s hs hspos
  have hMSpos : 0 < mainScale s := mainScale_pos hspos
  have hmeq : modelSaddle s / mainScale s * mainScale s = modelSaddle s := by
    field_simp
  calc (1 / 2 : ℝ) * mainScale s
      ≤ modelSaddle s / mainScale s * mainScale s :=
        mul_le_mul_of_nonneg_right hs hMSpos.le
    _ = modelSaddle s := hmeq

/-- **Brick 4 (log form)**: the `hB4` hypothesis of `erdos_limit_constant_of_asymptotics`. -/
theorem modelSaddle_log_asymp (hO : RiemannErrorNegligible) :
    Tendsto
      (fun t : ℝ =>
        Real.log (modelSaddle t) - Partitions.A / t - (1 / 2 : ℝ) * Real.log t
          - Real.log (4 * Real.sqrt Real.pi / C))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hCpos : 0 < C := C_pos
  have hratio := modelSaddle_ratio_asymp hO
  -- log of the ratio → log 1 = 0
  have hlog : Tendsto (fun s : ℝ => Real.log (modelSaddle s / mainScale s))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
    simpa [Real.log_one] using this
  refine hlog.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hspos : 0 < s := hs
  have hMSpos : 0 < modelSaddle s := modelSaddle_pos hspos
  have hmainpos : 0 < mainScale s := mainScale_pos hspos
  have hsqrtspos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
  have hKpos : 0 < 4 * Real.sqrt Real.pi / C := div_pos (by positivity) hCpos
  rw [Real.log_div (ne_of_gt hMSpos) (ne_of_gt hmainpos)]
  unfold mainScale
  rw [Real.log_mul (by positivity) (ne_of_gt (Real.exp_pos _)),
    Real.log_mul (ne_of_gt hKpos) (ne_of_gt hsqrtspos),
    Real.log_sqrt hspos.le, Real.log_exp]
  ring

/-- **The Erdős–Hardy–Ramanujan limit constant** is `1/(4√3)`, given the renewal/Tauberian
input `hlim : u n → a` and the negligibility of the mesh-1 Riemann error `hO`. -/
theorem erdos_limit_constant {a : ℝ} (ha : 0 < a)
    (hlim : Tendsto Erdos.u atTop (𝓝 a))
    (hO : RiemannErrorNegligible) :
    a = 1 / (4 * Real.sqrt 3) := by
  have hMS_atTop : Tendsto modelSaddle (𝓝[>] (0 : ℝ)) atTop := modelSaddle_tendsto_atTop hO
  have hB3 := partLaplace_log_sub_modelSaddle_tendsto ha hlim hMS_atTop
  have hB4 := modelSaddle_log_asymp hO
  exact erdos_limit_constant_of_asymptotics ha hB3 hB4

end

end AnalyticCombinatorics.Ch8.Partitions
