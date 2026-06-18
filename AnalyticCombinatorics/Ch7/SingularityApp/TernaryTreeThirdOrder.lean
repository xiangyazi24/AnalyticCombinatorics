import AnalyticCombinatorics.Ch4.Analytic.SqrtSingularityThirdOrder
import AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeSecondOrder

/-!
# Third-order ternary-tree asymptotics

This file records the ternary-tree square-root data at `ρ = 4 / 27` and plugs
it into the committed third-order square-root applicator.  The unconditional
Gamma-ratio check at the end gives the same relative coefficient.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics
open scoped Topology BigOperators PowerSeries

noncomputable section

def ternaryRho : ℝ :=
  4 / 27

def ternaryTreeSeriesℂ : PowerSeries ℂ :=
  PowerSeries.mk fun n => (ternaryTreeCount n : ℂ)

@[simp] lemma coeff_ternaryTreeSeriesℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n ternaryTreeSeriesℂ =
      (ternaryTreeCount n : ℂ) := by
  simp [ternaryTreeSeriesℂ]

def ternaryRegularValueℂ : ℂ :=
  (3 / 2 : ℂ)

def ternaryAnalyticLinearCoeffℂ : ℂ :=
  -(2 / 3 : ℂ)

def ternarySingularCoeff : ℂ :=
  -(((Real.sqrt 3 / 2 : ℝ) : ℂ))

def ternarySingularDerivAtRho : ℂ :=
  (((35 * Real.sqrt 3 / 16 : ℝ) : ℂ))

def ternarySingularSecondDerivAtRho : ℂ :=
  -(((3003 * Real.sqrt 3 / 128 : ℝ) : ℂ))

def ternaryThirdSingularCoeff : ℂ :=
  ((((ternaryRho : ℝ) : ℂ) ^ 2 * ternarySingularSecondDerivAtRho) / 2)

def ternaryRelativeThirdConstant : ℝ :=
  3145 / 10368

def ternaryThirdAsymptoticConstant : ℝ :=
  ternaryAsymptoticConstant * ternaryRelativeThirdConstant

lemma ternarySingularCoeff_ne_zero : ternarySingularCoeff ≠ 0 := by
  unfold ternarySingularCoeff
  norm_num

lemma ternarySecondSingularCoeff_eq_meta :
    -(((ternaryRho : ℝ) : ℂ) * ternarySingularDerivAtRho) =
      -(((35 * Real.sqrt 3 / 108 : ℝ) : ℂ)) := by
  unfold ternaryRho ternarySingularDerivAtRho
  norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg]
  ring

lemma ternaryThirdSingularCoeff_eq :
    ternaryThirdSingularCoeff =
      -(((1001 * Real.sqrt 3 / 3888 : ℝ) : ℂ)) := by
  unfold ternaryThirdSingularCoeff ternaryRho ternarySingularSecondDerivAtRho
  norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg]
  ring

lemma ternaryFirstAsymptoticConstant_eq_meta :
    sqrtSingularityC0 ternarySingularCoeff =
      ((ternaryAsymptoticConstant : ℝ) : ℂ) := by
  unfold sqrtSingularityC0 ternarySingularCoeff ternaryAsymptoticConstant
  norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg]
  ring

lemma ternarySecondAsymptoticConstant_eq_meta :
    sqrtSingularityC1 ternaryRho ternarySingularCoeff ternarySingularDerivAtRho =
      ((ternarySecondAsymptoticConstant : ℝ) : ℂ) := by
  unfold sqrtSingularityC1 sqrtSingularityC1Rescaled ternaryRho ternarySingularCoeff
    ternarySingularDerivAtRho ternarySecondAsymptoticConstant
    ternaryAsymptoticConstant ternaryRelativeSecondConstant
  norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg]
  ring

lemma ternaryThirdAsymptoticConstant_eq_meta :
    sqrtSingularityC2 ternaryRho ternarySingularCoeff
        ternarySingularDerivAtRho ternarySingularSecondDerivAtRho =
      ((ternaryThirdAsymptoticConstant : ℝ) : ℂ) := by
  unfold sqrtSingularityC2 sqrtSingularityC2Rescaled ternaryRho ternarySingularCoeff
    ternarySingularDerivAtRho ternarySingularSecondDerivAtRho
    ternaryThirdAsymptoticConstant ternaryAsymptoticConstant
    ternaryRelativeThirdConstant
  norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg]
  ring

lemma ternaryRelativeThirdConstant_eq_meta :
    sqrtSingularityRelativeC2 ternarySingularCoeff
        (((ternaryRho : ℝ) : ℂ) * ternarySingularDerivAtRho)
        ((((ternaryRho : ℝ) : ℂ) ^ 2) * ternarySingularSecondDerivAtRho) =
      (ternaryRelativeThirdConstant : ℂ) := by
  unfold sqrtSingularityRelativeC2 ternaryRho ternarySingularCoeff
    ternarySingularDerivAtRho ternarySingularSecondDerivAtRho
    ternaryRelativeThirdConstant
  norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg]
  have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3))
  field_simp [hs3]
  norm_num

theorem ternaryTreeSeries_complex_thirdOrder_meta
    {R φ : ℝ} {F : ℂ → ℂ}
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt
      (fun z : ℂ => F (((ternaryRho : ℝ) : ℂ) * z))
      (PowerSeries.toFMLS
        (PowerSeries.rescale (((ternaryRho : ℝ) : ℂ)) ternaryTreeSeriesℂ))
      (0 : ℂ))
    (hΔ : AnalyticOnNhd ℂ
      (fun z : ℂ => F (((ternaryRho : ℝ) : ℂ) * z))
      (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ =>
        ‖sqrtAdjustedFun
              (fun w : ℂ => F (((ternaryRho : ℝ) : ℂ) * w))
              ternaryRegularValueℂ ternaryAnalyticLinearCoeffℂ z -
            ternarySingularCoeff * (1 - z) ^ (1 / 2 : ℂ) -
            (-(((ternaryRho : ℝ) : ℂ) * ternarySingularDerivAtRho)) *
              (1 - z) ^ (3 / 2 : ℂ) -
            ((((ternaryRho : ℝ) : ℂ) ^ 2 *
                ternarySingularSecondDerivAtRho) / 2) *
              (1 - z) ^ (5 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(5 / 2 : ℝ)))
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ =>
      (ternaryTreeCount n : ℂ) -
        (((((ternaryRho : ℝ) : ℂ)⁻¹) ^ n) *
          (sqrtSingularityC0 ternarySingularCoeff *
              (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
            sqrtSingularityC1 ternaryRho ternarySingularCoeff
                ternarySingularDerivAtRho *
              (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) +
            sqrtSingularityC2 ternaryRho ternarySingularCoeff
                ternarySingularDerivAtRho ternarySingularSecondDerivAtRho *
              (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))))
      =o[atTop]
        (fun n : ℕ =>
          ‖(((((ternaryRho : ℝ) : ℂ)⁻¹) ^ n) *
            (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))‖) := by
  have hρ : 0 < ternaryRho := by
    unfold ternaryRho
    norm_num
  have hmeta := sqrt_singularity_thirdOrder_original_of_rescaled_singularity
    (ρ := ternaryRho) (R := R) (φ := φ)
    (F := F) (P := ternaryTreeSeriesℂ)
    (A0 := ternaryRegularValueℂ) (A1 := ternaryAnalyticLinearCoeffℂ)
    (Bρ := ternarySingularCoeff)
    (Bderivρ := ternarySingularDerivAtRho)
    (Bsecondρ := ternarySingularSecondDerivAtRho)
    hρ ternarySingularCoeff_ne_zero hR hφ0 hφ2 hp hΔ hsing
  simpa using hmeta

def gammaRatioThirdCoeff (α : ℝ) : ℝ :=
  α * (α - 1) * (α - 2) * (3 * α - 1) / 24

def gammaRatioThirdNormalizedError (α : ℝ) (n : ℕ) : ℝ :=
  ternaryGammaRatio α n / ((n : ℝ) ^ (α - 1)) -
    (1 + gammaRatioSecondCoeff α * (n : ℝ)⁻¹ +
      gammaRatioThirdCoeff α * ((n : ℝ)⁻¹) ^ 2)

def gammaRatioThirdNormalizedFactor (α : ℝ) (n : ℕ) : ℝ :=
  1 + gammaRatioSecondCoeff α * (n : ℝ)⁻¹ +
    gammaRatioThirdCoeff α * ((n : ℝ)⁻¹) ^ 2 +
      gammaRatioThirdNormalizedError α n

def ternaryGammaThirdNormalizedProduct (n : ℕ) : ℝ :=
  gammaRatioThirdNormalizedFactor (1 / 3 : ℝ) n *
    gammaRatioThirdNormalizedFactor (2 / 3 : ℝ) n /
    gammaRatioThirdNormalizedFactor (3 / 2 : ℝ) n

lemma gammaRatioThirdNormalizedFactor_eq (α : ℝ) (n : ℕ) :
    gammaRatioThirdNormalizedFactor α n =
      ternaryGammaRatio α n / ((n : ℝ) ^ (α - 1)) := by
  unfold gammaRatioThirdNormalizedFactor gammaRatioThirdNormalizedError
  ring

lemma ternaryGammaThirdNormalizedProduct_eq_second (n : ℕ) :
    ternaryGammaThirdNormalizedProduct n = ternaryGammaNormalizedProduct n := by
  unfold ternaryGammaThirdNormalizedProduct ternaryGammaNormalizedProduct
  rw [gammaRatioThirdNormalizedFactor_eq, gammaRatioThirdNormalizedFactor_eq,
    gammaRatioThirdNormalizedFactor_eq, gammaRatioNormalizedFactor_eq,
    gammaRatioNormalizedFactor_eq, gammaRatioNormalizedFactor_eq]

lemma ternary_gamma_ratio_third_correction :
    gammaRatioThirdCoeff (1 / 3 : ℝ) +
      gammaRatioThirdCoeff (2 / 3 : ℝ) -
      gammaRatioThirdCoeff (3 / 2 : ℝ) +
      gammaRatioSecondCoeff (1 / 3 : ℝ) *
        gammaRatioSecondCoeff (2 / 3 : ℝ) +
      gammaRatioSecondCoeff (3 / 2 : ℝ) *
        gammaRatioSecondCoeff (3 / 2 : ℝ) -
      gammaRatioSecondCoeff (3 / 2 : ℝ) *
        gammaRatioSecondCoeff (1 / 3 : ℝ) -
      gammaRatioSecondCoeff (3 / 2 : ℝ) *
        gammaRatioSecondCoeff (2 / 3 : ℝ) =
    ternaryRelativeThirdConstant := by
  norm_num [gammaRatioSecondCoeff, gammaRatioThirdCoeff, ternaryRelativeThirdConstant]

lemma ternaryThirdAsymptoticConstant_closed :
    ternaryThirdAsymptoticConstant =
      3145 * Real.sqrt 3 / (41472 * Real.sqrt Real.pi) := by
  unfold ternaryThirdAsymptoticConstant ternaryAsymptoticConstant
    ternaryRelativeThirdConstant
  ring

lemma gammaRatioThirdNormalizedError_isBigO {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => gammaRatioThirdNormalizedError α n)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(3 : ℝ))) := by
  have hO := gamma_ratio_third_order (α := α) hα
  have hp : (fun n : ℕ => (n : ℝ) ^ (1 - α))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 - α)) := isBigO_refl _ _
  have hmul :
      (fun n : ℕ =>
        (ternaryGammaRatio α n -
          (n : ℝ) ^ (α - 1) *
            (1 + (α * (α - 1) / 2) * (n : ℝ)⁻¹ +
              (α * (α - 1) * (α - 2) * (3 * α - 1) / 24) *
                ((n : ℝ)⁻¹) ^ 2)) *
          (n : ℝ) ^ (1 - α))
        =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(3 : ℝ))) := by
    simpa [ternaryGammaRatio] using
      IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
        (a := α - 4) (b := 1 - α) (c := -(3 : ℝ)) hO hp (by norm_num)
  refine hmul.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  have hnne : (n : ℝ) ≠ 0 := hnpos.ne'
  have hpow_ne : (n : ℝ) ^ (α - 1) ≠ 0 :=
    (Real.rpow_pos_of_pos hnpos _).ne'
  have hpow_inv : (n : ℝ) ^ (1 - α) = ((n : ℝ) ^ (α - 1))⁻¹ := by
    rw [← Real.rpow_neg hnpos.le]
    congr 1
    ring
  unfold gammaRatioThirdNormalizedError gammaRatioSecondCoeff gammaRatioThirdCoeff
  rw [hpow_inv]
  field_simp [hpow_ne, hnne]

lemma gammaRatioThirdNormalizedError_isBigO_inv_cube {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => gammaRatioThirdNormalizedError α n)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  have h := gammaRatioThirdNormalizedError_isBigO (α := α) hα
  refine h.congr' (EventuallyEq.refl _ _) ?_
  filter_upwards with n
  rw [Real.rpow_neg (Nat.cast_nonneg n)]
  norm_num [inv_pow]

private lemma inv_nat_cube_tendsto_zero :
    Tendsto (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) atTop (𝓝 0) := by
  simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 3

private lemma inv_nat_isBigO_one :
    (fun n : ℕ => (n : ℝ)⁻¹) =O[atTop] (fun _n : ℕ => (1 : ℝ)) := by
  exact (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).isBigO_one ℝ

private lemma inv_nat_sq_isBigO_one :
    (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) =O[atTop] (fun _n : ℕ => (1 : ℝ)) := by
  exact ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2).isBigO_one ℝ

private lemma inv_nat_cube_isBigO_one :
    (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) =O[atTop] (fun _n : ℕ => (1 : ℝ)) := by
  exact inv_nat_cube_tendsto_zero.isBigO_one ℝ

private lemma inv_nat_mul_inv_sq_isBigO_inv_cube :
    (fun n : ℕ => (n : ℝ)⁻¹ * ((n : ℝ)⁻¹) ^ 2)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  refine (isBigO_refl (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) atTop).congr' ?_
    (EventuallyEq.refl _ _)
  filter_upwards with n
  ring

private lemma inv_nat_four_isBigO_inv_cube :
    (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  refine IsBigO.of_bound 1 ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hinv_nonneg : 0 ≤ (n : ℝ)⁻¹ := by positivity
  have hinv_le_one : (n : ℝ)⁻¹ ≤ 1 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact inv_le_one_of_one_le₀ hn1
  rw [Real.norm_of_nonneg (pow_nonneg hinv_nonneg 4),
    Real.norm_of_nonneg (pow_nonneg hinv_nonneg 3)]
  nlinarith [mul_le_mul_of_nonneg_right hinv_le_one (pow_nonneg hinv_nonneg 3)]

private lemma quadratic_error_mul_isBigO_inv_cube
    {e f : ℕ → ℝ} {a b c d : ℝ}
    (he : e =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3))
    (hf : f =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3)) :
    (fun n : ℕ =>
      (1 + a * (n : ℝ)⁻¹ + b * ((n : ℝ)⁻¹) ^ 2 + e n) *
          (1 + c * (n : ℝ)⁻¹ + d * ((n : ℝ)⁻¹) ^ 2 + f n) -
        (1 + (a + c) * (n : ℝ)⁻¹ + (b + d + a * c) * ((n : ℝ)⁻¹) ^ 2))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  have hI3 : (fun n : ℕ => (a * d + b * c) *
      ((n : ℝ)⁻¹ * ((n : ℝ)⁻¹) ^ 2))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) :=
    inv_nat_mul_inv_sq_isBigO_inv_cube.const_mul_left (a * d + b * c)
  have hI4 : (fun n : ℕ => b * d * ((n : ℝ)⁻¹) ^ 4)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) :=
    inv_nat_four_isBigO_inv_cube.const_mul_left (b * d)
  have hIf : (fun n : ℕ => a * (n : ℝ)⁻¹ * f n)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
    have h := (inv_nat_isBigO_one.const_mul_left a).mul hf
    simpa [Pi.mul_apply, mul_assoc] using h
  have hI2f : (fun n : ℕ => b * ((n : ℝ)⁻¹) ^ 2 * f n)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
    have h := (inv_nat_sq_isBigO_one.const_mul_left b).mul hf
    simpa [Pi.mul_apply, mul_assoc] using h
  have hIe : (fun n : ℕ => c * (n : ℝ)⁻¹ * e n)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
    have h := (inv_nat_isBigO_one.const_mul_left c).mul he
    simpa [Pi.mul_apply, mul_assoc] using h
  have hI2e : (fun n : ℕ => d * ((n : ℝ)⁻¹) ^ 2 * e n)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
    have h := (inv_nat_sq_isBigO_one.const_mul_left d).mul he
    simpa [Pi.mul_apply, mul_assoc] using h
  have hf_one : f =O[atTop] (fun _n : ℕ => (1 : ℝ)) :=
    hf.trans inv_nat_cube_isBigO_one
  have hef : (fun n : ℕ => e n * f n)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
    have h := he.mul hf_one
    simpa [Pi.mul_apply] using h
  have hsum := (((((((hI3.add hI4).add hf).add he).add hIf).add hI2f).add hIe).add hI2e).add hef
  refine hsum.congr_left ?_
  intro n
  ring

private lemma quadratic_error_inv_isBigO_inv_cube
    {e : ℕ → ℝ} {a b : ℝ}
    (he : e =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3)) :
    (fun n : ℕ =>
      (1 + a * (n : ℝ)⁻¹ + b * ((n : ℝ)⁻¹) ^ 2 + e n)⁻¹ -
        (1 - a * (n : ℝ)⁻¹ + (a * a - b) * ((n : ℝ)⁻¹) ^ 2))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  have he0 : Tendsto e atTop (𝓝 0) :=
    he.trans_tendsto inv_nat_cube_tendsto_zero
  have hlin0 : Tendsto (fun n : ℕ => a * (n : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul a
  have hquad0 : Tendsto (fun n : ℕ => b * ((n : ℝ)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2).const_mul b
  have hden0 :
      Tendsto (fun n : ℕ => 1 + a * (n : ℝ)⁻¹ +
        b * ((n : ℝ)⁻¹) ^ 2 + e n) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds.add hlin0).add hquad0).add he0
  have hden_ne : ∀ᶠ n : ℕ in atTop,
      1 + a * (n : ℝ)⁻¹ + b * ((n : ℝ)⁻¹) ^ 2 + e n ≠ 0 :=
    hden0.eventually (compl_singleton_mem_nhds (by norm_num : (1 : ℝ) ≠ 0))
  have hden_inv_one :
      (fun n : ℕ => (1 + a * (n : ℝ)⁻¹ +
        b * ((n : ℝ)⁻¹) ^ 2 + e n)⁻¹)
        =O[atTop] (fun _n : ℕ => (1 : ℝ)) :=
    (hden0.inv₀ (by norm_num : (1 : ℝ) ≠ 0)).isBigO_one ℝ
  have hI3 : (fun n : ℕ => -(a * a * a - 2 * a * b) *
      ((n : ℝ)⁻¹ * ((n : ℝ)⁻¹) ^ 2))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) :=
    inv_nat_mul_inv_sq_isBigO_inv_cube.const_mul_left (-(a * a * a - 2 * a * b))
  have hI4 : (fun n : ℕ => -(b * (a * a - b)) * ((n : ℝ)⁻¹) ^ 4)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) :=
    inv_nat_four_isBigO_inv_cube.const_mul_left (-(b * (a * a - b)))
  have hIe : (fun n : ℕ => a * (n : ℝ)⁻¹ * e n)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
    have h := (inv_nat_isBigO_one.const_mul_left a).mul he
    simpa [Pi.mul_apply, mul_assoc] using h
  have hI2e : (fun n : ℕ => -(a * a - b) * ((n : ℝ)⁻¹) ^ 2 * e n)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
    have h := (inv_nat_sq_isBigO_one.const_mul_left (-(a * a - b))).mul he
    simpa [Pi.mul_apply, mul_assoc] using h
  have hnum : (fun n : ℕ =>
      -e n + a * (n : ℝ)⁻¹ * e n -
        (a * a - b) * ((n : ℝ)⁻¹) ^ 2 * e n -
        (a * a * a - 2 * a * b) *
          ((n : ℝ)⁻¹ * ((n : ℝ)⁻¹) ^ 2) -
        b * (a * a - b) * ((n : ℝ)⁻¹) ^ 4)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
    have hsum := (((he.neg_left.add hIe).add hI2e).add hI3).add hI4
    convert hsum using 1
    ext n
    ring_nf
  have hprod := hnum.mul hden_inv_one
  refine hprod.congr' ?_ ?_
  · filter_upwards [hden_ne] with n hne
    let I : ℝ := (n : ℝ)⁻¹
    let D : ℝ := 1 + a * I + b * I ^ 2 + e n
    let q : ℝ := 1 - a * I + (a * a - b) * I ^ 2
    let N : ℝ :=
      -e n + a * I * e n - (a * a - b) * I ^ 2 * e n -
        (a * a * a - 2 * a * b) * (I * I ^ 2) -
          b * (a * a - b) * I ^ 4
    change N * D⁻¹ = D⁻¹ - q
    have hD : D ≠ 0 := by
      simpa [D, I] using hne
    have hN : N = 1 - q * D := by
      dsimp [N, q, D]
      ring
    rw [hN]
    calc
      (1 - q * D) * D⁻¹ = D⁻¹ - q * (D * D⁻¹) := by ring
      _ = D⁻¹ - q * 1 := by rw [mul_inv_cancel₀ hD]
      _ = D⁻¹ - q := by ring
  · filter_upwards with n
    ring

theorem ternaryGammaThirdNormalizedProduct_thirdOrder :
    (fun n : ℕ =>
      ternaryGammaThirdNormalizedProduct n -
        (1 + ternaryRelativeSecondConstant * (n : ℝ)⁻¹ +
          ternaryRelativeThirdConstant * ((n : ℝ)⁻¹) ^ 2))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  let c₁ : ℝ := gammaRatioSecondCoeff (1 / 3 : ℝ)
  let c₂ : ℝ := gammaRatioSecondCoeff (2 / 3 : ℝ)
  let c₃ : ℝ := gammaRatioSecondCoeff (3 / 2 : ℝ)
  let d₁ : ℝ := gammaRatioThirdCoeff (1 / 3 : ℝ)
  let d₂ : ℝ := gammaRatioThirdCoeff (2 / 3 : ℝ)
  let d₃ : ℝ := gammaRatioThirdCoeff (3 / 2 : ℝ)
  let e₁ : ℕ → ℝ := gammaRatioThirdNormalizedError (1 / 3 : ℝ)
  let e₂ : ℕ → ℝ := gammaRatioThirdNormalizedError (2 / 3 : ℝ)
  let e₃ : ℕ → ℝ := gammaRatioThirdNormalizedError (3 / 2 : ℝ)
  let e₁₂ : ℕ → ℝ := fun n =>
    (1 + c₁ * (n : ℝ)⁻¹ + d₁ * ((n : ℝ)⁻¹) ^ 2 + e₁ n) *
        (1 + c₂ * (n : ℝ)⁻¹ + d₂ * ((n : ℝ)⁻¹) ^ 2 + e₂ n) -
      (1 + (c₁ + c₂) * (n : ℝ)⁻¹ +
        (d₁ + d₂ + c₁ * c₂) * ((n : ℝ)⁻¹) ^ 2)
  let e₃inv : ℕ → ℝ := fun n =>
    (1 + c₃ * (n : ℝ)⁻¹ + d₃ * ((n : ℝ)⁻¹) ^ 2 + e₃ n)⁻¹ -
      (1 - c₃ * (n : ℝ)⁻¹ + (c₃ * c₃ - d₃) * ((n : ℝ)⁻¹) ^ 2)
  have he₁ : e₁ =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
    simpa [e₁] using
      gammaRatioThirdNormalizedError_isBigO_inv_cube
        (α := (1 / 3 : ℝ)) (by norm_num : (0 : ℝ) < 1 / 3)
  have he₂ : e₂ =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
    simpa [e₂] using
      gammaRatioThirdNormalizedError_isBigO_inv_cube
        (α := (2 / 3 : ℝ)) (by norm_num : (0 : ℝ) < 2 / 3)
  have he₃ : e₃ =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
    simpa [e₃] using
      gammaRatioThirdNormalizedError_isBigO_inv_cube
        (α := (3 / 2 : ℝ)) (by norm_num : (0 : ℝ) < 3 / 2)
  have he₁₂ : e₁₂ =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
    simpa [e₁₂] using
      quadratic_error_mul_isBigO_inv_cube
        (a := c₁) (b := d₁) (c := c₂) (d := d₂) he₁ he₂
  have he₃inv : e₃inv =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
    simpa [e₃inv] using
      quadratic_error_inv_isBigO_inv_cube (a := c₃) (b := d₃) he₃
  have hprod :=
    quadratic_error_mul_isBigO_inv_cube
      (e := e₁₂) (f := e₃inv)
      (a := c₁ + c₂) (b := d₁ + d₂ + c₁ * c₂)
      (c := -c₃) (d := c₃ * c₃ - d₃) he₁₂ he₃inv
  have hcorr₁ : c₁ + c₂ - c₃ = ternaryRelativeSecondConstant := by
    simpa [c₁, c₂, c₃] using ternary_gamma_ratio_correction
  have hcorr₂ :
      d₁ + d₂ - d₃ + c₁ * c₂ + c₃ * c₃ - c₃ * c₁ - c₃ * c₂ =
        ternaryRelativeThirdConstant := by
    simpa [c₁, c₂, c₃, d₁, d₂, d₃, mul_assoc, add_assoc, add_comm,
      add_left_comm, sub_eq_add_neg] using ternary_gamma_ratio_third_correction
  refine hprod.congr_left ?_
  intro n
  unfold ternaryGammaThirdNormalizedProduct gammaRatioThirdNormalizedFactor
  dsimp [e₁, e₂, e₃, e₁₂, e₃inv, c₁, c₂, c₃, d₁, d₂, d₃]
  rw [← hcorr₁, ← hcorr₂]
  ring

theorem ternaryGammaProduct_normalized_thirdOrder :
    (fun n : ℕ =>
      (ternaryGammaRatio (1 / 3 : ℝ) n *
          ternaryGammaRatio (2 / 3 : ℝ) n /
          ternaryGammaRatio (3 / 2 : ℝ) n) /
        ((n : ℝ) ^ (-(3 / 2 : ℝ))) -
        (1 + ternaryRelativeSecondConstant * (n : ℝ)⁻¹ +
          ternaryRelativeThirdConstant * ((n : ℝ)⁻¹) ^ 2))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  refine ternaryGammaThirdNormalizedProduct_thirdOrder.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [ternaryGammaProduct_normalized_eq_of_one_le hn,
    ← ternaryGammaThirdNormalizedProduct_eq_second n]

theorem ternaryTreeCount_normalized_thirdOrder :
    (fun n : ℕ =>
      (ternaryTreeCount n : ℝ) /
          ((27 / 4 : ℝ) ^ n * ternaryAsymptoticConstant *
            (n : ℝ) ^ (-(3 / 2 : ℝ))) -
        (1 + ternaryRelativeSecondConstant * (n : ℝ)⁻¹ +
          ternaryRelativeThirdConstant * ((n : ℝ)⁻¹) ^ 2))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  refine ternaryGammaProduct_normalized_thirdOrder.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  have hbase : (27 / 4 : ℝ) ^ n ≠ 0 :=
    pow_ne_zero n (by norm_num : (27 / 4 : ℝ) ≠ 0)
  have hK : ternaryAsymptoticConstant ≠ 0 := by
    unfold ternaryAsymptoticConstant
    positivity
  have hp : (n : ℝ) ^ (-(3 / 2 : ℝ)) ≠ 0 :=
    (Real.rpow_pos_of_pos hnpos _).ne'
  rw [ternaryTreeCount_eq_gamma_ratios n]
  field_simp [hbase, hK, hp]

end
