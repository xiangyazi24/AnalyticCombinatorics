import Mathlib
import AnalyticCombinatorics.Ch4.Analytic.TransferGeneral
import AnalyticCombinatorics.Ch4.Analytic.RealAsymptotics
import AnalyticCombinatorics.Ch4.Analytic.CentralBinomial

/-!
# Two-regular labelled graphs

This file records the singularity-analysis asymptotic for the EGF

`exp (-z/2 - z^2/4) / sqrt (1 - z)`.

The sequence is defined through this EGF: `twoRegularGraphCount n / n!` is the
real coefficient of the Taylor expansion at zero.
-/

open Complex Filter Asymptotics
open scoped Topology BigOperators PowerSeries

noncomputable section

/-- The entire prefactor in the EGF for 2-regular labelled graphs. -/
def twoRegularPrefactor (z : ℂ) : ℂ :=
  Complex.exp (-(z / 2) - z ^ 2 / 4)

/-- The EGF as a complex analytic function. -/
def twoRegularEGFFun (z : ℂ) : ℂ :=
  twoRegularPrefactor z * (1 - z) ^ (-(1 / 2 : ℂ))

/-- The singular coefficient produced by evaluating the entire prefactor at `1`. -/
def twoRegularSingularCoeff : ℂ :=
  Complex.exp (-(3 / 4 : ℂ))

/-- The real leading constant produced by transfer. -/
def twoRegularAsymptoticConstant : ℝ :=
  Real.exp (-(3 / 4 : ℝ)) / Real.sqrt Real.pi

lemma analyticOnNhd_twoRegularPrefactor {s : Set ℂ} :
    AnalyticOnNhd ℂ twoRegularPrefactor s := by
  have hid : AnalyticOnNhd ℂ (fun z : ℂ => z) s := analyticOnNhd_id
  have hpoly :
      AnalyticOnNhd ℂ (fun z : ℂ => -(z / 2) - z ^ 2 / 4) s :=
    (hid.div_const.neg).sub ((hid.pow 2).div_const)
  simpa [twoRegularPrefactor] using hpoly.cexp

lemma analyticOnNhd_twoRegularEGFFun {R φ : ℝ} (hφ0 : 0 < φ) (hφπ : φ < Real.pi) :
    AnalyticOnNhd ℂ twoRegularEGFFun (DeltaDomainArg R φ) := by
  unfold twoRegularEGFFun
  exact analyticOnNhd_twoRegularPrefactor.mul
    (analyticOnNhd_one_sub_cpow_deltaDomain (α := (1 / 2 : ℂ))
      (R := R) (φ := φ) hφ0 hφπ)

lemma analyticAt_twoRegularEGFFun_zero :
    AnalyticAt ℂ twoRegularEGFFun (0 : ℂ) := by
  have hR : (0 : ℂ) ∈ DeltaDomainArg (3 / 2 : ℝ) (Real.pi / 4) :=
    zero_mem_deltaDomainArg (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
      (by norm_num) (by nlinarith [Real.pi_pos])
  exact analyticOnNhd_twoRegularEGFFun (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
    (by positivity) (by nlinarith [Real.pi_pos]) 0 hR

/-- The Taylor series at zero of the two-regular EGF. -/
def twoRegularEGFSeriesℂ : FormalMultilinearSeries ℂ ℂ ℂ :=
  Classical.choose analyticAt_twoRegularEGFFun_zero

lemma twoRegularEGFFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt twoRegularEGFFun twoRegularEGFSeriesℂ (0 : ℂ) :=
  Classical.choose_spec analyticAt_twoRegularEGFFun_zero

/-- The EGF coefficient `[z^n] G(z)`, as a real number. -/
def twoRegularEGFCoeff (n : ℕ) : ℝ :=
  ((twoRegularEGFSeriesℂ.coeff n).re)

/-- The labelled count defined by `g_n / n! = [z^n] G(z)`. -/
def twoRegularGraphCount (n : ℕ) : ℝ :=
  (n.factorial : ℝ) * twoRegularEGFCoeff n

lemma twoRegularGraphCount_div_factorial (n : ℕ) :
    twoRegularGraphCount n / (n.factorial : ℝ) = twoRegularEGFCoeff n := by
  unfold twoRegularGraphCount
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)]

lemma tendsto_twoRegularPrefactor_at_one :
    Tendsto twoRegularPrefactor (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ))
      (𝓝 twoRegularSingularCoeff) := by
  have hcont : ContinuousAt twoRegularPrefactor (1 : ℂ) := by
    unfold twoRegularPrefactor
    fun_prop
  convert Tendsto.mono_left hcont.tendsto nhdsWithin_le_nhds using 1
  unfold twoRegularPrefactor twoRegularSingularCoeff
  norm_num

lemma twoRegular_singularity_norm_eq {z : ℂ} (hz : z ≠ 1) :
    ‖twoRegularEGFFun z - twoRegularSingularCoeff * (1 - z) ^ (-(1 / 2 : ℂ))‖ *
        ‖(1 : ℂ) - z‖ ^ (1 / 2 : ℝ) =
      ‖twoRegularPrefactor z - twoRegularSingularCoeff‖ := by
  have hu_pos : 0 < ‖(1 : ℂ) - z‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz))
  have hpow_norm :
      ‖((1 : ℂ) - z) ^ (-(1 / 2 : ℂ))‖ =
        ‖(1 : ℂ) - z‖ ^ (-(1 / 2 : ℝ)) := by
    convert Complex.norm_cpow_real ((1 : ℂ) - z) (-(1 / 2 : ℝ)) using 1
    norm_num
  unfold twoRegularEGFFun
  rw [show twoRegularPrefactor z * (1 - z) ^ (-(1 / 2 : ℂ)) -
        twoRegularSingularCoeff * (1 - z) ^ (-(1 / 2 : ℂ)) =
        (twoRegularPrefactor z - twoRegularSingularCoeff) *
          (1 - z) ^ (-(1 / 2 : ℂ)) by ring]
  rw [norm_mul, hpow_norm, Real.rpow_neg hu_pos.le]
  have hroot_ne : ‖(1 : ℂ) - z‖ ^ (1 / 2 : ℝ) ≠ 0 := by positivity
  field_simp [hroot_ne]

lemma tendsto_twoRegular_singularity :
    Tendsto
      (fun z : ℂ =>
        ‖twoRegularEGFFun z -
            twoRegularSingularCoeff * (1 - z) ^ (-(1 / 2 : ℂ))‖ *
          ‖(1 : ℂ) - z‖ ^ (1 / 2 : ℝ))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  let l := 𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)
  have hnorm : Tendsto
      (fun z : ℂ => ‖twoRegularPrefactor z - twoRegularSingularCoeff‖) l (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℂ => twoRegularSingularCoeff) l
        (𝓝 twoRegularSingularCoeff) :=
      tendsto_const_nhds
    simpa using (tendsto_twoRegularPrefactor_at_one.sub hconst).norm
  have heq :
      (fun z : ℂ =>
        ‖twoRegularEGFFun z -
            twoRegularSingularCoeff * (1 - z) ^ (-(1 / 2 : ℂ))‖ *
          ‖(1 : ℂ) - z‖ ^ (1 / 2 : ℝ))
        =ᶠ[l]
      (fun z : ℂ => ‖twoRegularPrefactor z - twoRegularSingularCoeff‖) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact twoRegular_singularity_norm_eq hz.2.1
  exact hnorm.congr' heq.symm

lemma twoRegular_transfer_complex :
    (fun n : ℕ => twoRegularEGFSeriesℂ.coeff n) ~[atTop]
      (fun n : ℕ =>
        twoRegularSingularCoeff * (n : ℂ) ^ ((1 / 2 : ℂ) - 1) /
          Complex.Gamma (1 / 2 : ℂ)) := by
  refine transfer_theorem (α := (1 / 2 : ℂ)) (C := twoRegularSingularCoeff)
    (R := (3 / 2 : ℝ)) (φ := Real.pi / 4) (f := twoRegularEGFFun)
    (p := twoRegularEGFSeriesℂ) half_not_neg_nat ?_ ?_ ?_ ?_
    twoRegularEGFFun_hasFPowerSeriesAt_zero ?_ ?_
  · unfold twoRegularSingularCoeff
    exact Complex.exp_ne_zero _
  · norm_num
  · positivity
  · nlinarith [Real.pi_pos]
  · exact analyticOnNhd_twoRegularEGFFun (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
      (by positivity) (by nlinarith [Real.pi_pos])
  · simpa using tendsto_twoRegular_singularity

lemma twoRegular_transfer_constant_complex :
    twoRegularSingularCoeff / Complex.Gamma (1 / 2 : ℂ) =
      ((twoRegularAsymptoticConstant : ℝ) : ℂ) := by
  unfold twoRegularSingularCoeff twoRegularAsymptoticConstant
  rw [Complex.Gamma_one_half_eq]
  have hsqrtπ :
      ((Real.sqrt Real.pi : ℝ) : ℂ) = (Real.pi : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow]
    simpa using Complex.ofReal_cpow Real.pi_nonneg (1 / 2 : ℝ)
  rw [← hsqrtπ]
  norm_num [Complex.ofReal_exp, Complex.ofReal_div]

lemma transfer_target_to_twoRegular_real_eventuallyEq :
    (fun n : ℕ =>
        twoRegularSingularCoeff * (n : ℂ) ^ ((1 / 2 : ℂ) - 1) /
          Complex.Gamma (1 / 2 : ℂ)) =ᶠ[atTop]
      (fun n : ℕ =>
        ((twoRegularAsymptoticConstant * (n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by
  refine (eventually_ne_atTop 0).mono ?_
  intro n hn
  have hnnonneg : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
  have hcpow :
      (n : ℂ) ^ ((1 / 2 : ℂ) - 1) =
        (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    have h := (Complex.ofReal_cpow hnnonneg (-(1 / 2 : ℝ))).symm
    norm_num at h ⊢
    exact h
  calc
    twoRegularSingularCoeff * (n : ℂ) ^ ((1 / 2 : ℂ) - 1) /
          Complex.Gamma (1 / 2 : ℂ)
        = (twoRegularSingularCoeff / Complex.Gamma (1 / 2 : ℂ)) *
            (n : ℂ) ^ ((1 / 2 : ℂ) - 1) := by ring
    _ = (twoRegularAsymptoticConstant : ℂ) *
          (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
        rw [twoRegular_transfer_constant_complex, hcpow]
    _ = ((twoRegularAsymptoticConstant * (n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
        norm_num [Complex.ofReal_mul]

lemma complex_re_isEquivalent_ofReal {f : ℕ → ℂ} {g : ℕ → ℝ}
    (h : f ~[atTop] fun n : ℕ => (g n : ℂ)) :
    (fun n : ℕ => (f n).re) ~[atTop] g := by
  rw [Asymptotics.IsEquivalent] at h ⊢
  rw [Asymptotics.isLittleO_iff] at h ⊢
  intro c hc
  have hc_bound := h hc
  filter_upwards [hc_bound] with n hn
  calc
    ‖(f n).re - g n‖ = ‖(f n - (g n : ℂ)).re‖ := by
      simp [Complex.sub_re]
    _ ≤ ‖f n - (g n : ℂ)‖ := Complex.abs_re_le_norm _
    _ ≤ c * ‖(g n : ℂ)‖ := hn
    _ = c * ‖g n‖ := by rw [Complex.norm_real]

lemma twoRegularEGFCoeff_isEquivalent :
    (fun n : ℕ => twoRegularEGFCoeff n) ~[atTop]
      (fun n : ℕ => twoRegularAsymptoticConstant * (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have hcomplex := twoRegular_transfer_complex.trans_eventuallyEq
    transfer_target_to_twoRegular_real_eventuallyEq
  exact complex_re_isEquivalent_ofReal hcomplex

/-- Main asymptotic for the EGF-defined 2-regular labelled graph counts. -/
theorem twoRegularGraphCount_div_factorial_isEquivalent :
    (fun n : ℕ => twoRegularGraphCount n / (n.factorial : ℝ)) ~[atTop]
      (fun n : ℕ => twoRegularAsymptoticConstant * (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have hbridge :
      (fun n : ℕ => twoRegularGraphCount n / (n.factorial : ℝ)) =ᶠ[atTop]
        (fun n : ℕ => twoRegularEGFCoeff n) :=
    Eventually.of_forall twoRegularGraphCount_div_factorial
  exact hbridge.trans_isEquivalent twoRegularEGFCoeff_isEquivalent

/-- The constant is the expected `exp (-3/4) / sqrt pi`. -/
theorem twoRegularAsymptoticConstant_eq :
    twoRegularAsymptoticConstant = Real.exp (-(3 / 4 : ℝ)) / Real.sqrt Real.pi := by
  rfl
