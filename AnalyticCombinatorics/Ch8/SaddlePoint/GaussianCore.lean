import AnalyticCombinatorics.Ch8.SaddlePoint.Assembly
import Mathlib

/-!
# Gaussian central saddle core

This file packages the reusable dominated-convergence core for the central
Gaussian window after the saddle scaling `theta = x / sqrt (B n)`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

/-- The normalized Gaussian integral used by the saddle central window. -/
theorem gaussian_integral_half :
    (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2)) =
      (Real.sqrt (2 * Real.pi) : ℂ) := by
  have hgauss :=
    integral_gaussian_complex (b := (1 / 2 : ℂ))
      (by norm_num : 0 < (Complex.re (1 / 2 : ℂ)))
  rw [show (fun x : ℝ => Complex.exp (-(x ^ 2) / 2)) =
      (fun x : ℝ => Complex.exp (-(1 / 2 : ℂ) * (x : ℂ) ^ 2)) by
        funext x
        norm_num
        ring_nf]
  rw [hgauss]
  have hbase : (↑Real.pi / (1 / 2 : ℂ)) = (↑(2 * Real.pi) : ℂ) := by
    norm_num [div_eq_mul_inv]
    ring
  rw [hbase]
  have hexp : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [hexp]
  rw [← Complex.ofReal_cpow]
  · rw [Complex.ofReal_inj]
    rw [Real.sqrt_eq_rpow]
  · positivity

private lemma saddle_scaled_constant (B : ℕ → ℝ) (n : ℕ) (hB : 0 < B n) :
    (Real.sqrt (2 * Real.pi * B n) : ℂ) * (2 * Real.pi : ℂ)⁻¹ *
      ((Real.sqrt (B n))⁻¹ : ℂ) =
      (1 / Real.sqrt (2 * Real.pi) : ℂ) := by
  let c : ℝ := Real.sqrt (B n)
  have hc_pos : 0 < c := by simpa [c] using Real.sqrt_pos.mpr hB
  have hc_ne : c ≠ 0 := hc_pos.ne'
  have hsqrt2_pos : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hsqrt2_ne : Real.sqrt (2 * Real.pi) ≠ 0 := hsqrt2_pos.ne'
  have hsqrt_prod :
      Real.sqrt (2 * Real.pi * B n) = Real.sqrt (2 * Real.pi) * c := by
    rw [show 2 * Real.pi * B n = (2 * Real.pi) * B n by ring]
    rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
  have hconstR :
      Real.sqrt (2 * Real.pi * B n) * (2 * Real.pi)⁻¹ * c⁻¹ =
        1 / Real.sqrt (2 * Real.pi) := by
    rw [hsqrt_prod]
    calc
      (Real.sqrt (2 * Real.pi) * c) * (2 * Real.pi)⁻¹ * c⁻¹
          = Real.sqrt (2 * Real.pi) * (2 * Real.pi)⁻¹ := by
            field_simp [hc_ne]
      _ = Real.sqrt (2 * Real.pi) / (2 * Real.pi) := by
            rw [div_eq_mul_inv]
      _ = Real.sqrt (2 * Real.pi) /
            (Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi)) := by
            congr 1
            rw [← sq]
            rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
      _ = 1 / Real.sqrt (2 * Real.pi) := by
            field_simp [hsqrt2_ne]
  norm_cast

/--
After the scaling `theta = x / sqrt (B n)`, the central saddle integral has
the normalized full Gaussian prefactor.
-/
theorem saddleJc_eq_integral_scaled
    (f : ℂ → ℂ) (r δ B : ℕ → ℝ) (n : ℕ) (hB : 0 < B n) :
    (Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJc f r δ n =
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
        ∫ x in -(δ n * Real.sqrt (B n))..(δ n * Real.sqrt (B n)),
          saddleG f r n (x / Real.sqrt (B n)) := by
  let c : ℝ := Real.sqrt (B n)
  have hc_pos : 0 < c := by simpa [c] using Real.sqrt_pos.mpr hB
  have hc_ne : c ≠ 0 := hc_pos.ne'
  have hsubst :
      (∫ θ in (-(δ n))..(δ n), saddleG f r n θ) =
        c⁻¹ • ∫ x in -(δ n * c)..(δ n * c), saddleG f r n (x / c) := by
    have h := intervalIntegral.inv_smul_integral_comp_div
      (f := fun θ : ℝ => saddleG f r n θ)
      (a := -(δ n * c)) (b := δ n * c) c
    have hb : δ n * c / c = δ n := by
      exact mul_div_cancel_right₀ (δ n) hc_ne
    have ha : -(δ n * c) / c = -(δ n) := by
      rw [neg_div, hb]
    rw [ha, hb] at h
    exact h.symm
  unfold saddleJc saddleJcAt
  change (Real.sqrt (2 * Real.pi * B n) : ℂ) *
      ((2 * Real.pi : ℂ)⁻¹ * ∫ θ in (-(δ n))..(δ n), saddleG f r n θ) =
    (1 / Real.sqrt (2 * Real.pi) : ℂ) *
      ∫ x in -(δ n * c)..(δ n * c), saddleG f r n (x / c)
  rw [hsubst]
  rw [show ((c⁻¹ : ℝ) •
        ∫ (x : ℝ) in -(δ n * c)..δ n * c, saddleG f r n (x / c)) =
      ((c⁻¹ : ℂ) *
        ∫ (x : ℝ) in -(δ n * c)..δ n * c, saddleG f r n (x / c)) by
        simp]
  rw [← mul_assoc]
  rw [← mul_assoc]
  rw [show (Real.sqrt (2 * Real.pi * B n) : ℂ) * (2 * Real.pi : ℂ)⁻¹ *
      (c⁻¹ : ℂ) = (1 / Real.sqrt (2 * Real.pi) : ℂ) by
        simpa [c] using saddle_scaled_constant B n hB]

/-- The scaled central integrand with the moving cutoff built in. -/
def Hfun (f : ℂ → ℂ) (r B δ : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  if |x| ≤ δ n * Real.sqrt (B n) then
    saddleG f r n (x / Real.sqrt (B n))
  else
    0

private lemma Hfun_eq_indicator (f : ℂ → ℂ) (r B δ : ℕ → ℝ) (n : ℕ) :
    Hfun f r B δ n =
      Set.indicator (Set.Icc (-(δ n * Real.sqrt (B n))) (δ n * Real.sqrt (B n)))
        (fun x : ℝ => saddleG f r n (x / Real.sqrt (B n))) := by
  funext x
  simp [Hfun, Set.indicator, abs_le]

private lemma integral_Hfun_eq_interval
    (f : ℂ → ℂ) (r B δ : ℕ → ℝ) (n : ℕ)
    (hL : 0 ≤ δ n * Real.sqrt (B n)) :
    (∫ x : ℝ, Hfun f r B δ n x) =
      ∫ x in -(δ n * Real.sqrt (B n))..(δ n * Real.sqrt (B n)),
        saddleG f r n (x / Real.sqrt (B n)) := by
  let L : ℝ := δ n * Real.sqrt (B n)
  let g : ℝ → ℂ := fun x => saddleG f r n (x / Real.sqrt (B n))
  have hle : -L ≤ L := by linarith [hL]
  calc
    (∫ x : ℝ, Hfun f r B δ n x) =
        ∫ x : ℝ, Set.indicator (Set.Icc (-L) L) g x := by
          simp [Hfun_eq_indicator, L, g]
    _ = ∫ x in Set.Icc (-L) L, g x := by
          rw [MeasureTheory.integral_indicator measurableSet_Icc]
    _ = ∫ x in Set.Ioc (-L) L, g x := by
          rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    _ = ∫ x in (-L)..L, g x := by
          rw [intervalIntegral.integral_of_le hle]

/--
Dominated-convergence central Gaussian core, with the measurability hypothesis
required by Mathlib's DCT stated explicitly.
-/
theorem central_tendsto_one_of_dominated_of_aestronglyMeasurable
    (f : ℂ → ℂ) (r B δ : ℕ → ℝ)
    (hBpos : ∀ᶠ n in atTop, 0 < B n)
    (hL : Tendsto (fun n : ℕ => δ n * Real.sqrt (B n)) atTop atTop)
    (Hmeas :
      ∀ᶠ n in atTop,
        AEStronglyMeasurable (Hfun f r B δ n) MeasureTheory.volume)
    (Hpoint :
      ∀ᵐ x : ℝ,
        Tendsto (fun n : ℕ => Hfun f r B δ n x) atTop
          (𝓝 (Complex.exp (-(x ^ 2) / 2))))
    (D : ℝ → ℝ) (hDint : Integrable D)
    (Hdom :
      ∀ᶠ n in atTop, ∀ᵐ x : ℝ, ‖Hfun f r B δ n x‖ ≤ D x) :
    Tendsto
      (fun n : ℕ => (Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJc f r δ n)
      atTop (𝓝 1) := by
  have hInt_tendsto :
      Tendsto (fun n : ℕ => ∫ x : ℝ, Hfun f r B δ n x) atTop
        (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2))) := by
    exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := MeasureTheory.volume) (bound := D) Hmeas Hdom hDint Hpoint
  have hsqrt2_pos : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hsqrt2_ne : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt2_pos.ne'
  have hscaled :
      Tendsto
        (fun n : ℕ => (1 / Real.sqrt (2 * Real.pi) : ℂ) *
          ∫ x : ℝ, Hfun f r B δ n x)
        atTop (𝓝 1) := by
    have hmul := hInt_tendsto.const_mul (1 / Real.sqrt (2 * Real.pi) : ℂ)
    have hconst :
        (1 / Real.sqrt (2 * Real.pi) : ℂ) *
          (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2)) = 1 := by
      rw [gaussian_integral_half]
      field_simp [hsqrt2_ne]
    simpa only [hconst] using hmul
  have hLnonneg : ∀ᶠ n in atTop, 0 ≤ δ n * Real.sqrt (B n) :=
    hL.eventually_ge_atTop 0
  have heq :
      (fun n : ℕ => (Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJc f r δ n)
        =ᶠ[atTop]
      (fun n : ℕ => (1 / Real.sqrt (2 * Real.pi) : ℂ) *
        ∫ x : ℝ, Hfun f r B δ n x) := by
    filter_upwards [hBpos, hLnonneg] with n hBn hLn
    rw [saddleJc_eq_integral_scaled f r δ B n hBn]
    rw [← integral_Hfun_eq_interval f r B δ n hLn]
  exact Tendsto.congr' heq.symm hscaled

/-
Note: the prompt-shaped version dropping the measurability hypothesis is omitted;
Mathlib's dominated convergence genuinely requires `AEStronglyMeasurable` of the
integrands, which is not implied by pointwise convergence + domination for an
arbitrary `f`. The clean theorem `central_tendsto_one_of_dominated_of_aestronglyMeasurable`
takes it as a hypothesis (discharged easily for continuous integrands, e.g. the exp testbed).
-/
