import AnalyticCombinatorics.Ch4.Analytic.ModelCoeffSecondOrder
import AnalyticCombinatorics.Ch4.Analytic.LittleODescent

/-!
# Second-order two-term transfer

This file assembles the two-term transfer theorem from the committed model
coefficient estimates and the all-real little-o coefficient descent.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics
open scoped Topology BigOperators

noncomputable section

private lemma coeff_sub_const_smul (C : ℂ)
    (p q : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
    (p - C • q).coeff n = p.coeff n - C * q.coeff n := by
  change (p n - (C • q) n) 1 = p n 1 - C * q.coeff n
  rw [FormalMultilinearSeries.smul_apply]
  rw [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.smul_apply]
  change p.coeff n - C • q.coeff n = p.coeff n - C * q.coeff n
  simp [smul_eq_mul]

private lemma coeff_sub_two_const_smul (C0 C1 : ℂ)
    (p q0 q1 : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
    (p - C0 • q0 - C1 • q1).coeff n =
      p.coeff n - C0 * q0.coeff n - C1 * q1.coeff n := by
  rw [coeff_sub_const_smul, coeff_sub_const_smul]

private lemma rpow_sub_one_isLittleO (a : ℝ) :
    (fun n : ℕ => (n : ℝ) ^ (a - 1)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ a) := by
  refine IsLittleO.of_bound ?_
  intro c hc
  have hsmall : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ < c :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (Iio_mem_nhds hc)
  filter_upwards [eventually_ge_atTop 1, hsmall] with n hn hninvc
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  have hpowpos : 0 < (n : ℝ) ^ a := Real.rpow_pos_of_pos hnpos a
  have hleft_nonneg : 0 ≤ (n : ℝ) ^ (a - 1) := Real.rpow_nonneg (le_of_lt hnpos) _
  have hright_nonneg : 0 ≤ (n : ℝ) ^ a := le_of_lt hpowpos
  have hpow_eq : (n : ℝ) ^ (a - 1) = (n : ℝ) ^ a * (n : ℝ)⁻¹ := by
    calc
      (n : ℝ) ^ (a - 1) = (n : ℝ) ^ (a + (-(1 : ℝ))) := by ring_nf
      _ = (n : ℝ) ^ a * (n : ℝ) ^ (-(1 : ℝ)) := by rw [Real.rpow_add hnpos]
      _ = (n : ℝ) ^ a * (n : ℝ)⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hnpos), Real.rpow_one]
  calc
    ‖(n : ℝ) ^ (a - 1)‖ = (n : ℝ) ^ (a - 1) := Real.norm_of_nonneg hleft_nonneg
    _ = (n : ℝ) ^ a * (n : ℝ)⁻¹ := hpow_eq
    _ ≤ (n : ℝ) ^ a * c :=
      mul_le_mul_of_nonneg_left (le_of_lt hninvc) (le_of_lt hpowpos)
    _ = c * ‖(n : ℝ) ^ a‖ := by
      rw [Real.norm_of_nonneg hright_nonneg]
      ring

private lemma model0_expand_real {α : ℝ} (hα : 1 < α) {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ) ^ (α - 1) / Real.Gamma α) *
        (1 + α * (α - 1) / (2 * (n : ℝ))) =
      (n : ℝ) ^ (α - 1) / Real.Gamma α +
        (α * (α - 1) / 2 / Real.Gamma α) * (n : ℝ) ^ (α - 2) := by
  have hΓ : Real.Gamma α ≠ 0 := (Real.Gamma_pos_of_pos (by linarith : 0 < α)).ne'
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  have hnne : (n : ℝ) ≠ 0 := hnpos.ne'
  have hpow : (n : ℝ) ^ (α - 2) = (n : ℝ) ^ (α - 1) * (n : ℝ)⁻¹ := by
    calc
      (n : ℝ) ^ (α - 2) = (n : ℝ) ^ ((α - 1) + (-(1 : ℝ))) := by ring_nf
      _ = (n : ℝ) ^ (α - 1) * (n : ℝ) ^ (-(1 : ℝ)) := by rw [Real.rpow_add hnpos]
      _ = (n : ℝ) ^ (α - 1) * (n : ℝ)⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hnpos), Real.rpow_one]
  rw [hpow]
  field_simp [hΓ, hnne]

private lemma model0_expand_eventually {α : ℝ} (hα : 1 < α) :
    (fun n : ℕ =>
      ((n : ℝ) ^ (α - 1) / Real.Gamma α) *
        (1 + α * (α - 1) / (2 * (n : ℝ))))
      =ᶠ[atTop]
    (fun n : ℕ =>
      (n : ℝ) ^ (α - 1) / Real.Gamma α +
        (α * (α - 1) / 2 / Real.Gamma α) * (n : ℝ) ^ (α - 2)) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact model0_expand_real hα hn

private lemma modelCoeff_secondOrder_littleO {α : ℝ} (hα : 1 < α) :
    (fun n : ℕ =>
      Ring.choose (α + n - 1) n -
        ((n : ℝ) ^ (α - 1) / Real.Gamma α +
          (α * (α - 1) / 2 / Real.Gamma α) * (n : ℝ) ^ (α - 2)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
  have hcompact :
      (fun n : ℕ =>
        Ring.choose (α + n - 1) n -
          ((n : ℝ) ^ (α - 1) / Real.Gamma α) *
            (1 + α * (α - 1) / (2 * (n : ℝ))))
        =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
    have hO := modelCoeff_secondOrder (α := α) (by linarith : 0 < α)
    have ho : (fun n : ℕ => (n : ℝ) ^ (α - 3)) =o[atTop]
        (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
      convert rpow_sub_one_isLittleO (α - 2) using 1
      ext n
      congr 1
      ring
    exact hO.trans_isLittleO ho
  have hEq :
      (fun n : ℕ =>
        Ring.choose (α + n - 1) n -
          ((n : ℝ) ^ (α - 1) / Real.Gamma α +
            (α * (α - 1) / 2 / Real.Gamma α) * (n : ℝ) ^ (α - 2)))
        =ᶠ[atTop]
      (fun n : ℕ =>
        Ring.choose (α + n - 1) n -
          ((n : ℝ) ^ (α - 1) / Real.Gamma α) *
            (1 + α * (α - 1) / (2 * (n : ℝ)))) := by
    filter_upwards [model0_expand_eventually hα] with n hn
    rw [hn]
  exact hEq.trans_isLittleO hcompact

private lemma modelCoeff_leading_sub_littleO {α : ℝ} (hα : 1 < α) :
    (fun n : ℕ =>
      Ring.choose ((α - 1) + n - 1) n -
        (n : ℝ) ^ (α - 2) / Real.Gamma (α - 1))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
  have hO := modelCoeff_explicit (α := α - 1) (by linarith : 0 < α - 1)
  have ho : (fun n : ℕ => (n : ℝ) ^ (α - 1 - 2)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
    convert rpow_sub_one_isLittleO (α - 2) using 1
    ext n
    congr 1
    ring
  convert hO.trans_isLittleO ho using 1
  · ext n
    congr 2
    ring_nf

private lemma ofReal_isLittleO {u v : ℕ → ℝ}
    (h : u =o[atTop] v) :
    (fun n : ℕ => ((u n : ℝ) : ℂ)) =o[atTop] v := by
  exact Asymptotics.IsLittleO.of_norm_left (by
    simpa [Complex.norm_real] using h.norm_left)

/--
Second-order two-term transfer for a real exponent `α > 1`.

The `C0` model contributes the displayed correction
`C0 * (α*(α-1)/2/Γ(α)) * n^(α-2)`, so the `n^(α-2)` coefficient is the sum of
that correction and the leading contribution from the `C1` model.
-/
theorem transfer_twoTerm_secondOrder
    {α : ℝ} {C0 C1 : ℂ} {R φ : ℝ} {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hα : 1 < α) (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p 0)
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ =>
        ‖f z - C0 * (1 - z) ^ (-(α : ℂ)) -
            C1 * (1 - z) ^ (-(((α - 1 : ℝ) : ℂ)))‖ *
          ‖(1 : ℂ) - z‖ ^ (α - 1))
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ =>
      p.coeff n -
        (C0 *
            ((((n : ℝ) ^ (α - 1) / Real.Gamma α : ℝ) : ℂ) +
              (((α * (α - 1) / 2 / Real.Gamma α) *
                  (n : ℝ) ^ (α - 2) : ℝ) : ℂ)) +
          C1 * (((n : ℝ) ^ (α - 2) / Real.Gamma (α - 1) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
  let h0 : ℂ → ℂ := fun z => (1 - z) ^ (-(α : ℂ))
  let h1 : ℂ → ℂ := fun z => (1 - z) ^ (-(((α - 1 : ℝ) : ℂ)))
  let q0 : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ
      (fun n : ℕ => Ring.choose ((α : ℂ) + n - 1) n)
  let q1 : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ
      (fun n : ℕ => Ring.choose (((α - 1 : ℝ) : ℂ) + n - 1) n)
  let a0 : ℕ → ℂ := fun n =>
    (((n : ℝ) ^ (α - 1) / Real.Gamma α : ℝ) : ℂ) +
      (((α * (α - 1) / 2 / Real.Gamma α) * (n : ℝ) ^ (α - 2) : ℝ) : ℂ)
  let a1 : ℕ → ℂ := fun n =>
    (((n : ℝ) ^ (α - 2) / Real.Gamma (α - 1) : ℝ) : ℂ)
  have hφπ : φ < Real.pi := by linarith [hφ2, Real.pi_pos]
  have hp0 : HasFPowerSeriesAt h0 q0 0 := by
    have hraw := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (α : ℂ)).hasFPowerSeriesAt
    convert hraw using 1
    ext z
    dsimp [h0]
    rw [Complex.cpow_neg, inv_eq_one_div]
  have hp1 : HasFPowerSeriesAt h1 q1 0 := by
    have hraw :=
      (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (((α - 1 : ℝ) : ℂ))).hasFPowerSeriesAt
    convert hraw using 1
    ext z
    dsimp [h1]
    rw [Complex.cpow_neg, inv_eq_one_div]
  have hΔ0 : AnalyticOnNhd ℂ h0 (DeltaDomainArg R φ) := by
    simpa [h0] using
      (analyticOnNhd_one_sub_cpow_deltaDomain
        (α := (α : ℂ)) (R := R) (φ := φ) hφ0 hφπ)
  have hΔ1 : AnalyticOnNhd ℂ h1 (DeltaDomainArg R φ) := by
    simpa [h1] using
      (analyticOnNhd_one_sub_cpow_deltaDomain
        (α := (((α - 1 : ℝ) : ℂ))) (R := R) (φ := φ) hφ0 hφπ)
  have hpR : HasFPowerSeriesAt
      (fun z : ℂ => f z - C0 • h0 z - C1 • h1 z)
      (p - C0 • q0 - C1 • q1) 0 :=
    (hp.sub (hp0.const_smul (c := C0))).sub (hp1.const_smul (c := C1))
  have hΔR : AnalyticOnNhd ℂ
      (fun z : ℂ => f z - C0 • h0 z - C1 • h1 z)
      (DeltaDomainArg R φ) :=
    (hΔ.sub (hΔ0.const_smul (c := C0))).sub (hΔ1.const_smul (c := C1))
  have hres_norm : (fun n : ℕ => ‖(p - C0 • q0 - C1 • q1).coeff n‖)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
    convert coeff_norm_isLittleO_atTop_of_delta_littleO
      (R := R) (φ := φ) (β := α - 1)
      (f := fun z : ℂ => f z - C0 • h0 z - C1 • h1 z)
      (p := p - C0 • q0 - C1 • q1)
      hR hφ0 hφ2 hpR hΔR ?_ using 1
    · ext n
      congr 1
      ring
    · simpa [h0, h1, smul_eq_mul] using hsing
  have hres : (fun n : ℕ => (p - C0 • q0 - C1 • q1).coeff n)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) :=
    Asymptotics.IsLittleO.of_norm_left hres_norm
  have h0real := modelCoeff_secondOrder_littleO hα
  have h0c :
      (fun n : ℕ =>
        ((Ring.choose (α + n - 1) n -
          ((n : ℝ) ^ (α - 1) / Real.Gamma α +
            (α * (α - 1) / 2 / Real.Gamma α) * (n : ℝ) ^ (α - 2)) : ℝ) : ℂ))
        =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) :=
    ofReal_isLittleO h0real
  have h0term : (fun n : ℕ => C0 * q0.coeff n - C0 * a0 n)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
    have h := h0c.const_mul_left C0
    have hEq : (fun n : ℕ => C0 * q0.coeff n - C0 * a0 n) =ᶠ[atTop]
        (fun n : ℕ =>
          C0 * ((Ring.choose (α + n - 1) n -
            ((n : ℝ) ^ (α - 1) / Real.Gamma α +
              (α * (α - 1) / 2 / Real.Gamma α) * (n : ℝ) ^ (α - 2)) : ℝ) : ℂ)) := by
      refine Eventually.of_forall fun n => ?_
      dsimp [q0, a0]
      rw [FormalMultilinearSeries.coeff_ofScalars, choose_ofReal_model]
      rw [← Complex.ofReal_add, Complex.ofReal_sub]
      ring
    exact hEq.trans_isLittleO h
  have h1real := modelCoeff_leading_sub_littleO hα
  have h1c :
      (fun n : ℕ =>
        ((Ring.choose ((α - 1) + n - 1) n -
          (n : ℝ) ^ (α - 2) / Real.Gamma (α - 1) : ℝ) : ℂ))
        =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) :=
    ofReal_isLittleO h1real
  have h1term : (fun n : ℕ => C1 * q1.coeff n - C1 * a1 n)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
    have h := h1c.const_mul_left C1
    have hEq : (fun n : ℕ => C1 * q1.coeff n - C1 * a1 n) =ᶠ[atTop]
        (fun n : ℕ =>
          C1 * ((Ring.choose ((α - 1) + n - 1) n -
            (n : ℝ) ^ (α - 2) / Real.Gamma (α - 1) : ℝ) : ℂ)) := by
      refine Eventually.of_forall fun n => ?_
      dsimp [q1, a1]
      rw [FormalMultilinearSeries.coeff_ofScalars, choose_ofReal_model]
      rw [Complex.ofReal_sub]
      ring
    exact hEq.trans_isLittleO h
  have hsum : (fun n : ℕ =>
      (C0 * q0.coeff n - C0 * a0 n) +
        (C1 * q1.coeff n - C1 * a1 n) +
        (p - C0 • q0 - C1 • q1).coeff n)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) :=
    (h0term.add h1term).add hres
  have hEq : (fun n : ℕ =>
      p.coeff n -
        (C0 *
            ((((n : ℝ) ^ (α - 1) / Real.Gamma α : ℝ) : ℂ) +
              (((α * (α - 1) / 2 / Real.Gamma α) *
                  (n : ℝ) ^ (α - 2) : ℝ) : ℂ)) +
          C1 * (((n : ℝ) ^ (α - 2) / Real.Gamma (α - 1) : ℝ) : ℂ)))
      =ᶠ[atTop]
    (fun n : ℕ =>
      (C0 * q0.coeff n - C0 * a0 n) +
        (C1 * q1.coeff n - C1 * a1 n) +
        (p - C0 • q0 - C1 • q1).coeff n) := by
    refine Eventually.of_forall fun n => ?_
    dsimp [a0, a1]
    rw [coeff_sub_two_const_smul]
    ring
  exact hEq.trans_isLittleO hsum

end
