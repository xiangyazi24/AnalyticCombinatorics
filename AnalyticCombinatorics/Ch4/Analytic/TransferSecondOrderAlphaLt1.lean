import AnalyticCombinatorics.Ch4.Analytic.TransferSecondOrder

/-!
# Second-order transfer for `0 < α < 1`

This file derives the second-order two-term transfer below the threshold
`α = 1` by differentiating once, applying the committed `α > 1` transfer to
the derivative, and descending coefficients through
`[z^m] f' = (m + 1) [z^(m+1)] f`.
-/

open Complex Filter Asymptotics
open scoped Topology BigOperators

noncomputable section

private lemma ofReal_isLittleO {u v : ℕ → ℝ}
    (h : u =o[atTop] v) :
    (fun n : ℕ => ((u n : ℝ) : ℂ)) =o[atTop] v := by
  exact Asymptotics.IsLittleO.of_norm_left (by
    simpa [Complex.norm_real] using h.norm_left)

private lemma deriv_one_sub_cpow_neg {a : ℝ} {z : ℂ}
    (hz : (1 - z) ∈ Complex.slitPlane) :
    deriv (fun w : ℂ => (1 - w) ^ (-(a : ℂ))) z =
      (a : ℂ) * (1 - z) ^ (-(((a + 1 : ℝ) : ℂ))) := by
  have hdiff : DifferentiableAt ℂ (fun w : ℂ => 1 - w) z := by fun_prop
  have hder : deriv (fun w : ℂ => 1 - w) z = -1 := by
    rw [deriv_const_sub]
    simp [deriv_id'']
  rw [deriv_cpow_const hdiff hz, hder]
  have hexp : (-(a : ℂ) - 1) = (-(((a + 1 : ℝ) : ℂ))) := by
    norm_num [Complex.ofReal_add]
    ring
  rw [hexp]
  ring

private lemma deriv_one_sub_cpow_neg_sub_one {α : ℝ} {z : ℂ}
    (hz : (1 - z) ∈ Complex.slitPlane) :
    deriv (fun w : ℂ => (1 - w) ^ (-(((α - 1 : ℝ) : ℂ)))) z =
      ((α - 1 : ℝ) : ℂ) * (1 - z) ^ (-(α : ℂ)) := by
  have h := deriv_one_sub_cpow_neg (a := α - 1) (z := z) hz
  simpa [sub_add_cancel] using h

private lemma one_sub_rpow_sub_linear_isLittleO (a : ℝ) :
    (fun x : ℝ => (1 - x) ^ a - 1 + a * x) =o[𝓝 0]
      (fun x : ℝ => x) := by
  have hlin : HasDerivAt (fun x : ℝ => 1 - x) (-1) 0 := by
    simpa using
      (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id (0 : ℝ))
  have hpow : HasDerivAt (fun x : ℝ => (1 - x) ^ a) (-a) 0 := by
    have h := hlin.rpow_const (p := a)
      (Or.inl (by norm_num : (1 : ℝ) - 0 ≠ 0))
    simpa using h
  have ho := hpow.isLittleO
  simpa [mul_comm, mul_left_comm, mul_assoc] using ho

private lemma rpow_mul_inv_eventually (a : ℝ) :
    (fun n : ℕ => (n : ℝ) ^ (a - 1) * (n : ℝ)⁻¹) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (a - 2)) := by
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  calc
    (n : ℝ) ^ (a - 1) * (n : ℝ)⁻¹
        = (n : ℝ) ^ (a - 1) * (n : ℝ) ^ (-(1 : ℝ)) := by
            rw [Real.rpow_neg hnpos.le, Real.rpow_one]
    _ = (n : ℝ) ^ ((a - 1) + (-(1 : ℝ))) := by
            rw [← Real.rpow_add hnpos]
    _ = (n : ℝ) ^ (a - 2) := by ring_nf

private lemma shifted_rpow_div_first (a : ℝ) :
    (fun n : ℕ =>
      ((n - 1 : ℕ) : ℝ) ^ a / (n : ℝ) - (n : ℝ) ^ (a - 1) +
        a * (n : ℝ) ^ (a - 2))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (a - 2)) := by
  let H : ℝ → ℝ := fun x => (1 - x) ^ a - 1 + a * x
  have hH : H =o[𝓝 0] (fun x : ℝ => x) := by
    simpa [H] using one_sub_rpow_sub_linear_isLittleO a
  have hHinv : (fun n : ℕ => H ((n : ℝ)⁻¹)) =o[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
    simpa using hH.comp_tendsto (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hprod :=
    (isBigO_refl (fun n : ℕ => (n : ℝ) ^ (a - 1)) atTop).mul_isLittleO hHinv
  have hprod' : (fun n : ℕ => (n : ℝ) ^ (a - 1) * H ((n : ℝ)⁻¹))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (a - 2)) := by
    exact hprod.trans_eventuallyEq (rpow_mul_inv_eventually a)
  have heq : (fun n : ℕ =>
      ((n - 1 : ℕ) : ℝ) ^ a / (n : ℝ) - (n : ℝ) ^ (a - 1) +
        a * (n : ℝ) ^ (a - 2)) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (a - 1) * H ((n : ℝ)⁻¹)) := by
    refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    let x : ℝ := n
    have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn
    have hnpos : 0 < x := by dsimp [x]; exact_mod_cast hnpos_nat
    have hn1 : (1 : ℝ) ≤ x := by dsimp [x]; exact_mod_cast hn
    have hcast_sub : ((n - 1 : ℕ) : ℝ) = x - 1 := by
      dsimp [x]
      norm_num [Nat.cast_sub hn]
    have hy_nonneg : 0 ≤ 1 - x⁻¹ := by
      have hinv_le : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn1
      linarith
    have hmulbase : x * (1 - x⁻¹) = x - 1 := by
      field_simp [hnpos.ne']
    have hpowsub : ((n - 1 : ℕ) : ℝ) ^ a =
        x ^ a * (1 - x⁻¹) ^ a := by
      rw [hcast_sub, ← hmulbase]
      exact Real.mul_rpow hnpos.le hy_nonneg
    have hdivpow : ((n - 1 : ℕ) : ℝ) ^ a / x =
        x ^ (a - 1) * (1 - x⁻¹) ^ a := by
      rw [hpowsub]
      have hxpow : x ^ a / x = x ^ (a - 1) := by
        calc
          x ^ a / x = x ^ a * x⁻¹ := by rw [div_eq_mul_inv]
          _ = x ^ a * x ^ (-(1 : ℝ)) := by
                rw [Real.rpow_neg hnpos.le, Real.rpow_one]
          _ = x ^ (a + (-(1 : ℝ))) := by rw [← Real.rpow_add hnpos]
          _ = x ^ (a - 1) := by ring_nf
      rw [show x ^ a * (1 - x⁻¹) ^ a / x =
          (x ^ a / x) * (1 - x⁻¹) ^ a by ring]
      rw [hxpow]
    have hpowinv : x ^ (a - 1) * x⁻¹ = x ^ (a - 2) := by
      calc
        x ^ (a - 1) * x⁻¹ =
            x ^ (a - 1) * x ^ (-(1 : ℝ)) := by
              rw [Real.rpow_neg hnpos.le, Real.rpow_one]
        _ = x ^ ((a - 1) + (-(1 : ℝ))) := by rw [← Real.rpow_add hnpos]
        _ = x ^ (a - 2) := by ring_nf
    dsimp [H]
    change ((n - 1 : ℕ) : ℝ) ^ a / x - x ^ (a - 1) + a * x ^ (a - 2) =
      x ^ (a - 1) * ((1 - x⁻¹) ^ a - 1 + a * x⁻¹)
    rw [hdivpow, ← hpowinv]
    ring
  exact heq.trans_isLittleO hprod'

private lemma one_sub_inv_rpow_sub_one_isLittleO (a : ℝ) :
    (fun n : ℕ => (1 - (n : ℝ)⁻¹) ^ (a - 1) - 1) =o[atTop]
      (fun _ : ℕ => (1 : ℝ)) := by
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) :=
    tendsto_const_nhds
  have hbase : Tendsto (fun n : ℕ => 1 - (n : ℝ)⁻¹) atTop
      (𝓝 (1 : ℝ)) := by
    simpa using hconst.sub hinv
  have hpow_raw : Tendsto (fun n : ℕ => (1 - (n : ℝ)⁻¹) ^ (a - 1)) atTop
      (𝓝 ((1 : ℝ) ^ (a - 1))) :=
    hbase.rpow tendsto_const_nhds (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
  have hpow : Tendsto (fun n : ℕ => (1 - (n : ℝ)⁻¹) ^ (a - 1)) atTop
      (𝓝 (1 : ℝ)) := by
    simpa using hpow_raw
  have hzero : Tendsto
      (fun n : ℕ => (1 - (n : ℝ)⁻¹) ^ (a - 1) - 1) atTop (𝓝 0) := by
    simpa using hpow.sub hconst
  exact (isLittleO_one_iff ℝ).mpr hzero

private lemma shifted_rpow_div_second (a : ℝ) :
    (fun n : ℕ =>
      ((n - 1 : ℕ) : ℝ) ^ (a - 1) / (n : ℝ) - (n : ℝ) ^ (a - 2))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (a - 2)) := by
  let K : ℕ → ℝ := fun n => (1 - (n : ℝ)⁻¹) ^ (a - 1) - 1
  have hK : K =o[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    simpa [K] using one_sub_inv_rpow_sub_one_isLittleO a
  have hprod :=
    (isBigO_refl (fun n : ℕ => (n : ℝ) ^ (a - 2)) atTop).mul_isLittleO hK
  have hprod' : (fun n : ℕ => (n : ℝ) ^ (a - 2) * K n)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (a - 2)) := by
    refine hprod.congr' (EventuallyEq.refl _ _) ?_
    refine eventually_atTop.mpr ⟨0, fun n _ => ?_⟩
    simp
  have heq : (fun n : ℕ =>
      ((n - 1 : ℕ) : ℝ) ^ (a - 1) / (n : ℝ) - (n : ℝ) ^ (a - 2))
      =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (a - 2) * K n) := by
    refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    let x : ℝ := n
    have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn
    have hnpos : 0 < x := by dsimp [x]; exact_mod_cast hnpos_nat
    have hn1 : (1 : ℝ) ≤ x := by dsimp [x]; exact_mod_cast hn
    have hcast_sub : ((n - 1 : ℕ) : ℝ) = x - 1 := by
      dsimp [x]
      norm_num [Nat.cast_sub hn]
    have hy_nonneg : 0 ≤ 1 - x⁻¹ := by
      have hinv_le : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn1
      linarith
    have hmulbase : x * (1 - x⁻¹) = x - 1 := by
      field_simp [hnpos.ne']
    have hpowsub : ((n - 1 : ℕ) : ℝ) ^ (a - 1) =
        x ^ (a - 1) * (1 - x⁻¹) ^ (a - 1) := by
      rw [hcast_sub, ← hmulbase]
      exact Real.mul_rpow hnpos.le hy_nonneg
    have hdivpow : ((n - 1 : ℕ) : ℝ) ^ (a - 1) / x =
        x ^ (a - 2) * (1 - x⁻¹) ^ (a - 1) := by
      rw [hpowsub]
      have hxpow : x ^ (a - 1) / x = x ^ (a - 2) := by
        calc
          x ^ (a - 1) / x = x ^ (a - 1) * x⁻¹ := by rw [div_eq_mul_inv]
          _ = x ^ (a - 1) * x ^ (-(1 : ℝ)) := by
                rw [Real.rpow_neg hnpos.le, Real.rpow_one]
          _ = x ^ ((a - 1) + (-(1 : ℝ))) := by rw [← Real.rpow_add hnpos]
          _ = x ^ (a - 2) := by ring_nf
      rw [show x ^ (a - 1) * (1 - x⁻¹) ^ (a - 1) / x =
          (x ^ (a - 1) / x) * (1 - x⁻¹) ^ (a - 1) by ring]
      rw [hxpow]
    dsimp [K]
    change ((n - 1 : ℕ) : ℝ) ^ (a - 1) / x - x ^ (a - 2) =
      x ^ (a - 2) * ((1 - x⁻¹) ^ (a - 1) - 1)
    rw [hdivpow]
    ring
  exact heq.trans_isLittleO hprod'

private lemma complex_inv_natCast_isBigO :
    (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : ℂ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards with n
  have htarget : (n : ℝ) ^ (-(1 : ℝ)) = (n : ℝ)⁻¹ := by
    rw [Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_one]
  rw [htarget]
  simp

private lemma rpow_neg_one_mul_eventually (a : ℝ) :
    (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ)) * (n : ℝ) ^ (a - 1)) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (a - 2)) := by
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  calc
    (n : ℝ) ^ (-(1 : ℝ)) * (n : ℝ) ^ (a - 1)
        = (n : ℝ) ^ ((-(1 : ℝ)) + (a - 1)) := by
            rw [← Real.rpow_add hnpos]
    _ = (n : ℝ) ^ (a - 2) := by ring_nf

private lemma coeff_of_scalarDerivSeries_pred
    (p : FormalMultilinearSeries ℂ ℂ ℂ) {n : ℕ} (hn : 1 ≤ n) :
    p.coeff n = (((n : ℝ)⁻¹ : ℝ) : ℂ) * (scalarDerivSeries p).coeff (n - 1) := by
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnpos_nat)
  have hcoeff : (scalarDerivSeries p).coeff (n - 1) = (n : ℂ) * p.coeff n := by
    rw [scalarDerivSeries_coeff]
    have hnat : n - 1 + 1 = n := Nat.sub_add_cancel hn
    have hcast : ((n - 1 : ℕ) : ℂ) + 1 = (n : ℂ) := by
      norm_num [Nat.cast_sub hn]
    rw [hnat, hcast]
  rw [hcoeff]
  have hinv : (((n : ℝ)⁻¹ : ℝ) : ℂ) = (n : ℂ)⁻¹ := by
    norm_num [Complex.ofReal_inv]
  rw [hinv]
  field_simp [hnC]

private lemma secondOrder_of_deriv_secondOrder
    {α : ℝ} {A B : ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hderiv :
      (fun m : ℕ =>
        (scalarDerivSeries p).coeff m -
          (A * (((m : ℝ) ^ α : ℝ) : ℂ) +
            B * (((m : ℝ) ^ (α - 1) : ℝ) : ℂ)))
        =o[atTop] (fun m : ℕ => (m : ℝ) ^ (α - 1))) :
    (fun n : ℕ =>
      p.coeff n -
        (A * (((n : ℝ) ^ (α - 1) : ℝ) : ℂ) +
          (B - (α : ℂ) * A) * (((n : ℝ) ^ (α - 2) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
  let err : ℕ → ℂ := fun m =>
    (scalarDerivSeries p).coeff m -
      (A * (((m : ℝ) ^ α : ℝ) : ℂ) +
        B * (((m : ℝ) ^ (α - 1) : ℝ) : ℂ))
  have herr_sub : (fun n : ℕ => err (n - 1)) =o[atTop]
      (fun n : ℕ => ((n - 1 : ℕ) : ℝ) ^ (α - 1)) := by
    simpa [err, Function.comp_apply] using
      hderiv.comp_tendsto (Filter.tendsto_sub_atTop_nat 1)
  have herr_n : (fun n : ℕ => err (n - 1)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ (α - 1)) :=
    herr_sub.trans_isBigO (nat_sub_const_rpow_isBigO 1 (α - 1))
  have hinv_err_raw :=
    complex_inv_natCast_isBigO.mul_isLittleO herr_n
  have hinv_err : (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : ℂ) * err (n - 1))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
    exact hinv_err_raw.trans_eventuallyEq (rpow_neg_one_mul_eventually α)
  have hAterm : (fun n : ℕ =>
        A * (((((n - 1 : ℕ) : ℝ) ^ α / (n : ℝ) -
            (n : ℝ) ^ (α - 1) + α * (n : ℝ) ^ (α - 2) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) :=
    (ofReal_isLittleO (shifted_rpow_div_first α)).const_mul_left A
  have hBterm : (fun n : ℕ =>
        B * (((((n - 1 : ℕ) : ℝ) ^ (α - 1) / (n : ℝ) -
            (n : ℝ) ^ (α - 2) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) :=
    (ofReal_isLittleO (shifted_rpow_div_second α)).const_mul_left B
  have hsum := (hinv_err.add hAterm).add hBterm
  have heq : (fun n : ℕ =>
      p.coeff n -
        (A * (((n : ℝ) ^ (α - 1) : ℝ) : ℂ) +
          (B - (α : ℂ) * A) * (((n : ℝ) ^ (α - 2) : ℝ) : ℂ))) =ᶠ[atTop]
    (fun n : ℕ =>
      (((n : ℝ)⁻¹ : ℝ) : ℂ) * err (n - 1) +
        A * (((((n - 1 : ℕ) : ℝ) ^ α / (n : ℝ) -
            (n : ℝ) ^ (α - 1) + α * (n : ℝ) ^ (α - 2) : ℝ) : ℂ)) +
        B * (((((n - 1 : ℕ) : ℝ) ^ (α - 1) / (n : ℝ) -
            (n : ℝ) ^ (α - 2) : ℝ) : ℂ))) := by
    refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    have hpcoeff := coeff_of_scalarDerivSeries_pred p hn
    have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn
    have hnR_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnpos_nat)
    have hnat : n - 1 + 1 = n := Nat.sub_add_cancel hn
    have hdiv0 :
        (((n : ℝ)⁻¹ : ℝ) : ℂ) *
          ((((n - 1 : ℕ) : ℝ) ^ α : ℝ) : ℂ) =
            (((((n - 1 : ℕ) : ℝ) ^ α / (n : ℝ) : ℝ) : ℂ)) := by
      rw [← Complex.ofReal_mul]
      congr 1
      field_simp [hnR_ne]
    have hdiv1 :
        (((n : ℝ)⁻¹ : ℝ) : ℂ) *
          ((((n - 1 : ℕ) : ℝ) ^ (α - 1) : ℝ) : ℂ) =
            (((((n - 1 : ℕ) : ℝ) ^ (α - 1) / (n : ℝ) : ℝ) : ℂ)) := by
      rw [← Complex.ofReal_mul]
      congr 1
      field_simp [hnR_ne]
    change p.coeff n -
        (A * (((n : ℝ) ^ (α - 1) : ℝ) : ℂ) +
          (B - (α : ℂ) * A) * (((n : ℝ) ^ (α - 2) : ℝ) : ℂ)) =
      (((n : ℝ)⁻¹ : ℝ) : ℂ) * err (n - 1) +
        A * (((((n - 1 : ℕ) : ℝ) ^ α / (n : ℝ) -
            (n : ℝ) ^ (α - 1) + α * (n : ℝ) ^ (α - 2) : ℝ) : ℂ)) +
        B * (((((n - 1 : ℕ) : ℝ) ^ (α - 1) / (n : ℝ) -
            (n : ℝ) ^ (α - 2) : ℝ) : ℂ))
    rw [hpcoeff]
    dsimp [err]
    have hdiv0A :
        (((n : ℝ)⁻¹ : ℝ) : ℂ) *
          (A * ((((n - 1 : ℕ) : ℝ) ^ α : ℝ) : ℂ)) =
            A * (((((n - 1 : ℕ) : ℝ) ^ α / (n : ℝ) : ℝ) : ℂ)) := by
      calc
        (((n : ℝ)⁻¹ : ℝ) : ℂ) *
            (A * ((((n - 1 : ℕ) : ℝ) ^ α : ℝ) : ℂ))
            = A * ((((n : ℝ)⁻¹ : ℝ) : ℂ) *
                ((((n - 1 : ℕ) : ℝ) ^ α : ℝ) : ℂ)) := by ring
        _ = A * (((((n - 1 : ℕ) : ℝ) ^ α / (n : ℝ) : ℝ) : ℂ)) := by
            rw [hdiv0]
    have hdiv1B :
        (((n : ℝ)⁻¹ : ℝ) : ℂ) *
          (B * ((((n - 1 : ℕ) : ℝ) ^ (α - 1) : ℝ) : ℂ)) =
            B * (((((n - 1 : ℕ) : ℝ) ^ (α - 1) / (n : ℝ) : ℝ) : ℂ)) := by
      calc
        (((n : ℝ)⁻¹ : ℝ) : ℂ) *
            (B * ((((n - 1 : ℕ) : ℝ) ^ (α - 1) : ℝ) : ℂ))
            = B * ((((n : ℝ)⁻¹ : ℝ) : ℂ) *
                ((((n - 1 : ℕ) : ℝ) ^ (α - 1) : ℝ) : ℂ)) := by ring
        _ = B * (((((n - 1 : ℕ) : ℝ) ^ (α - 1) / (n : ℝ) : ℝ) : ℂ)) := by
            rw [hdiv1]
    rw [mul_sub, mul_add, hdiv0A, hdiv1B]
    norm_num [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul]
    ring
  exact heq.trans_isLittleO hsum

/--
Second-order two-term transfer for `0 < α < 1`.

The proof differentiates once, applies `transfer_twoTerm_secondOrder` at
`β = α + 1`, then descends coefficients through the identity
`[z^m] f' = (m + 1)[z^(m+1)]f`.
-/
theorem transfer_twoTerm_secondOrder_alpha_lt_one
    {α : ℝ} {C0 C1 : ℂ} {R φ : ℝ} {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
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
  let g : ℂ → ℂ := fun z => f z - C0 • h0 z - C1 • h1 z
  let R' : ℝ := (1 + R) / 2
  let φ' : ℝ := (φ + Real.pi / 2) / 2
  have hφπ : φ < Real.pi := by linarith [hφ2, Real.pi_pos]
  have hR'1 : 1 < R' := by dsimp [R']; linarith
  have hRR' : R' < R := by dsimp [R']; linarith
  have hφ'0 : 0 < φ' := by dsimp [φ']; linarith [hφ0, Real.pi_pos]
  have hφlt : φ < φ' := by dsimp [φ']; linarith [hφ2]
  have hφ'2 : φ' < Real.pi / 2 := by dsimp [φ']; linarith [hφ2]
  have hφ'π : φ' < Real.pi := by linarith [hφ'2, Real.pi_pos]
  have hsubset : DeltaDomainArg R' φ' ⊆ DeltaDomainArg R φ := by
    intro z hz
    exact ⟨lt_trans hz.1 hRR', hz.2.1, lt_trans hφlt hz.2.2⟩
  have hΔ0 : AnalyticOnNhd ℂ h0 (DeltaDomainArg R φ) := by
    simpa [h0] using
      (analyticOnNhd_one_sub_cpow_deltaDomain
        (α := (α : ℂ)) (R := R) (φ := φ) hφ0 hφπ)
  have hΔ1 : AnalyticOnNhd ℂ h1 (DeltaDomainArg R φ) := by
    simpa [h1] using
      (analyticOnNhd_one_sub_cpow_deltaDomain
        (α := (((α - 1 : ℝ) : ℂ))) (R := R) (φ := φ) hφ0 hφπ)
  have hΔg : AnalyticOnNhd ℂ g (DeltaDomainArg R φ) := by
    simpa [g] using
      (hΔ.sub (hΔ0.const_smul (c := C0))).sub (hΔ1.const_smul (c := C1))
  have hsing_g : Tendsto (fun z : ℂ => ‖g z‖ * ‖(1 : ℂ) - z‖ ^ (α - 1))
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0) := by
    simpa [g, h0, h1, smul_eq_mul] using hsing
  have hderiv_g_o : Tendsto (fun z : ℂ => ‖deriv g z‖ * ‖(1 : ℂ) - z‖ ^ α)
      (𝓝[DeltaDomainArg R' φ'] (1 : ℂ)) (𝓝 0) := by
    have h := iteratedDeriv_littleO_of_delta_littleO
      (R := R) (R' := R') (φ := φ) (φ' := φ') (β := α - 1)
      (f := g) 1 hR'1 hRR' hφ0 hφlt hφ'2 hΔg hsing_g
    simpa [iteratedDeriv_eq_iterate, add_comm, add_left_comm, add_assoc] using h
  have hΔ' : AnalyticOnNhd ℂ f (DeltaDomainArg R' φ') := fun z hz => hΔ z (hsubset hz)
  have hp_deriv : HasFPowerSeriesAt (deriv f) (scalarDerivSeries p) (0 : ℂ) := by
    simpa [scalarIteratedDerivSeries, iteratedDeriv_eq_iterate] using
      hp.scalar_iteratedDeriv 1
  have hΔ_deriv : AnalyticOnNhd ℂ (deriv f) (DeltaDomainArg R' φ') :=
    hΔ'.deriv
  have hderiv_g_eq : ∀ z ∈ DeltaDomainArg R' φ',
      deriv g z =
        deriv f z -
          C0 * ((α : ℂ) * (1 - z) ^ (-(((α + 1 : ℝ) : ℂ)))) -
          C1 * (((α - 1 : ℝ) : ℂ) * (1 - z) ^ (-(α : ℂ))) := by
    intro z hz
    have hz_big : z ∈ DeltaDomainArg R φ := hsubset hz
    have hfz : DifferentiableAt ℂ f z := (hΔ z hz_big).differentiableAt
    have h0z : DifferentiableAt ℂ h0 z := (hΔ0 z hz_big).differentiableAt
    have h1z : DifferentiableAt ℂ h1 z := (hΔ1 z hz_big).differentiableAt
    have hzslit : (1 - z) ∈ Complex.slitPlane :=
      one_sub_mem_slitPlane_of_mem_delta hφ0 hz_big
    dsimp [g]
    change deriv ((f - C0 • h0) - C1 • h1) z =
        deriv f z -
          C0 * ((α : ℂ) * (1 - z) ^ (-(((α + 1 : ℝ) : ℂ)))) -
          C1 * (((α - 1 : ℝ) : ℂ) * (1 - z) ^ (-(α : ℂ)))
    rw [deriv_sub]
    · rw [deriv_sub]
      · rw [deriv_const_smul, deriv_const_smul]
        · rw [show deriv h0 z =
            (α : ℂ) * (1 - z) ^ (-(((α + 1 : ℝ) : ℂ))) by
              simpa [h0] using deriv_one_sub_cpow_neg (a := α) (z := z) hzslit]
          rw [show deriv h1 z =
            ((α - 1 : ℝ) : ℂ) * (1 - z) ^ (-(α : ℂ)) by
              simpa [h1] using deriv_one_sub_cpow_neg_sub_one (α := α) (z := z) hzslit]
          simp [smul_eq_mul]
        · exact h1z
        · exact h0z
      · exact hfz
      · exact h0z.const_smul C0
    · exact hfz.sub (h0z.const_smul C0)
    · exact h1z.const_smul C1
  have hsing_deriv : Tendsto
      (fun z : ℂ =>
        ‖deriv f z - ((α : ℂ) * C0) * (1 - z) ^ (-(((α + 1 : ℝ) : ℂ))) -
            (((α - 1 : ℝ) : ℂ) * C1) * (1 - z) ^ (-(α : ℂ))‖ *
          ‖(1 : ℂ) - z‖ ^ α)
      (𝓝[DeltaDomainArg R' φ'] (1 : ℂ)) (𝓝 0) := by
    refine hderiv_g_o.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [hderiv_g_eq z hz]
    congr 1
    ring_nf
  have hderiv_transfer := transfer_twoTerm_secondOrder
    (α := α + 1) (C0 := (α : ℂ) * C0)
    (C1 := ((α - 1 : ℝ) : ℂ) * C1)
    (R := R') (φ := φ') (f := deriv f) (p := scalarDerivSeries p)
    (by linarith : 1 < α + 1) hR'1 hφ'0 hφ'2 hp_deriv hΔ_deriv
    (by simpa [add_sub_cancel_right] using hsing_deriv)
  have hΓα_ne : Real.Gamma α ≠ 0 := (Real.Gamma_pos_of_pos hα0).ne'
  have hα_ne : α ≠ 0 := ne_of_gt hα0
  have hΓ_succ : Real.Gamma (α + 1) = α * Real.Gamma α :=
    Real.Gamma_add_one hα_ne
  let A : ℂ := C0 * (((1 / Real.Gamma α : ℝ) : ℂ))
  let B : ℂ :=
    C0 * ((((α * (α + 1) / 2 / Real.Gamma α : ℝ)) : ℂ)) +
      C1 * (((((α - 1) / Real.Gamma α : ℝ)) : ℂ))
  have hderiv_AB :
      (fun m : ℕ =>
        (scalarDerivSeries p).coeff m -
          (A * (((m : ℝ) ^ α : ℝ) : ℂ) +
            B * (((m : ℝ) ^ (α - 1) : ℝ) : ℂ)))
        =o[atTop] (fun m : ℕ => (m : ℝ) ^ (α - 1)) := by
    refine hderiv_transfer.congr' ?_ ?_
    · refine Eventually.of_forall fun n => ?_
      dsimp [A, B]
      rw [hΓ_succ]
      norm_num [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div]
      field_simp [hα_ne, hΓα_ne]
      ring_nf
    · refine Eventually.of_forall fun n => ?_
      ring_nf
  have hdesc := secondOrder_of_deriv_secondOrder (α := α) (A := A) (B := B)
    (p := p) hderiv_AB
  have hΓ_sub_ne : α - 1 ≠ 0 := by linarith
  have hΓ_sub : Real.Gamma α = (α - 1) * Real.Gamma (α - 1) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      Real.Gamma_add_one hΓ_sub_ne
  have hΓ_subval_ne : Real.Gamma (α - 1) ≠ 0 := by
    intro hzero
    have : Real.Gamma α = 0 := by rw [hΓ_sub, hzero, mul_zero]
    exact hΓα_ne this
  have hαm1C_ne : (((α - 1 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hΓ_sub_ne
  have hαm1C_ne' : (-1 + (α : ℂ)) ≠ 0 := by
    simpa [sub_eq_add_neg, add_comm] using hαm1C_ne
  exact hdesc.congr_left fun n => by
    dsimp [A, B]
    rw [hΓ_sub]
    norm_num [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div]
    ring_nf
    field_simp [hαm1C_ne']
    ring

end
