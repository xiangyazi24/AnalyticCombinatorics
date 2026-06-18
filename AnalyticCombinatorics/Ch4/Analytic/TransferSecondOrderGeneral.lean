import AnalyticCombinatorics.Ch4.Analytic.TransferSecondOrderAlphaLt1

/-!
# General second-order transfer

This file extends the second-order two-term transfer theorem to real exponents
away from the poles `1, 0, -1, ...`.  The proof follows the k-fold derivative
descent used by the all-real little-o transfer theorem.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics
open scoped Topology BigOperators

noncomputable section

private lemma ofReal_isLittleO {u v : ℕ → ℝ}
    (h : u =o[atTop] v) :
    (fun n : ℕ => ((u n : ℝ) : ℂ)) =o[atTop] v := by
  exact Asymptotics.IsLittleO.of_norm_left (by
    simpa [Complex.norm_real] using h.norm_left)

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

lemma secondOrder_of_deriv_secondOrder
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

def secondOrderShiftCorr (α : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, (α + (j : ℝ))

lemma secondOrderShiftCorr_zero (α : ℝ) :
    secondOrderShiftCorr α 0 = 0 := by
  simp [secondOrderShiftCorr]

lemma secondOrderShiftCorr_succ (α : ℝ) (k : ℕ) :
    secondOrderShiftCorr α (k + 1) =
      secondOrderShiftCorr α k + (α + k) := by
  simp [secondOrderShiftCorr, Finset.sum_range_succ]

lemma secondOrderShiftCorr_eq (α : ℝ) (k : ℕ) :
    secondOrderShiftCorr α k =
      (k : ℝ) * α + (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  induction k with
  | zero =>
      simp [secondOrderShiftCorr]
  | succ k ih =>
      rw [secondOrderShiftCorr_succ, ih]
      norm_num [Nat.cast_add]
      ring

lemma scalarIteratedDerivSeries_succ
    (k : ℕ) (p : FormalMultilinearSeries ℂ ℂ ℂ) :
    scalarIteratedDerivSeries (k + 1) p =
      scalarDerivSeries (scalarIteratedDerivSeries k p) := rfl

theorem secondOrder_of_iteratedDeriv_secondOrder
    (k : ℕ) {α : ℝ} {A B : ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hderiv :
      (fun m : ℕ =>
        (scalarIteratedDerivSeries k p).coeff m -
          (A * (((m : ℝ) ^ (α + (k : ℝ) - 1) : ℝ) : ℂ) +
           B * (((m : ℝ) ^ (α + (k : ℝ) - 2) : ℝ) : ℂ)))
        =o[atTop] (fun m : ℕ => (m : ℝ) ^ (α + (k : ℝ) - 2))) :
    (fun n : ℕ =>
      p.coeff n -
        (A * (((n : ℝ) ^ (α - 1) : ℝ) : ℂ) +
         (B - ((secondOrderShiftCorr α k : ℝ) : ℂ) * A) *
            (((n : ℝ) ^ (α - 2) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
  induction k generalizing p α B with
  | zero =>
      simpa [scalarIteratedDerivSeries, secondOrderShiftCorr] using hderiv
  | succ k ih =>
      let q : FormalMultilinearSeries ℂ ℂ ℂ := scalarIteratedDerivSeries k p
      let a : ℝ := α + k
      have hderiv_q :
          (fun m : ℕ =>
            (scalarDerivSeries q).coeff m -
              (A * (((m : ℝ) ^ a : ℝ) : ℂ) +
               B * (((m : ℝ) ^ (a - 1) : ℝ) : ℂ)))
            =o[atTop] (fun m : ℕ => (m : ℝ) ^ (a - 1)) := by
        refine hderiv.congr' ?_ ?_
        · refine Eventually.of_forall fun m => ?_
          dsimp [q, a]
          rw [scalarIteratedDerivSeries_succ]
          congr 2
          · congr 1
            norm_num [Nat.cast_add]
            ring
          · congr 1
            norm_num [Nat.cast_add]
            ring
        · refine Eventually.of_forall fun m => ?_
          dsimp [a]
          congr 1
          norm_num [Nat.cast_add]
          ring
      have hq := secondOrder_of_deriv_secondOrder
        (α := a) (A := A) (B := B) (p := q) hderiv_q
      let Bq : ℂ := B - (a : ℂ) * A
      have hq' :
          (fun m : ℕ =>
            (scalarIteratedDerivSeries k p).coeff m -
              (A * (((m : ℝ) ^ (α + (k : ℝ) - 1) : ℝ) : ℂ) +
               Bq * (((m : ℝ) ^ (α + (k : ℝ) - 2) : ℝ) : ℂ)))
            =o[atTop] (fun m : ℕ => (m : ℝ) ^ (α + (k : ℝ) - 2)) := by
        simpa [q, a, Bq, add_assoc, add_comm, add_left_comm] using hq
      have hp := ih (α := α) (B := Bq) (p := p) hq'
      refine hp.congr_left ?_
      intro n
      dsimp [Bq, a]
      rw [secondOrderShiftCorr_succ]
      norm_num [Complex.ofReal_add]
      ring_nf
      exact Or.inl trivial

def rising (a : ℝ) (k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k, (a + (j : ℝ))

lemma rising_zero (a : ℝ) : rising a 0 = 1 := by
  simp [rising]

lemma rising_succ (a : ℝ) (k : ℕ) :
    rising a (k + 1) = rising a k * (a + k) := by
  simp [rising, Finset.prod_range_succ]

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

private lemma eventually_one_sub_mem_slitPlane {z : ℂ}
    (hz : (1 - z) ∈ Complex.slitPlane) :
    ∀ᶠ w : ℂ in 𝓝 z, (1 - w) ∈ Complex.slitPlane := by
  have hcont : ContinuousAt (fun w : ℂ => 1 - w) z := by fun_prop
  exact hcont.eventually_mem (Complex.isOpen_slitPlane.mem_nhds hz)

lemma iteratedDeriv_one_sub_cpow_neg (k : ℕ) {a : ℝ} {z : ℂ}
    (hz : (1 - z) ∈ Complex.slitPlane) :
    iteratedDeriv k (fun w : ℂ => (1 - w) ^ (-(a : ℂ))) z =
      (((rising a k : ℝ) : ℂ) *
        (1 - z) ^ (-(((a + (k : ℝ) : ℝ) : ℂ)))) := by
  induction k generalizing z with
  | zero =>
      simp [iteratedDeriv_zero, rising]
  | succ k ih =>
      rw [iteratedDeriv_succ]
      let F : ℂ → ℂ := iteratedDeriv k (fun w : ℂ => (1 - w) ^ (-(a : ℂ)))
      let G : ℂ → ℂ := fun w : ℂ =>
        ((rising a k : ℝ) : ℂ) *
          (1 - w) ^ (-(((a + (k : ℝ) : ℝ) : ℂ)))
      have heq : F =ᶠ[𝓝 z] G := by
        filter_upwards [eventually_one_sub_mem_slitPlane hz] with w hw
        exact ih hw
      have hdiff_base : DifferentiableAt ℂ
          (fun w : ℂ => (1 - w) ^ (-(((a + (k : ℝ) : ℝ) : ℂ)))) z := by
        exact (show DifferentiableAt ℂ (fun w : ℂ => 1 - w) z by fun_prop).cpow_const hz
      calc
        deriv (iteratedDeriv k (fun w : ℂ => (1 - w) ^ (-(a : ℂ)))) z
            = deriv G z := Filter.EventuallyEq.deriv_eq heq
        _ = ((rising a k : ℝ) : ℂ) *
            (((a + (k : ℝ) : ℝ) : ℂ) *
              (1 - z) ^ (-(((a + (k : ℝ) + 1 : ℝ) : ℂ)))) := by
              dsimp [G]
              rw [deriv_const_mul _ hdiff_base]
              rw [deriv_one_sub_cpow_neg (a := a + (k : ℝ)) hz]
        _ = ((rising a (k + 1) : ℝ) : ℂ) *
            (1 - z) ^ (-(((a + ((k + 1 : ℕ) : ℝ) : ℝ) : ℂ))) := by
              rw [rising_succ]
              norm_num [Complex.ofReal_mul, Complex.ofReal_add, Nat.cast_add]
              ring

lemma Real.Gamma_add_nat_rising_of_forall_ne
    {a : ℝ} (k : ℕ)
    (h : ∀ j ∈ Finset.range k, a + (j : ℝ) ≠ 0) :
    Real.Gamma (a + (k : ℝ)) = rising a k * Real.Gamma a := by
  induction k with
  | zero =>
      simp [rising]
  | succ k ih =>
      have hlast : a + (k : ℝ) ≠ 0 := h k (by simp)
      have hprev : ∀ j ∈ Finset.range k, a + (j : ℝ) ≠ 0 := by
        intro j hj
        exact h j (by
          exact Finset.mem_range.mpr
            (Nat.lt_trans (Finset.mem_range.mp hj) (Nat.lt_succ_self k)))
      calc
        Real.Gamma (a + ((k + 1 : ℕ) : ℝ))
            = Real.Gamma ((a + (k : ℝ)) + 1) := by
                congr 1
                norm_num [Nat.cast_add]
                ring
        _ = (a + (k : ℝ)) * Real.Gamma (a + (k : ℝ)) :=
                Real.Gamma_add_one hlast
        _ = (a + (k : ℝ)) * (rising a k * Real.Gamma a) := by
                rw [ih hprev]
        _ = rising a (k + 1) * Real.Gamma a := by
                rw [rising_succ]
                ring

private lemma rising_ne_zero_of_forall_ne {a : ℝ} {k : ℕ}
    (h : ∀ j ∈ Finset.range k, a + (j : ℝ) ≠ 0) :
    rising a k ≠ 0 := by
  unfold rising
  exact Finset.prod_ne_zero_iff.mpr h

private lemma noPole_alpha_add {α : ℝ}
    (hαpole : ∀ m : ℕ, α ≠ 1 - (m : ℝ)) {k : ℕ} :
    ∀ j ∈ Finset.range k, α + (j : ℝ) ≠ 0 := by
  intro j _hj hzero
  have hα : α = 1 - ((j + 1 : ℕ) : ℝ) := by
    have : α = -(j : ℝ) := by linarith
    rw [this]
    norm_num [Nat.cast_add]
  exact hαpole (j + 1) hα

private lemma noPole_alpha_sub_one_add {α : ℝ}
    (hαpole : ∀ m : ℕ, α ≠ 1 - (m : ℝ)) {k : ℕ} :
    ∀ j ∈ Finset.range k, α - 1 + (j : ℝ) ≠ 0 := by
  intro j _hj hzero
  have hα : α = 1 - (j : ℝ) := by linarith
  exact hαpole j hα

private lemma Real.Gamma_ne_zero_of_alpha_pole {α : ℝ}
    (hαpole : ∀ m : ℕ, α ≠ 1 - (m : ℝ)) :
    Real.Gamma α ≠ 0 := by
  exact Real.Gamma_ne_zero (by
    intro m hm
    have hα : α = 1 - ((m + 1 : ℕ) : ℝ) := by
      rw [hm]
      norm_num [Nat.cast_add]
    exact hαpole (m + 1) hα)

private lemma Real.Gamma_ne_zero_of_alpha_sub_one_pole {α : ℝ}
    (hαpole : ∀ m : ℕ, α ≠ 1 - (m : ℝ)) :
    Real.Gamma (α - 1) ≠ 0 := by
  exact Real.Gamma_ne_zero (by
    intro m hm
    have hα : α = 1 - (m : ℝ) := by linarith
    exact hαpole m hα)

lemma rising_div_Gamma_add_eq_inv_Gamma
    {α : ℝ} (k : ℕ)
    (hαpole : ∀ m : ℕ, α ≠ 1 - (m : ℝ)) :
    rising α k / Real.Gamma (α + (k : ℝ)) = 1 / Real.Gamma α := by
  have hprod : rising α k ≠ 0 :=
    rising_ne_zero_of_forall_ne (noPole_alpha_add (α := α) hαpole)
  have hΓ : Real.Gamma α ≠ 0 := Real.Gamma_ne_zero_of_alpha_pole hαpole
  have hrec := Real.Gamma_add_nat_rising_of_forall_ne
    (a := α) k (noPole_alpha_add (α := α) hαpole)
  rw [hrec]
  field_simp [hprod, hΓ]

lemma rising_sub_one_div_Gamma_add_eq_inv_Gamma_sub_one
    {α : ℝ} (k : ℕ)
    (hαpole : ∀ m : ℕ, α ≠ 1 - (m : ℝ)) :
    rising (α - 1) k / Real.Gamma (α - 1 + (k : ℝ)) =
      1 / Real.Gamma (α - 1) := by
  have hprod : rising (α - 1) k ≠ 0 :=
    rising_ne_zero_of_forall_ne (noPole_alpha_sub_one_add (α := α) hαpole)
  have hΓ : Real.Gamma (α - 1) ≠ 0 :=
    Real.Gamma_ne_zero_of_alpha_sub_one_pole hαpole
  have hrec := Real.Gamma_add_nat_rising_of_forall_ne
    (a := α - 1) k (noPole_alpha_sub_one_add (α := α) hαpole)
  rw [hrec]
  field_simp [hprod, hΓ]

theorem transfer_twoTerm_secondOrder_general_of_k
    {α : ℝ} {C0 C1 : ℂ} {R φ : ℝ} {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (k : ℕ)
    (hβ : 1 < α + (k : ℝ))
    (hαpole : ∀ m : ℕ, α ≠ 1 - (m : ℝ))
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
  let β : ℝ := α + (k : ℝ)
  let D0 : ℂ := C0 * (((rising α k : ℝ) : ℂ))
  let D1 : ℂ := C1 * (((rising (α - 1) k : ℝ) : ℂ))
  let A : ℂ := C0 * (((1 / Real.Gamma α : ℝ) : ℂ))
  let B : ℂ :=
    C0 * ((((β * (β - 1) / 2 / Real.Gamma α : ℝ)) : ℂ)) +
      C1 * (((1 / Real.Gamma (α - 1) : ℝ) : ℂ))
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
  have hderiv_g_o : Tendsto (fun z : ℂ =>
      ‖iteratedDeriv k g z‖ * ‖(1 : ℂ) - z‖ ^ (β - 1))
      (𝓝[DeltaDomainArg R' φ'] (1 : ℂ)) (𝓝 0) := by
    have h := iteratedDeriv_littleO_of_delta_littleO
      (R := R) (R' := R') (φ := φ) (φ' := φ') (β := α - 1)
      (f := g) k hR'1 hRR' hφ0 hφlt hφ'2 hΔg hsing_g
    convert h using 1
    ext z
    congr 2
    dsimp [β]
    ring
  have hΔ' : AnalyticOnNhd ℂ f (DeltaDomainArg R' φ') := fun z hz => hΔ z (hsubset hz)
  have hp_iter : HasFPowerSeriesAt (iteratedDeriv k f)
      (scalarIteratedDerivSeries k p) (0 : ℂ) := hp.scalar_iteratedDeriv k
  have hΔ_iter : AnalyticOnNhd ℂ (iteratedDeriv k f) (DeltaDomainArg R' φ') := by
    simpa [iteratedDeriv_eq_iterate] using hΔ'.iterated_deriv k
  have hderiv_g_eq : ∀ z ∈ DeltaDomainArg R' φ',
      iteratedDeriv k g z =
        iteratedDeriv k f z -
          D0 * (1 - z) ^ (-(β : ℂ)) -
          D1 * (1 - z) ^ (-(((β - 1 : ℝ) : ℂ))) := by
    intro z hz
    have hz_big : z ∈ DeltaDomainArg R φ := hsubset hz
    have hzslit : (1 - z) ∈ Complex.slitPlane :=
      one_sub_mem_slitPlane_of_mem_delta hφ0 hz_big
    have hfcont : ContDiffAt ℂ (↑k) f z := (hΔ z hz_big).contDiffAt
    have h0cont : ContDiffAt ℂ (↑k) h0 z := (hΔ0 z hz_big).contDiffAt
    have h1cont : ContDiffAt ℂ (↑k) h1 z := (hΔ1 z hz_big).contDiffAt
    have hC0cont : ContDiffAt ℂ (↑k) (fun y : ℂ => C0 • h0 y) z :=
      h0cont.const_smul C0
    have hC1cont : ContDiffAt ℂ (↑k) (fun y : ℂ => C1 • h1 y) z :=
      h1cont.const_smul C1
    change iteratedDeriv k ((fun y : ℂ => f y - C0 • h0 y) -
          fun y : ℂ => C1 • h1 y) z =
        iteratedDeriv k f z -
          D0 * (1 - z) ^ (-(β : ℂ)) -
          D1 * (1 - z) ^ (-(((β - 1 : ℝ) : ℂ)))
    rw [iteratedDeriv_sub (hfcont.sub hC0cont) hC1cont]
    have hsub0 :
        iteratedDeriv k (fun x : ℂ => f x - C0 • h0 x) z =
          iteratedDeriv k f z - iteratedDeriv k (fun y : ℂ => C0 • h0 y) z := by
      simpa using (iteratedDeriv_sub hfcont hC0cont)
    rw [hsub0]
    have hC0der :
        iteratedDeriv k (fun y : ℂ => C0 • h0 y) z =
          C0 • iteratedDeriv k h0 z := by
      simpa using (iteratedDeriv_const_smul h0cont C0)
    have hC1der :
        iteratedDeriv k (fun y : ℂ => C1 • h1 y) z =
          C1 • iteratedDeriv k h1 z := by
      simpa using (iteratedDeriv_const_smul h1cont C1)
    rw [hC0der, hC1der]
    rw [iteratedDeriv_one_sub_cpow_neg (k := k) (a := α) hzslit]
    rw [iteratedDeriv_one_sub_cpow_neg (k := k) (a := α - 1) hzslit]
    dsimp [h0, h1, D0, D1, β]
    norm_num [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, smul_eq_mul]
    ring_nf
  have hsing_deriv : Tendsto
      (fun z : ℂ =>
        ‖iteratedDeriv k f z - D0 * (1 - z) ^ (-(β : ℂ)) -
            D1 * (1 - z) ^ (-(((β - 1 : ℝ) : ℂ)))‖ *
          ‖(1 : ℂ) - z‖ ^ (β - 1))
      (𝓝[DeltaDomainArg R' φ'] (1 : ℂ)) (𝓝 0) := by
    refine hderiv_g_o.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [hderiv_g_eq z hz]
  have htransfer := transfer_twoTerm_secondOrder
    (α := β) (C0 := D0) (C1 := D1)
    (R := R') (φ := φ') (f := iteratedDeriv k f)
    (p := scalarIteratedDerivSeries k p)
    (by simpa [β] using hβ) hR'1 hφ'0 hφ'2 hp_iter hΔ_iter hsing_deriv
  have hrise0 := rising_div_Gamma_add_eq_inv_Gamma (α := α) k hαpole
  have hrise1 := rising_sub_one_div_Gamma_add_eq_inv_Gamma_sub_one (α := α) k hαpole
  have hrise0' :
      ((rising α k / Real.Gamma (α + (k : ℝ)) : ℝ) : ℂ) =
        ((1 / Real.Gamma α : ℝ) : ℂ) := by
    rw [hrise0]
  have hrise1' :
      ((rising (α - 1) k / Real.Gamma (α + (k : ℝ) - 1) : ℝ) : ℂ) =
        ((1 / Real.Gamma (α - 1) : ℝ) : ℂ) := by
    convert congrArg (fun x : ℝ => ((x : ℝ) : ℂ)) hrise1 using 2
    ring
  have hrise0C :
      (((rising α k : ℝ) : ℂ) / ((Real.Gamma (α + (k : ℝ)) : ℝ) : ℂ)) =
        (((Real.Gamma α : ℝ) : ℂ))⁻¹ := by
    calc
      (((rising α k : ℝ) : ℂ) / ((Real.Gamma (α + (k : ℝ)) : ℝ) : ℂ))
          = ((rising α k / Real.Gamma (α + (k : ℝ)) : ℝ) : ℂ) := by
              rw [Complex.ofReal_div]
      _ = ((1 / Real.Gamma α : ℝ) : ℂ) := hrise0'
      _ = (((Real.Gamma α : ℝ) : ℂ))⁻¹ := by
              rw [Complex.ofReal_div]
              norm_num
  have hrise1C :
      (((rising (α - 1) k : ℝ) : ℂ) /
          ((Real.Gamma (α + (k : ℝ) - 1) : ℝ) : ℂ)) =
        (((Real.Gamma (α - 1) : ℝ) : ℂ))⁻¹ := by
    calc
      (((rising (α - 1) k : ℝ) : ℂ) /
          ((Real.Gamma (α + (k : ℝ) - 1) : ℝ) : ℂ))
          = ((rising (α - 1) k /
              Real.Gamma (α + (k : ℝ) - 1) : ℝ) : ℂ) := by
              rw [Complex.ofReal_div]
      _ = ((1 / Real.Gamma (α - 1) : ℝ) : ℂ) := hrise1'
      _ = (((Real.Gamma (α - 1) : ℝ) : ℂ))⁻¹ := by
              rw [Complex.ofReal_div]
              norm_num
  have hderiv_AB :
      (fun m : ℕ =>
        (scalarIteratedDerivSeries k p).coeff m -
          (A * (((m : ℝ) ^ (α + (k : ℝ) - 1) : ℝ) : ℂ) +
           B * (((m : ℝ) ^ (α + (k : ℝ) - 2) : ℝ) : ℂ)))
        =o[atTop] (fun m : ℕ => (m : ℝ) ^ (α + (k : ℝ) - 2)) := by
    refine htransfer.congr' ?_ ?_
    · refine Eventually.of_forall fun n => ?_
      dsimp [A, B, D0, D1, β]
      norm_num [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_div]
      ring_nf at hrise0C hrise1C ⊢
      rw [hrise0C, hrise1C]
    · refine Eventually.of_forall fun n => ?_
      dsimp [β]
  have hdesc := secondOrder_of_iteratedDeriv_secondOrder
    (k := k) (α := α) (A := A) (B := B) (p := p) hderiv_AB
  refine hdesc.congr_left ?_
  intro n
  dsimp [A, B, β]
  rw [secondOrderShiftCorr_eq]
  norm_num [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_div]
  ring_nf

theorem transfer_twoTerm_secondOrder_general
    {α : ℝ} {C0 C1 : ℂ} {R φ : ℝ} {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hαpole : ∀ m : ℕ, α ≠ 1 - (m : ℝ))
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
  obtain ⟨k, hk⟩ := exists_nat_gt (1 - α)
  exact transfer_twoTerm_secondOrder_general_of_k
    (α := α) (C0 := C0) (C1 := C1) (R := R) (φ := φ)
    (f := f) (p := p) k (by linarith) hαpole hR hφ0 hφ2 hp hΔ hsing

end
