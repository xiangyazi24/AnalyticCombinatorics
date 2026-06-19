import AnalyticCombinatorics.Ch7.SingularityApp.CayleyThirdOrder
import AnalyticCombinatorics.Ch7.SingularityApp.FussCatalan

/-!
# Third-order Fuss-Catalan coefficient asymptotic, fixed general arity

This file proves the relative third-order asymptotic for the closed form

`1 / ((p - 1)n + 1) * binom (pn) n`.

The only analytic input is the third-order Stirling-sequence expansion already
proved in `CayleyThirdOrder`, applied at `n`, `(p - 1)n`, and `pn`.
-/

set_option maxHeartbeats 1600000

open Filter Asymptotics
open scoped Topology

namespace AnalyticCombinatorics.Ch7.SingularityApp.FussCatalanNS

noncomputable section

def fussCatalanGeneralRho (p : ℕ) : ℝ :=
  (((p - 1 : ℕ) : ℝ) ^ (p - 1)) / ((p : ℝ) ^ p)

def fussCatalanGeneralLeadingConstant (p : ℕ) : ℝ :=
  fussCatalanConst p

def fussCatalanGeneralMainTermBase (p n : ℕ) : ℝ :=
  fussCatalanGeneralLeadingConstant p * fussCatalanBase p ^ n *
    ((n : ℝ) ^ (-(3 / 2 : ℝ)))

def fussCatalanGeneralMainTerm (p n : ℕ) : ℝ :=
  (fussCatalanGeneralRho p) ^ (-(n : ℝ)) *
    ((n : ℝ) ^ (-(3 / 2 : ℝ))) *
      fussCatalanGeneralLeadingConstant p

def fussCatalanGeneralStirlingC (p : ℕ) : ℝ :=
  -((1 + (p : ℝ) * ((p - 1 : ℕ) : ℝ)) /
      (12 * (p : ℝ) * ((p - 1 : ℕ) : ℝ)))

def fussCatalanGeneralC1 (p : ℕ) : ℝ :=
  -(((p : ℝ) ^ 2 + 11 * (p : ℝ) + 1) /
      (12 * (p : ℝ) * ((p - 1 : ℕ) : ℝ)))

def fussCatalanGeneralC2 (p : ℕ) : ℝ :=
  let q : ℝ := ((p - 1 : ℕ) : ℝ)
  1 / q ^ 2 - fussCatalanGeneralStirlingC p / q +
    (fussCatalanGeneralStirlingC p) ^ 2 / 2

def fussCatalanGeneralThirdApprox (p n : ℕ) : ℝ :=
  1 + fussCatalanGeneralC1 p * (n : ℝ)⁻¹ +
    fussCatalanGeneralC2 p * ((n : ℝ)⁻¹) ^ 2

def fussCatalanRaneyCoeff (p n : ℕ) : ℝ :=
  (1 / ((((p - 1) * n + 1 : ℕ) : ℝ))) *
    (((Nat.choose (p * n) n : ℕ) : ℝ))

private def stirlingInvRatio (n : ℕ) : ℝ :=
  Real.sqrt Real.pi / Stirling.stirlingSeq n

private def stirlingInvRatioApprox (a n : ℕ) : ℝ :=
  1 - (1 / (12 * (a : ℝ))) * (n : ℝ)⁻¹ +
    (1 / (288 * (a : ℝ) ^ 2)) * ((n : ℝ)⁻¹) ^ 2

private def stirlingLinear (a : ℕ) : ℝ :=
  -(1 / (12 * (a : ℝ)))

private def stirlingQuadratic (a : ℕ) : ℝ :=
  1 / (288 * (a : ℝ) ^ 2)

private def stirlingProductApprox (p n : ℕ) : ℝ :=
  1 + fussCatalanGeneralStirlingC p * (n : ℝ)⁻¹ +
    ((fussCatalanGeneralStirlingC p) ^ 2 / 2) * ((n : ℝ)⁻¹) ^ 2

private def rationalPrefactorApprox (q n : ℕ) : ℝ :=
  1 - (1 / (q : ℝ)) * (n : ℝ)⁻¹ +
    (1 / ((q : ℝ) ^ 2)) * ((n : ℝ)⁻¹) ^ 2

private def rationalPrefactor (q n : ℕ) : ℝ :=
  (((q * n : ℕ) : ℝ)) / (((q * n + 1 : ℕ) : ℝ))

private def poly2 (a b : ℝ) (n : ℕ) : ℝ :=
  1 + a * (n : ℝ)⁻¹ + b * ((n : ℝ)⁻¹) ^ 2

private lemma stirlingSeq_pos_of_pos {n : ℕ} (hn : 0 < n) :
    0 < Stirling.stirlingSeq n := by
  cases n with
  | zero => cases hn
  | succ n => simpa using Stirling.stirlingSeq'_pos n

private lemma inv_nat_cube_isLittleO_inv_sq :
    (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) =o[atTop]
      fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  refine IsLittleO.of_bound ?_
  intro c hc
  have hsmall : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ < c :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (Iio_mem_nhds hc)
  filter_upwards [eventually_ge_atTop 1, hsmall] with n hn hninvc
  have hinv_nonneg : 0 ≤ (n : ℝ)⁻¹ := by positivity
  rw [Real.norm_of_nonneg (pow_nonneg hinv_nonneg 3),
    Real.norm_of_nonneg (pow_nonneg hinv_nonneg 2)]
  calc
    ((n : ℝ)⁻¹) ^ 3 = (n : ℝ)⁻¹ * ((n : ℝ)⁻¹) ^ 2 := by ring
    _ ≤ c * ((n : ℝ)⁻¹) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_of_lt hninvc) (pow_nonneg hinv_nonneg 2)

private lemma inv_nat_four_isLittleO_inv_sq :
    (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4) =o[atTop]
      fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  have hO : (fun n : ℕ => (n : ℝ)⁻¹) =O[atTop] fun _n : ℕ => (1 : ℝ) :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).isBigO_one ℝ
  have h := inv_nat_cube_isLittleO_inv_sq.mul_isBigO hO
  simpa [Pi.mul_apply, mul_assoc] using h.congr_left (fun n => by ring)

private lemma const_mul_inv_sq_isBigO_inv_sq (a : ℕ) (ha : 0 < a) :
    (fun n : ℕ => ((((a * n : ℕ) : ℝ) ^ 2)⁻¹))
      =O[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  refine IsBigO.of_bound ((a : ℝ)⁻¹ ^ 2) ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) hn))
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ ((((a * n : ℕ) : ℝ) ^ 2)⁻¹)),
    Real.norm_of_nonneg (pow_nonneg (by positivity : 0 ≤ (n : ℝ)⁻¹) 2)]
  rw [show ((((a * n : ℕ) : ℝ) ^ 2)⁻¹) =
      ((a : ℝ)⁻¹ ^ 2) * ((n : ℝ)⁻¹) ^ 2 by
    norm_num [Nat.cast_mul]
    field_simp [haR, hnR]]

private lemma stirlingInvRatio_constMul_tendsto_one (a : ℕ) (ha : 0 < a) :
    Tendsto (fun n : ℕ => stirlingInvRatio (a * n)) atTop (𝓝 1) := by
  have hseq :
      Tendsto (fun n : ℕ => Stirling.stirlingSeq (a * n)) atTop
        (𝓝 (Real.sqrt Real.pi)) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_const_mul_atTop a ha)
  have hsqrt : Real.sqrt Real.pi ≠ 0 := by positivity
  have hconst : Tendsto (fun _n : ℕ => Real.sqrt Real.pi) atTop
      (𝓝 (Real.sqrt Real.pi)) := tendsto_const_nhds
  simpa [stirlingInvRatio, div_self hsqrt] using hconst.div hseq hsqrt

private lemma stirlingInvRatioApprox_tendsto_one (a : ℕ) :
    Tendsto (fun n : ℕ => stirlingInvRatioApprox a n) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h2 : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using h1.pow 2
  have hlin := h1.const_mul (-(1 / (12 * (a : ℝ))))
  have hquad := h2.const_mul (1 / (288 * (a : ℝ) ^ 2))
  simpa [stirlingInvRatioApprox, sub_eq_add_neg] using
    (tendsto_const_nhds.add hlin).add hquad

private lemma stirlingInvRatio_constMul_thirdOrder (a : ℕ) (ha : 0 < a) :
    (fun n : ℕ =>
      stirlingInvRatio (a * n) - stirlingInvRatioApprox a n)
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  have hraw :=
    TreeFunctionNS.stirlingSeq_inv_ratio_thirdOrder.comp_tendsto
      (tendsto_const_mul_atTop a ha)
  have htarget := hraw.trans_isBigO (by
    simpa [Function.comp_def] using const_mul_inv_sq_isBigO_inv_sq a ha)
  have hleft :
      (fun n : ℕ =>
        stirlingInvRatio (a * n) - stirlingInvRatioApprox a n)
        =o[atTop] fun n : ℕ => (((n : ℝ) ^ 2)⁻¹) := by
    refine htarget.congr_left ?_
    intro n
    unfold stirlingInvRatio stirlingInvRatioApprox
    unfold TreeFunctionNS.cayleyRelativeSecondConstant
      TreeFunctionNS.cayleyRelativeThirdConstant
    by_cases hn : n = 0
    · subst n
      simp [Stirling.stirlingSeq_zero]
    · have haR : (a : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      norm_num [Nat.cast_mul]
      field_simp [haR, hnR]
      ring_nf
  simpa [inv_pow] using hleft

private lemma poly2_tendsto_one (a b : ℝ) :
    Tendsto (fun n : ℕ => poly2 a b n) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h2 : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using h1.pow 2
  simpa [poly2] using (tendsto_const_nhds.add (h1.const_mul a)).add (h2.const_mul b)

private lemma product_two_sub_product_two_isLittleO
    {f g F G : ℕ → ℝ}
    (hf : (fun n : ℕ => f n - F n) =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2)
    (hg : (fun n : ℕ => g n - G n) =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2)
    (hgO : g =O[atTop] fun _n : ℕ => (1 : ℝ))
    (hFO : F =O[atTop] fun _n : ℕ => (1 : ℝ)) :
    (fun n : ℕ => f n * g n - F n * G n)
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  have h1 := hf.mul_isBigO hgO
  have h2 := hg.mul_isBigO hFO
  have hsum := h1.add h2
  simpa [Pi.mul_apply] using hsum.congr_left (fun n => by ring)

private lemma poly2_mul_trunc_isLittleO (a b c d : ℝ) :
    (fun n : ℕ =>
      poly2 a b n * poly2 c d n - poly2 (a + c) (b + d + a * c) n)
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  have h3 := inv_nat_cube_isLittleO_inv_sq.const_mul_left (a * d + b * c)
  have h4 := inv_nat_four_isLittleO_inv_sq.const_mul_left (b * d)
  have h := h3.add h4
  refine h.congr_left ?_
  intro n
  unfold poly2
  ring

private lemma poly2_div_trunc_residual_isLittleO (A B C D : ℝ) :
    (fun n : ℕ =>
      poly2 A B n - poly2 (A - C) (B - D - C * (A - C)) n * poly2 C D n)
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  let S : ℝ := A - C
  let T : ℝ := B - D - C * (A - C)
  have h3 := inv_nat_cube_isLittleO_inv_sq.const_mul_left (-(S * D + T * C))
  have h4 := inv_nat_four_isLittleO_inv_sq.const_mul_left (-(T * D))
  have h := h3.add h4
  refine h.congr_left ?_
  intro n
  unfold poly2
  simp [S, T]
  ring

private lemma stirlingInvRatioApprox_eq_poly2 (a n : ℕ) :
    stirlingInvRatioApprox a n = poly2 (stirlingLinear a) (stirlingQuadratic a) n := by
  unfold stirlingInvRatioApprox poly2 stirlingLinear stirlingQuadratic
  ring

private lemma stirlingProductApprox_eq_poly2 (p n : ℕ) :
    stirlingProductApprox p n =
      poly2 (fussCatalanGeneralStirlingC p)
        ((fussCatalanGeneralStirlingC p) ^ 2 / 2) n := by
  rfl

private lemma rationalPrefactorApprox_eq_poly2 (q n : ℕ) :
    rationalPrefactorApprox q n =
      poly2 (-(1 / (q : ℝ))) (1 / ((q : ℝ) ^ 2)) n := by
  unfold rationalPrefactorApprox poly2
  ring

private lemma stirlingProductApprox_tendsto_one (p : ℕ) :
    Tendsto (fun n : ℕ => stirlingProductApprox p n) atTop (𝓝 1) := by
  simpa [stirlingProductApprox_eq_poly2] using
    poly2_tendsto_one (fussCatalanGeneralStirlingC p)
      ((fussCatalanGeneralStirlingC p) ^ 2 / 2)

private lemma stirlingProduct_linear_eq (p : ℕ) (hp : 2 ≤ p) :
    (stirlingLinear 1 + stirlingLinear (p - 1)) - stirlingLinear p =
      fussCatalanGeneralStirlingC p := by
  have hpR : (p : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hp))
  have hqR : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
    have hq : 0 < p - 1 := by omega
    exact_mod_cast Nat.ne_of_gt hq
  have hqcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
  unfold stirlingLinear fussCatalanGeneralStirlingC
  field_simp [hpR, hqR]
  rw [hqcast]
  ring

private lemma stirlingProduct_quadratic_eq (p : ℕ) (hp : 2 ≤ p) :
    (stirlingQuadratic 1 + stirlingQuadratic (p - 1) +
        stirlingLinear 1 * stirlingLinear (p - 1)) -
        stirlingQuadratic p -
        stirlingLinear p *
          ((stirlingLinear 1 + stirlingLinear (p - 1)) - stirlingLinear p) =
      (fussCatalanGeneralStirlingC p) ^ 2 / 2 := by
  have hpR : (p : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hp))
  have hqR : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
    have hq : 0 < p - 1 := by omega
    exact_mod_cast Nat.ne_of_gt hq
  have hqcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
  unfold stirlingLinear stirlingQuadratic fussCatalanGeneralStirlingC
  field_simp [hpR, hqR]
  rw [hqcast]
  ring

private lemma stirlingProduct_quadratic_eq_stirlingC (p : ℕ) (hp : 2 ≤ p) :
    (stirlingQuadratic 1 + stirlingQuadratic (p - 1) +
        stirlingLinear 1 * stirlingLinear (p - 1)) -
        stirlingQuadratic p -
        stirlingLinear p * fussCatalanGeneralStirlingC p =
      (fussCatalanGeneralStirlingC p) ^ 2 / 2 := by
  calc
    (stirlingQuadratic 1 + stirlingQuadratic (p - 1) +
        stirlingLinear 1 * stirlingLinear (p - 1)) -
        stirlingQuadratic p -
        stirlingLinear p * fussCatalanGeneralStirlingC p =
      (stirlingQuadratic 1 + stirlingQuadratic (p - 1) +
        stirlingLinear 1 * stirlingLinear (p - 1)) -
        stirlingQuadratic p -
        stirlingLinear p *
          ((stirlingLinear 1 + stirlingLinear (p - 1)) - stirlingLinear p) := by
          rw [stirlingProduct_linear_eq p hp]
    _ = (fussCatalanGeneralStirlingC p) ^ 2 / 2 :=
      stirlingProduct_quadratic_eq p hp

private lemma stirlingInvProduct_thirdOrder (p : ℕ) (hp : 2 ≤ p) :
    (fun n : ℕ =>
      stirlingInvRatio n * stirlingInvRatio ((p - 1) * n) /
          stirlingInvRatio (p * n) -
        stirlingProductApprox p n)
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num : 0 < 2) hp
  have hq0 : 0 < p - 1 := by omega
  have hA1 :
      (fun n : ℕ =>
        stirlingInvRatio n - poly2 (stirlingLinear 1) (stirlingQuadratic 1) n)
        =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
    simpa [stirlingInvRatioApprox_eq_poly2] using
      stirlingInvRatio_constMul_thirdOrder 1 (by norm_num)
  have hAq :
      (fun n : ℕ =>
        stirlingInvRatio ((p - 1) * n) -
          poly2 (stirlingLinear (p - 1)) (stirlingQuadratic (p - 1)) n)
        =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
    simpa [stirlingInvRatioApprox_eq_poly2] using
      stirlingInvRatio_constMul_thirdOrder (p - 1) hq0
  have hAp :
      (fun n : ℕ =>
        stirlingInvRatio (p * n) - poly2 (stirlingLinear p) (stirlingQuadratic p) n)
        =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
    simpa [stirlingInvRatioApprox_eq_poly2] using
      stirlingInvRatio_constMul_thirdOrder p hp0
  have hAqO :
      (fun n : ℕ => stirlingInvRatio ((p - 1) * n))
        =O[atTop] fun _n : ℕ => (1 : ℝ) :=
    (stirlingInvRatio_constMul_tendsto_one (p - 1) hq0).isBigO_one ℝ
  have hP1O :
      (fun n : ℕ => poly2 (stirlingLinear 1) (stirlingQuadratic 1) n)
        =O[atTop] fun _n : ℕ => (1 : ℝ) :=
    (poly2_tendsto_one (stirlingLinear 1) (stirlingQuadratic 1)).isBigO_one ℝ
  have hprod :=
    product_two_sub_product_two_isLittleO hA1 hAq hAqO hP1O
  let A : ℝ := stirlingLinear 1 + stirlingLinear (p - 1)
  let B : ℝ := stirlingQuadratic 1 + stirlingQuadratic (p - 1) +
    stirlingLinear 1 * stirlingLinear (p - 1)
  let C : ℝ := stirlingLinear p
  let D : ℝ := stirlingQuadratic p
  have hpolyProd :
      (fun n : ℕ =>
        poly2 (stirlingLinear 1) (stirlingQuadratic 1) n *
            poly2 (stirlingLinear (p - 1)) (stirlingQuadratic (p - 1)) n -
          poly2 A B n)
        =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
    simpa [A, B] using
      poly2_mul_trunc_isLittleO (stirlingLinear 1) (stirlingQuadratic 1)
        (stirlingLinear (p - 1)) (stirlingQuadratic (p - 1))
  have hpolyDiv :
      (fun n : ℕ =>
        poly2 A B n -
          stirlingProductApprox p n * poly2 (stirlingLinear p) (stirlingQuadratic p) n)
        =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
    have hraw := poly2_div_trunc_residual_isLittleO A B C D
    simpa [A, B, C, D, stirlingProductApprox_eq_poly2,
      stirlingProduct_linear_eq p hp, stirlingProduct_quadratic_eq_stirlingC p hp] using hraw
  have hpoly := hpolyProd.add hpolyDiv
  have hpoly' :
      (fun n : ℕ =>
        poly2 (stirlingLinear 1) (stirlingQuadratic 1) n *
            poly2 (stirlingLinear (p - 1)) (stirlingQuadratic (p - 1)) n -
          stirlingProductApprox p n *
            poly2 (stirlingLinear p) (stirlingQuadratic p) n)
        =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
    refine hpoly.congr_left ?_
    intro n
    ring
  have hnumToApprox := hprod.add hpoly'
  have hnumToApprox' :
      (fun n : ℕ =>
        stirlingInvRatio n * stirlingInvRatio ((p - 1) * n) -
          stirlingProductApprox p n *
            poly2 (stirlingLinear p) (stirlingQuadratic p) n)
        =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
    refine hnumToApprox.congr_left ?_
    intro n
    ring
  have hSPO :
      (fun n : ℕ => stirlingProductApprox p n)
        =O[atTop] fun _n : ℕ => (1 : ℝ) :=
    (stirlingProductApprox_tendsto_one p).isBigO_one ℝ
  have hdenErr0 := hAp.mul_isBigO hSPO
  have hdenErr :
      (fun n : ℕ =>
        stirlingProductApprox p n * stirlingInvRatio (p * n) -
          stirlingProductApprox p n *
            poly2 (stirlingLinear p) (stirlingQuadratic p) n)
        =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
    simpa [Pi.mul_apply] using hdenErr0.congr_left (fun n => by ring)
  have hnum0 := hnumToApprox'.sub hdenErr
  have hnum :
      (fun n : ℕ =>
        stirlingInvRatio n * stirlingInvRatio ((p - 1) * n) -
          stirlingProductApprox p n * stirlingInvRatio (p * n))
        =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
    refine hnum0.congr_left ?_
    intro n
    ring
  have hdenInvO :
      (fun n : ℕ => (stirlingInvRatio (p * n))⁻¹)
        =O[atTop] fun _n : ℕ => (1 : ℝ) :=
    ((stirlingInvRatio_constMul_tendsto_one p hp0).inv₀ one_ne_zero).isBigO_one ℝ
  have hdiv0 := hnum.mul_isBigO hdenInvO
  refine hdiv0.congr' ?_ (Eventually.of_forall fun n => by ring)
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hpnpos : 0 < p * n := Nat.mul_pos hp0 hn
  have hden : stirlingInvRatio (p * n) ≠ 0 := by
    unfold stirlingInvRatio
    exact div_ne_zero (by positivity) (stirlingSeq_pos_of_pos hpnpos).ne'
  field_simp [hden]

private lemma rationalPrefactorApprox_tendsto_one (q : ℕ) :
    Tendsto (fun n : ℕ => rationalPrefactorApprox q n) atTop (𝓝 1) := by
  simpa [rationalPrefactorApprox_eq_poly2] using
    poly2_tendsto_one (-(1 / (q : ℝ))) (((q : ℝ) ^ 2)⁻¹)

private lemma rationalPrefactor_thirdOrder (q : ℕ) (hq : 0 < q) :
    (fun n : ℕ => rationalPrefactor q n - rationalPrefactorApprox q n)
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  have hnat : Tendsto (fun n : ℕ => q * n + 1) atTop atTop := by
    simpa [Function.comp_def] using
      (tendsto_add_atTop_nat 1).comp (tendsto_const_mul_atTop q hq)
  have hinv_tend :
      Tendsto (fun n : ℕ => (((q * n + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hnat
  have hinvLittle :
      (fun n : ℕ => (((q * n + 1 : ℕ) : ℝ)⁻¹))
        =o[atTop] fun _n : ℕ => (1 : ℝ) :=
    (isLittleO_one_iff ℝ).mpr hinv_tend
  have hx2O :
      (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2)
        =O[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 :=
    isBigO_refl _ _
  have hprod := hinvLittle.mul_isBigO hx2O
  have hscaled := hprod.const_mul_left (-(1 / ((q : ℝ) ^ 2)))
  refine hscaled.congr' ?_ (Eventually.of_forall fun n => by ring)
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hden : (((q * n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  unfold rationalPrefactor rationalPrefactorApprox
  norm_num [Nat.cast_mul, Nat.cast_add]
  field_simp [hqR, hnR, hden]
  ring

private lemma stirlingInvProduct_tendsto_one (p : ℕ) (hp : 2 ≤ p) :
    Tendsto
      (fun n : ℕ =>
        stirlingInvRatio n * stirlingInvRatio ((p - 1) * n) /
          stirlingInvRatio (p * n))
      atTop (𝓝 1) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num : 0 < 2) hp
  have hq0 : 0 < p - 1 := by omega
  have h1 : Tendsto (fun n : ℕ => stirlingInvRatio n) atTop (𝓝 1) := by
    simpa using stirlingInvRatio_constMul_tendsto_one 1 (by norm_num)
  have hq := stirlingInvRatio_constMul_tendsto_one (p - 1) hq0
  have hp' := stirlingInvRatio_constMul_tendsto_one p hp0
  simpa using (h1.mul hq).div hp' one_ne_zero

private lemma fussCatalanGeneralC1_eq (p : ℕ) (hp : 2 ≤ p) :
    fussCatalanGeneralC1 p =
      -(1 / ((p - 1 : ℕ) : ℝ)) + fussCatalanGeneralStirlingC p := by
  have hpR : (p : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hp))
  have hqR : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
    have hq : 0 < p - 1 := by omega
    exact_mod_cast Nat.ne_of_gt hq
  have hqcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
  unfold fussCatalanGeneralC1 fussCatalanGeneralStirlingC
  field_simp [hpR, hqR]
  rw [hqcast]
  ring

private lemma fussCatalanGeneralC2_eq (p : ℕ) :
    fussCatalanGeneralC2 p =
      1 / (((p - 1 : ℕ) : ℝ) ^ 2) +
        (fussCatalanGeneralStirlingC p) ^ 2 / 2 +
          (-(1 / ((p - 1 : ℕ) : ℝ))) * fussCatalanGeneralStirlingC p := by
  unfold fussCatalanGeneralC2
  ring

private lemma fussCatalanRelativeCore_thirdOrder (p : ℕ) (hp : 2 ≤ p) :
    (fun n : ℕ =>
      rationalPrefactor (p - 1) n *
          (stirlingInvRatio n * stirlingInvRatio ((p - 1) * n) /
            stirlingInvRatio (p * n)) -
        fussCatalanGeneralThirdApprox p n)
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  have hq0 : 0 < p - 1 := by omega
  have hrat := rationalPrefactor_thirdOrder (p - 1) hq0
  have hstir := stirlingInvProduct_thirdOrder p hp
  have hstirO :
      (fun n : ℕ =>
        stirlingInvRatio n * stirlingInvRatio ((p - 1) * n) /
          stirlingInvRatio (p * n))
        =O[atTop] fun _n : ℕ => (1 : ℝ) :=
    (stirlingInvProduct_tendsto_one p hp).isBigO_one ℝ
  have hratApproxO :
      (fun n : ℕ => rationalPrefactorApprox (p - 1) n)
        =O[atTop] fun _n : ℕ => (1 : ℝ) :=
    (rationalPrefactorApprox_tendsto_one (p - 1)).isBigO_one ℝ
  have hprod :=
    product_two_sub_product_two_isLittleO hrat hstir hstirO hratApproxO
  have hpolyRaw :=
    poly2_mul_trunc_isLittleO
      (-(1 / ((p - 1 : ℕ) : ℝ)))
      (1 / (((p - 1 : ℕ) : ℝ) ^ 2))
      (fussCatalanGeneralStirlingC p)
      ((fussCatalanGeneralStirlingC p) ^ 2 / 2)
  have hpoly :
      (fun n : ℕ =>
        rationalPrefactorApprox (p - 1) n * stirlingProductApprox p n -
          fussCatalanGeneralThirdApprox p n)
        =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
    refine hpolyRaw.congr_left ?_
    intro n
    unfold rationalPrefactorApprox stirlingProductApprox fussCatalanGeneralThirdApprox poly2
    rw [fussCatalanGeneralC1_eq p hp, fussCatalanGeneralC2_eq p]
    ring
  have htotal := hprod.add hpoly
  refine htotal.congr_left ?_
  intro n
  ring

private lemma factorial_eq_stirlingScale_div_invRatio {m : ℕ} (hm : m ≠ 0) :
    (((m.factorial : ℕ) : ℝ)) = stirlingScale m / stirlingInvRatio m := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hsqrtπ : Real.sqrt Real.pi ≠ 0 := by positivity
  have hsqrt2m : Real.sqrt (2 * (m : ℝ)) ≠ 0 := by positivity
  have hpow : ((m : ℝ) / Real.exp 1) ^ m ≠ 0 := by
    exact pow_ne_zero _ (div_ne_zero hmR (Real.exp_ne_zero 1))
  have hsqrt_split :
      Real.sqrt (2 * (m : ℝ) * Real.pi) =
        Real.sqrt (2 * (m : ℝ)) * Real.sqrt Real.pi := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * (m : ℝ))]
  unfold stirlingScale stirlingInvRatio Stirling.stirlingSeq
  rw [hsqrt_split]
  field_simp [hmR, hsqrtπ, hsqrt2m, hpow]

private lemma stirlingInvRatio_ne_zero_of_pos {m : ℕ} (hm : 0 < m) :
    stirlingInvRatio m ≠ 0 := by
  unfold stirlingInvRatio
  exact div_ne_zero (by positivity) (stirlingSeq_pos_of_pos hm).ne'

private lemma stirlingScale_ne_zero_of_pos {m : ℕ} (hm : 0 < m) :
    stirlingScale m ≠ 0 := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  unfold stirlingScale
  exact mul_ne_zero (by positivity) (pow_ne_zero _ (div_ne_zero hmR.ne' (Real.exp_ne_zero 1)))

private lemma factorial_ratio_eq_chooseScale_mul_invRatios
    (q n : ℕ) (hq : 1 ≤ q) (hn : n ≠ 0) :
    (((((q + 1) * n).factorial : ℕ) : ℝ) /
        ((((n.factorial : ℕ) : ℝ) * ((((q * n).factorial : ℕ) : ℝ))))) =
      fussCatalanChooseScale (q + 1) n *
        (stirlingInvRatio n * stirlingInvRatio (q * n) /
          stirlingInvRatio ((q + 1) * n)) := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num : 0 < 1) hq
  have hqnpos : 0 < q * n := Nat.mul_pos hqpos hnpos
  have hpnpos : 0 < (q + 1) * n := Nat.mul_pos (Nat.succ_pos q) hnpos
  have hAn : stirlingInvRatio n ≠ 0 := stirlingInvRatio_ne_zero_of_pos hnpos
  have hAq : stirlingInvRatio (q * n) ≠ 0 := stirlingInvRatio_ne_zero_of_pos hqnpos
  have hAp : stirlingInvRatio ((q + 1) * n) ≠ 0 :=
    stirlingInvRatio_ne_zero_of_pos hpnpos
  have hSn : stirlingScale n ≠ 0 := stirlingScale_ne_zero_of_pos hnpos
  have hSq : stirlingScale (q * n) ≠ 0 := stirlingScale_ne_zero_of_pos hqnpos
  have hSp : stirlingScale ((q + 1) * n) ≠ 0 := stirlingScale_ne_zero_of_pos hpnpos
  rw [factorial_eq_stirlingScale_div_invRatio (m := (q + 1) * n)
        (Nat.ne_of_gt hpnpos),
    factorial_eq_stirlingScale_div_invRatio (m := n) hn,
    factorial_eq_stirlingScale_div_invRatio (m := q * n) (Nat.ne_of_gt hqnpos)]
  rw [show
      (stirlingScale ((q + 1) * n) / stirlingInvRatio ((q + 1) * n)) /
          ((stirlingScale n / stirlingInvRatio n) *
            (stirlingScale (q * n) / stirlingInvRatio (q * n))) =
        (stirlingScale ((q + 1) * n) / (stirlingScale n * stirlingScale (q * n))) *
          (stirlingInvRatio n * stirlingInvRatio (q * n) /
            stirlingInvRatio ((q + 1) * n)) by
        field_simp [hAn, hAq, hAp, hSn, hSq, hSp]
        ]
  rw [stirling_choose_scale_succ_eq q n hq hn]

private lemma fussCatalanChooseScale_ne_zero_succ
    (q n : ℕ) (hq : 1 ≤ q) (hn : n ≠ 0) :
    fussCatalanChooseScale (q + 1) n ≠ 0 := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  unfold fussCatalanChooseScale fussCatalanBase
  simp only [Nat.add_sub_cancel]
  positivity

private lemma fussCatalan_succ_ratio_eq_core
    (q n : ℕ) (hq : 1 ≤ q) (hn : n ≠ 0) :
    (fussCatalan (q + 1) n : ℝ) / fussCatalanGeneralMainTermBase (q + 1) n =
      rationalPrefactor q n *
        (stirlingInvRatio n * stirlingInvRatio (q * n) /
          stirlingInvRatio ((q + 1) * n)) := by
  have hp : 2 ≤ q + 1 := by omega
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num : 0 < 1) hq
  have hqnpos : 0 < q * n := Nat.mul_pos hqpos hnpos
  have hpnpos : 0 < (q + 1) * n := Nat.mul_pos (Nat.succ_pos q) hnpos
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hqpos
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hqn1 : (((q * n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hscale : fussCatalanChooseScale (q + 1) n ≠ 0 :=
    fussCatalanChooseScale_ne_zero_succ q n hq hn
  have hAp : stirlingInvRatio ((q + 1) * n) ≠ 0 :=
    stirlingInvRatio_ne_zero_of_pos hpnpos
  have hmain :
      fussCatalanGeneralMainTermBase (q + 1) n =
        fussCatalanChooseScale (q + 1) n / ((q : ℝ) * (n : ℝ)) := by
    symm
    simpa [fussCatalanGeneralMainTermBase, fussCatalanGeneralLeadingConstant] using
      fussCatalan_scale_succ_simplified q n hq hn
  rw [fussCatalan_cast (q + 1) n hp, choose_succ_mul_cast q n,
    factorial_ratio_eq_chooseScale_mul_invRatios q n hq hn, hmain]
  unfold rationalPrefactor
  norm_num [Nat.cast_mul, Nat.cast_add]
  field_simp [hqR, hnR, hqn1, hscale, hAp]

private theorem fussCatalanGeneral_relative_thirdOrder_base (p : ℕ) (hp : 2 ≤ p) :
    (fun n : ℕ =>
      (fussCatalan p n : ℝ) / fussCatalanGeneralMainTermBase p n -
        fussCatalanGeneralThirdApprox p n)
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  have hcore := fussCatalanRelativeCore_thirdOrder p hp
  refine hcore.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hq : 1 ≤ p - 1 := by omega
  have hpq : p - 1 + 1 = p := by omega
  have hbridge := fussCatalan_succ_ratio_eq_core (p - 1) n hq (Nat.ne_of_gt hn)
  simpa [hpq] using
    (congrArg (fun x : ℝ => x - fussCatalanGeneralThirdApprox p n) hbridge).symm

private lemma fussCatalanGeneral_rho_inv_eq_base (p : ℕ) (hp : 2 ≤ p) :
    (fussCatalanGeneralRho p)⁻¹ = fussCatalanBase p := by
  have hpR : (p : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hp))
  have hqR : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
    have hq : 0 < p - 1 := by omega
    exact_mod_cast Nat.ne_of_gt hq
  have hpPow : (p : ℝ) ^ p ≠ 0 := pow_ne_zero _ hpR
  have hqPow : ((p - 1 : ℕ) : ℝ) ^ (p - 1) ≠ 0 := pow_ne_zero _ hqR
  unfold fussCatalanGeneralRho fussCatalanBase
  field_simp [hpPow, hqPow]

private lemma fussCatalanGeneral_rho_rpow_neg_nat_eq_base_pow
    (p n : ℕ) (hp : 2 ≤ p) :
    (fussCatalanGeneralRho p) ^ (-(n : ℝ)) = fussCatalanBase p ^ n := by
  have hρpos : 0 < fussCatalanGeneralRho p := by
    have hpR : 0 < (p : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hp)
    have hqR : 0 < ((p - 1 : ℕ) : ℝ) := by
      have hq : 0 < p - 1 := by omega
      exact_mod_cast hq
    unfold fussCatalanGeneralRho
    positivity
  rw [Real.rpow_neg hρpos.le, Real.rpow_natCast, ← inv_pow,
    fussCatalanGeneral_rho_inv_eq_base p hp]

private lemma fussCatalanGeneralMainTerm_eq_base (p n : ℕ) (hp : 2 ≤ p) :
    fussCatalanGeneralMainTerm p n = fussCatalanGeneralMainTermBase p n := by
  unfold fussCatalanGeneralMainTerm fussCatalanGeneralMainTermBase
  rw [fussCatalanGeneral_rho_rpow_neg_nat_eq_base_pow p n hp]
  ring

private theorem fussCatalanGeneral_relative_thirdOrder_fussCatalan (p : ℕ) (hp : 2 ≤ p) :
    (fun n : ℕ =>
      (fussCatalan p n : ℝ) / fussCatalanGeneralMainTerm p n -
        fussCatalanGeneralThirdApprox p n)
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  refine (fussCatalanGeneral_relative_thirdOrder_base p hp).congr' ?_
    (EventuallyEq.refl _ _)
  filter_upwards with n
  rw [fussCatalanGeneralMainTerm_eq_base p n hp]

private lemma fussCatalanRaneyCoeff_eq_fussCatalan
    (p n : ℕ) (hp : 2 ≤ p) :
    fussCatalanRaneyCoeff p n = (fussCatalan p n : ℝ) := by
  have hden : ((((p - 1) * n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [fussCatalan_cast p n hp]
  unfold fussCatalanRaneyCoeff
  field_simp [hden]

theorem fussCatalanGeneral_relative_thirdOrder (p : ℕ) (hp : 2 ≤ p) :
    (fun n : ℕ =>
      fussCatalanRaneyCoeff p n / fussCatalanGeneralMainTerm p n -
        fussCatalanGeneralThirdApprox p n)
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  refine (fussCatalanGeneral_relative_thirdOrder_fussCatalan p hp).congr' ?_
    (EventuallyEq.refl _ _)
  filter_upwards with n
  rw [fussCatalanRaneyCoeff_eq_fussCatalan p n hp]

end

end AnalyticCombinatorics.Ch7.SingularityApp.FussCatalanNS
