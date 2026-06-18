import AnalyticCombinatorics.Ch4.Analytic.ModelCoeffSecondOrder
import AnalyticCombinatorics.Ch7.SingularityApp.FussCatalan
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Second-order ternary-tree asymptotics

This file records the second-order constants for the Fuss-Catalan `p = 3`
ternary-tree numbers.  The correction is computed from the three positive
Gamma ratios obtained from the exact Fuss-Catalan closed form.
-/

open Filter Asymptotics
open scoped Topology BigOperators

noncomputable section

def ternaryTransferAlpha : ℝ :=
  -(1 / 2)

def ternaryAsymptoticConstant : ℝ :=
  Real.sqrt 3 / (4 * Real.sqrt Real.pi)

def ternaryRelativeSecondConstant : ℝ :=
  -(43 / 72 : ℝ)

def ternarySecondAsymptoticConstant : ℝ :=
  ternaryAsymptoticConstant * ternaryRelativeSecondConstant

def ternaryGammaRatio (α : ℝ) (n : ℕ) : ℝ :=
  Real.Gamma ((n : ℝ) + α) / Real.Gamma ((n : ℝ) + 1)

def ternaryGammaPrefactor (n : ℕ) : ℝ :=
  (3 : ℝ) ^ (3 * n) * (2 : ℝ) ^ (-(2 * (n : ℝ) + 1)) *
    Real.sqrt Real.pi / (Real.Gamma (1 / 3 : ℝ) * Real.Gamma (2 / 3 : ℝ))

def gammaRatioSecondCoeff (α : ℝ) : ℝ :=
  α * (α - 1) / 2

def gammaRatioNormalizedError (α : ℝ) (n : ℕ) : ℝ :=
  ternaryGammaRatio α n / ((n : ℝ) ^ (α - 1)) -
    (1 + gammaRatioSecondCoeff α * (n : ℝ)⁻¹)

def gammaRatioNormalizedFactor (α : ℝ) (n : ℕ) : ℝ :=
  1 + gammaRatioSecondCoeff α * (n : ℝ)⁻¹ + gammaRatioNormalizedError α n

def ternaryGammaNormalizedProduct (n : ℕ) : ℝ :=
  gammaRatioNormalizedFactor (1 / 3 : ℝ) n *
    gammaRatioNormalizedFactor (2 / 3 : ℝ) n /
    gammaRatioNormalizedFactor (3 / 2 : ℝ) n

lemma gammaRatioNormalizedFactor_eq (α : ℝ) (n : ℕ) :
    gammaRatioNormalizedFactor α n =
      ternaryGammaRatio α n / ((n : ℝ) ^ (α - 1)) := by
  unfold gammaRatioNormalizedFactor gammaRatioNormalizedError
  ring

lemma ternary_gamma_ratio_correction :
    gammaRatioSecondCoeff (1 / 3 : ℝ) +
      gammaRatioSecondCoeff (2 / 3 : ℝ) -
      gammaRatioSecondCoeff (3 / 2 : ℝ) =
    ternaryRelativeSecondConstant := by
  unfold gammaRatioSecondCoeff ternaryRelativeSecondConstant
  norm_num

lemma ternarySecondAsymptoticConstant_closed :
    ternarySecondAsymptoticConstant =
      -(43 * Real.sqrt 3 / (288 * Real.sqrt Real.pi)) := by
  unfold ternarySecondAsymptoticConstant ternaryAsymptoticConstant
    ternaryRelativeSecondConstant
  ring

lemma gamma_one_third_mul_two_thirds :
    Real.Gamma (1 / 3 : ℝ) * Real.Gamma (2 / 3 : ℝ) =
      2 * Real.pi / Real.sqrt 3 := by
  have h := Real.Gamma_mul_Gamma_one_sub (1 / 3 : ℝ)
  rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num] at h
  rw [h, show Real.pi * (1 / 3 : ℝ) = Real.pi / 3 by ring,
    Real.sin_pi_div_three]
  field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3)]

private lemma gamma_three_step (x : ℝ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0)
    (hx2 : x + 2 ≠ 0) :
    Real.Gamma (x + 3) = (x + 2) * (x + 1) * x * Real.Gamma x := by
  calc
    Real.Gamma (x + 3) = Real.Gamma ((x + 2) + 1) := by ring_nf
    _ = (x + 2) * Real.Gamma (x + 2) := Real.Gamma_add_one hx2
    _ = (x + 2) * ((x + 1) * Real.Gamma (x + 1)) := by
      rw [show x + 2 = (x + 1) + 1 by ring, Real.Gamma_add_one hx1]
    _ = (x + 2) * ((x + 1) * (x * Real.Gamma x)) := by
      rw [show x + 1 = x + 1 by rfl, Real.Gamma_add_one hx]
    _ = (x + 2) * (x + 1) * x * Real.Gamma x := by ring

lemma gamma_three_mul_nat_add_one (n : ℕ) :
    Real.Gamma ((3 * n : ℕ) + 1 : ℝ) =
      (3 : ℝ) ^ (3 * n) *
        Real.Gamma ((n : ℝ) + 1 / 3) *
        Real.Gamma ((n : ℝ) + 2 / 3) *
        Real.Gamma ((n : ℝ) + 1) /
        (Real.Gamma (1 / 3 : ℝ) * Real.Gamma (2 / 3 : ℝ)) := by
  induction n with
  | zero =>
      have hΓ13 : Real.Gamma (1 / 3 : ℝ) ≠ 0 :=
        (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 3)).ne'
      have hΓ23 : Real.Gamma (2 / 3 : ℝ) ≠ 0 :=
        (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 2 / 3)).ne'
      field_simp [Real.Gamma_one, hΓ13, hΓ23]
      norm_num
  | succ n ih =>
      have hΓ13 : Real.Gamma (1 / 3 : ℝ) ≠ 0 :=
        (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 3)).ne'
      have hΓ23 : Real.Gamma (2 / 3 : ℝ) ≠ 0 :=
        (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 2 / 3)).ne'
      have hbase_ne : Real.Gamma (1 / 3 : ℝ) * Real.Gamma (2 / 3 : ℝ) ≠ 0 :=
        mul_ne_zero hΓ13 hΓ23
      have hx : ((3 * n : ℕ) + 1 : ℝ) ≠ 0 := by positivity
      have hx1 : ((3 * n : ℕ) + 1 : ℝ) + 1 ≠ 0 := by positivity
      have hx2 : ((3 * n : ℕ) + 1 : ℝ) + 2 ≠ 0 := by positivity
      have hstep := gamma_three_step (((3 * n : ℕ) + 1 : ℝ)) hx hx1 hx2
      have hsucc13 :
          Real.Gamma ((n + 1 : ℕ) + 1 / 3 : ℝ) =
            ((n : ℝ) + 1 / 3) * Real.Gamma ((n : ℝ) + 1 / 3) := by
        have hne : (n : ℝ) + 1 / 3 ≠ 0 := by positivity
        calc
          Real.Gamma ((n + 1 : ℕ) + 1 / 3 : ℝ) =
              Real.Gamma (((n : ℝ) + 1 / 3) + 1) := by
                congr 1
                norm_num [Nat.cast_add]
                ring
          _ = ((n : ℝ) + 1 / 3) * Real.Gamma ((n : ℝ) + 1 / 3) :=
              Real.Gamma_add_one hne
      have hsucc23 :
          Real.Gamma ((n + 1 : ℕ) + 2 / 3 : ℝ) =
            ((n : ℝ) + 2 / 3) * Real.Gamma ((n : ℝ) + 2 / 3) := by
        have hne : (n : ℝ) + 2 / 3 ≠ 0 := by positivity
        calc
          Real.Gamma ((n + 1 : ℕ) + 2 / 3 : ℝ) =
              Real.Gamma (((n : ℝ) + 2 / 3) + 1) := by
                congr 1
                norm_num [Nat.cast_add]
                ring
          _ = ((n : ℝ) + 2 / 3) * Real.Gamma ((n : ℝ) + 2 / 3) :=
              Real.Gamma_add_one hne
      have hsucc1 :
          Real.Gamma ((n + 1 : ℕ) + 1 : ℝ) =
            ((n : ℝ) + 1) * Real.Gamma ((n : ℝ) + 1) := by
        have hne : (n : ℝ) + 1 ≠ 0 := by positivity
        calc
          Real.Gamma ((n + 1 : ℕ) + 1 : ℝ) =
              Real.Gamma (((n : ℝ) + 1) + 1) := by
                congr 1
                norm_num [Nat.cast_add]
          _ = ((n : ℝ) + 1) * Real.Gamma ((n : ℝ) + 1) :=
              Real.Gamma_add_one hne
      calc
        Real.Gamma ((3 * (n + 1) : ℕ) + 1 : ℝ)
            = Real.Gamma (((3 * n : ℕ) + 1 : ℝ) + 3) := by
                congr 1
                norm_num [Nat.cast_add, Nat.cast_mul]
                ring
        _ = (((3 * n : ℕ) + 1 : ℝ) + 2) *
              (((3 * n : ℕ) + 1 : ℝ) + 1) *
              ((3 * n : ℕ) + 1 : ℝ) *
              Real.Gamma ((3 * n : ℕ) + 1 : ℝ) := hstep
        _ =
            (3 : ℝ) ^ (3 * (n + 1)) *
              Real.Gamma ((n + 1 : ℕ) + 1 / 3 : ℝ) *
              Real.Gamma ((n + 1 : ℕ) + 2 / 3 : ℝ) *
              Real.Gamma ((n + 1 : ℕ) + 1 : ℝ) /
              (Real.Gamma (1 / 3 : ℝ) * Real.Gamma (2 / 3 : ℝ)) := by
                rw [ih, hsucc13, hsucc23, hsucc1]
                field_simp [hbase_ne]
                norm_num [Nat.cast_add, Nat.cast_mul, pow_succ]
                ring

lemma gamma_two_mul_nat_add_two (n : ℕ) :
    Real.Gamma ((n : ℝ) + 1) * Real.Gamma ((n : ℝ) + 3 / 2) =
      Real.Gamma ((2 * n : ℕ) + 2 : ℝ) *
        (2 : ℝ) ^ (-(2 * (n : ℝ) + 1)) * Real.sqrt Real.pi := by
  have h := Real.Gamma_mul_Gamma_add_half ((n : ℝ) + 1)
  have hhalf : (n : ℝ) + 1 + 1 / 2 = (n : ℝ) + 3 / 2 := by ring
  have harg : 2 * ((n : ℝ) + 1) = ((2 * n : ℕ) + 2 : ℝ) := by
    norm_num [Nat.cast_mul]
    ring
  have hexp : (1 : ℝ) - (((2 * n : ℕ) + 2 : ℝ)) = -(2 * (n : ℝ) + 1) := by
    norm_num [Nat.cast_mul]
    ring
  rwa [hhalf, harg, hexp] at h

lemma gamma_two_mul_nat_add_two_solved (n : ℕ) :
    Real.Gamma ((2 * n : ℕ) + 2 : ℝ) =
      (Real.Gamma ((n : ℝ) + 1) * Real.Gamma ((n : ℝ) + 3 / 2)) /
        ((2 : ℝ) ^ (-(2 * (n : ℝ) + 1)) * Real.sqrt Real.pi) := by
  have h := gamma_two_mul_nat_add_two n
  have hpow : (2 : ℝ) ^ (-(2 * (n : ℝ) + 1)) ≠ 0 := by positivity
  have hsqrt : Real.sqrt Real.pi ≠ 0 := by positivity
  field_simp [hpow, hsqrt] at h ⊢
  linarith

lemma ternaryTreeCount_gamma_factorial (n : ℕ) :
    (ternaryTreeCount n : ℝ) =
      Real.Gamma ((3 * n : ℕ) + 1 : ℝ) /
        (Real.Gamma ((n : ℝ) + 1) *
          Real.Gamma ((2 * n : ℕ) + 2 : ℝ)) := by
  have hΓ3 : Real.Gamma ((3 * n : ℕ) + 1 : ℝ) = (((3 * n).factorial : ℕ) : ℝ) := by
    simpa using Real.Gamma_nat_eq_factorial (3 * n)
  have hΓn : Real.Gamma ((n : ℝ) + 1) = ((n.factorial : ℕ) : ℝ) := by
    simpa using Real.Gamma_nat_eq_factorial n
  have hΓ2 : Real.Gamma ((2 * n : ℕ) + 2 : ℝ) =
      (((2 * n + 1 : ℕ) : ℝ) * (((2 * n).factorial : ℕ) : ℝ)) := by
    have h := Real.Gamma_nat_eq_factorial (2 * n + 1)
    have hfac : ((2 * n + 1).factorial : ℝ) =
        ((2 * n + 1 : ℕ) : ℝ) * (((2 * n).factorial : ℕ) : ℝ) := by
      rw [show 2 * n + 1 = (2 * n) + 1 by omega, Nat.factorial_succ]
      norm_num
    rw [← hfac]
    calc
      Real.Gamma ((2 * n : ℕ) + 2 : ℝ) =
          Real.Gamma ((2 * n + 1 : ℕ) + 1 : ℝ) := by
            congr 1
            norm_num [Nat.cast_add, Nat.cast_mul]
            ring
      _ = ((2 * n + 1).factorial : ℝ) := h
  rw [ternaryTreeCount_cast n, choose_three_mul_cast n, hΓ3, hΓn, hΓ2]
  have hnfac : ((n.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have h2fac : (((2 * n).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hodd : ((2 * n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hnfac, h2fac, hodd]

lemma ternaryTreeCount_eq_gamma_ratios_raw (n : ℕ) :
    (ternaryTreeCount n : ℝ) =
      ternaryGammaPrefactor n *
        (ternaryGammaRatio (1 / 3 : ℝ) n *
          ternaryGammaRatio (2 / 3 : ℝ) n /
          ternaryGammaRatio (3 / 2 : ℝ) n) := by
  rw [ternaryTreeCount_gamma_factorial n, gamma_three_mul_nat_add_one n,
    gamma_two_mul_nat_add_two_solved n]
  unfold ternaryGammaPrefactor ternaryGammaRatio
  have hΓ13 : Real.Gamma (1 / 3 : ℝ) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 3)).ne'
  have hΓ23 : Real.Gamma (2 / 3 : ℝ) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 2 / 3)).ne'
  have hΓn1 : Real.Gamma ((n : ℝ) + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity : 0 < (n : ℝ) + 1)).ne'
  have hΓn32 : Real.Gamma ((n : ℝ) + 3 / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity : 0 < (n : ℝ) + 3 / 2)).ne'
  have hpow : (2 : ℝ) ^ (-(2 * (n : ℝ) + 1)) ≠ 0 := by positivity
  have hsqrt : Real.sqrt Real.pi ≠ 0 := by positivity
  field_simp [hΓ13, hΓ23, hΓn1, hΓn32, hpow, hsqrt]

lemma ternaryGammaPrefactor_eq (n : ℕ) :
    ternaryGammaPrefactor n =
      (27 / 4 : ℝ) ^ n * ternaryAsymptoticConstant := by
  unfold ternaryGammaPrefactor ternaryAsymptoticConstant
  rw [gamma_one_third_mul_two_thirds]
  have h2rpow :
      (2 : ℝ) ^ (-(2 * (n : ℝ) + 1)) = ((2 : ℝ) ^ (2 * n + 1))⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    rw [show 2 * (n : ℝ) + 1 = ((2 * n + 1 : ℕ) : ℝ) by
      norm_num [Nat.cast_mul, Nat.cast_add]]
    rw [Real.rpow_natCast]
  rw [h2rpow]
  have hsqrtπ : Real.sqrt Real.pi ≠ 0 := by positivity
  have hsqrt3 : Real.sqrt 3 ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hsqrtπ_sq : Real.sqrt Real.pi ^ 2 = Real.pi := by
    rw [Real.sq_sqrt Real.pi_nonneg]
  have h3pow : (3 : ℝ) ^ (3 * n) = 27 ^ n := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num]
    rw [pow_mul]
  have h2pow : (2 : ℝ) ^ (2 * n + 1) = 2 * 4 ^ n := by
    rw [pow_add]
    norm_num
    rw [show (2 : ℝ) ^ (2 * n) = 4 ^ n by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
      rw [pow_mul]]
    ring
  rw [h3pow, h2pow]
  field_simp [hsqrtπ, hsqrt3, hpi]
  rw [hsqrtπ_sq]
  rw [show (27 / 4 : ℝ) ^ n = 27 ^ n / 4 ^ n by rw [div_pow]]
  field_simp [pow_ne_zero n (by norm_num : (4 : ℝ) ≠ 0), hpi]
  ring

lemma ternaryTreeCount_eq_gamma_ratios (n : ℕ) :
    (ternaryTreeCount n : ℝ) =
      (27 / 4 : ℝ) ^ n * ternaryAsymptoticConstant *
        (ternaryGammaRatio (1 / 3 : ℝ) n *
          ternaryGammaRatio (2 / 3 : ℝ) n /
          ternaryGammaRatio (3 / 2 : ℝ) n) := by
  rw [ternaryTreeCount_eq_gamma_ratios_raw n, ternaryGammaPrefactor_eq n]

lemma ternaryGammaProduct_normalized_eq_of_one_le {n : ℕ} (hn : 1 ≤ n) :
    (ternaryGammaRatio (1 / 3 : ℝ) n *
        ternaryGammaRatio (2 / 3 : ℝ) n /
        ternaryGammaRatio (3 / 2 : ℝ) n) /
      ((n : ℝ) ^ (-(3 / 2 : ℝ))) =
    ternaryGammaNormalizedProduct n := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  have hp1 : (n : ℝ) ^ ((1 / 3 : ℝ) - 1) ≠ 0 :=
    (Real.rpow_pos_of_pos hnpos _).ne'
  have hp2 : (n : ℝ) ^ ((2 / 3 : ℝ) - 1) ≠ 0 :=
    (Real.rpow_pos_of_pos hnpos _).ne'
  have hp3 : (n : ℝ) ^ ((3 / 2 : ℝ) - 1) ≠ 0 :=
    (Real.rpow_pos_of_pos hnpos _).ne'
  have hp : (n : ℝ) ^ (-(3 / 2 : ℝ)) ≠ 0 :=
    (Real.rpow_pos_of_pos hnpos _).ne'
  have hR3 : ternaryGammaRatio (3 / 2 : ℝ) n ≠ 0 := by
    unfold ternaryGammaRatio
    have hnum : Real.Gamma ((n : ℝ) + 3 / 2) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by positivity : 0 < (n : ℝ) + 3 / 2)).ne'
    have hden : Real.Gamma ((n : ℝ) + 1) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by positivity : 0 < (n : ℝ) + 1)).ne'
    exact div_ne_zero hnum hden
  have hpow :
      (n : ℝ) ^ ((1 / 3 : ℝ) - 1) *
          (n : ℝ) ^ ((2 / 3 : ℝ) - 1) /
          (n : ℝ) ^ ((3 / 2 : ℝ) - 1) =
        (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [div_eq_mul_inv]
    rw [← Real.rpow_neg hnpos.le]
    rw [← Real.rpow_add hnpos, ← Real.rpow_add hnpos]
    congr 1
    norm_num
  unfold ternaryGammaNormalizedProduct
  rw [gammaRatioNormalizedFactor_eq, gammaRatioNormalizedFactor_eq,
    gammaRatioNormalizedFactor_eq]
  field_simp [hp1, hp2, hp3, hp, hR3]
  have hpow' :
      (n : ℝ) ^ (((1 : ℝ) - 3) / 3) *
          (n : ℝ) ^ (((2 : ℝ) - 3) / 3) =
        (n : ℝ) ^ (-(3 / 2 : ℝ)) *
          (n : ℝ) ^ (((3 : ℝ) - 2) / 2) := by
    rw [← Real.rpow_add hnpos, ← Real.rpow_add hnpos]
    congr 1
    norm_num
  calc
    ternaryGammaRatio (1 / 3) n * ternaryGammaRatio (2 / 3) n *
          (n : ℝ) ^ (((1 : ℝ) - 3) / 3) *
          (n : ℝ) ^ (((2 : ℝ) - 3) / 3)
        =
        ternaryGammaRatio (1 / 3) n * ternaryGammaRatio (2 / 3) n *
          ((n : ℝ) ^ (((1 : ℝ) - 3) / 3) *
            (n : ℝ) ^ (((2 : ℝ) - 3) / 3)) := by ring
    _ =
        ternaryGammaRatio (1 / 3) n * ternaryGammaRatio (2 / 3) n *
          ((n : ℝ) ^ (-(3 / 2 : ℝ)) *
            (n : ℝ) ^ (((3 : ℝ) - 2) / 2)) := by rw [hpow']
    _ =
        ternaryGammaRatio (1 / 3) n * ternaryGammaRatio (2 / 3) n *
          (n : ℝ) ^ (-(3 / 2 : ℝ)) *
          (n : ℝ) ^ (((3 : ℝ) - 2) / 2) := by ring

lemma gammaRatioNormalizedError_isBigO {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => gammaRatioNormalizedError α n)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(2 : ℝ))) := by
  have hO := gamma_ratio_second_order (α := α) hα
  have hp : (fun n : ℕ => (n : ℝ) ^ (1 - α))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 - α)) := isBigO_refl _ _
  have hmul :
      (fun n : ℕ =>
        (ternaryGammaRatio α n -
          (n : ℝ) ^ (α - 1) *
            (1 + α * (α - 1) / (2 * (n : ℝ)))) *
          (n : ℝ) ^ (1 - α))
        =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(2 : ℝ))) := by
    simpa [ternaryGammaRatio] using
      IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
        (a := α - 3) (b := 1 - α) (c := -(2 : ℝ)) hO hp (by norm_num)
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
  unfold gammaRatioNormalizedError gammaRatioSecondCoeff
  rw [hpow_inv]
  field_simp [hpow_ne, hnne]

lemma gammaRatioNormalizedError_isBigO_inv_sq {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => gammaRatioNormalizedError α n)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  have h := gammaRatioNormalizedError_isBigO (α := α) hα
  refine h.congr' (EventuallyEq.refl _ _) ?_
  filter_upwards with n
  rw [Real.rpow_neg (Nat.cast_nonneg n)]
  norm_num [inv_pow]

private lemma inv_nat_sq_tendsto_zero :
    Tendsto (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) atTop (𝓝 0) := by
  simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2

private lemma inv_nat_isBigO_one :
    (fun n : ℕ => (n : ℝ)⁻¹) =O[atTop] (fun _n : ℕ => (1 : ℝ)) := by
  exact (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).isBigO_one ℝ

private lemma inv_nat_sq_isBigO_one :
    (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) =O[atTop] (fun _n : ℕ => (1 : ℝ)) := by
  exact inv_nat_sq_tendsto_zero.isBigO_one ℝ

private lemma inv_nat_sq_isBigO_inv_sq :
    (fun n : ℕ => (n : ℝ)⁻¹ * (n : ℝ)⁻¹)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  refine (isBigO_refl (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) atTop).congr' ?_
    (EventuallyEq.refl _ _)
  filter_upwards with n
  ring

private lemma linear_error_mul_isBigO_inv_sq
    {e f : ℕ → ℝ} {a b : ℝ}
    (he : e =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2))
    (hf : f =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2)) :
    (fun n : ℕ =>
      (1 + a * (n : ℝ)⁻¹ + e n) * (1 + b * (n : ℝ)⁻¹ + f n) -
        (1 + (a + b) * (n : ℝ)⁻¹))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  have hI2 : (fun n : ℕ => a * b * ((n : ℝ)⁻¹ * (n : ℝ)⁻¹))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) :=
    inv_nat_sq_isBigO_inv_sq.const_mul_left (a * b)
  have hIf : (fun n : ℕ => a * (n : ℝ)⁻¹ * f n)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
    have h := (inv_nat_isBigO_one.const_mul_left a).mul hf
    simpa [Pi.mul_apply, mul_assoc] using h
  have hIe : (fun n : ℕ => b * (n : ℝ)⁻¹ * e n)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
    have h := (inv_nat_isBigO_one.const_mul_left b).mul he
    simpa [Pi.mul_apply, mul_assoc] using h
  have hf_one : f =O[atTop] (fun _n : ℕ => (1 : ℝ)) :=
    hf.trans inv_nat_sq_isBigO_one
  have hef : (fun n : ℕ => e n * f n)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
    have h := he.mul hf_one
    simpa [Pi.mul_apply] using h
  have hsum := (((((hI2.add hf).add he).add hIf).add hIe).add hef)
  refine hsum.congr_left ?_
  intro n
  ring

private lemma linear_error_inv_isBigO_inv_sq
    {e : ℕ → ℝ} {a : ℝ}
    (he : e =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2)) :
    (fun n : ℕ =>
      (1 + a * (n : ℝ)⁻¹ + e n)⁻¹ - (1 - a * (n : ℝ)⁻¹))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  have he0 : Tendsto e atTop (𝓝 0) :=
    he.trans_tendsto inv_nat_sq_tendsto_zero
  have hlin0 : Tendsto (fun n : ℕ => a * (n : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul a
  have hden0 : Tendsto (fun n : ℕ => 1 + a * (n : ℝ)⁻¹ + e n) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add hlin0).add he0
  have hden_ne : ∀ᶠ n : ℕ in atTop, 1 + a * (n : ℝ)⁻¹ + e n ≠ 0 :=
    hden0.eventually (compl_singleton_mem_nhds (by norm_num : (1 : ℝ) ≠ 0))
  have hden_inv_one :
      (fun n : ℕ => (1 + a * (n : ℝ)⁻¹ + e n)⁻¹)
        =O[atTop] (fun _n : ℕ => (1 : ℝ)) :=
    (hden0.inv₀ (by norm_num : (1 : ℝ) ≠ 0)).isBigO_one ℝ
  have hx2 : (fun n : ℕ => a * a * ((n : ℝ)⁻¹ * (n : ℝ)⁻¹))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) :=
    inv_nat_sq_isBigO_inv_sq.const_mul_left (a * a)
  have hxe : (fun n : ℕ => a * (n : ℝ)⁻¹ * e n)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
    have h := (inv_nat_isBigO_one.const_mul_left a).mul he
    simpa [Pi.mul_apply, mul_assoc] using h
  have hnum : (fun n : ℕ =>
      a * a * ((n : ℝ)⁻¹ * (n : ℝ)⁻¹) - e n + a * (n : ℝ)⁻¹ * e n)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
    simpa [sub_eq_add_neg] using (hx2.add he.neg_left).add hxe
  have hprod := hnum.mul hden_inv_one
  refine hprod.congr' ?_ ?_
  · filter_upwards [hden_ne] with n hne
    let I : ℝ := (n : ℝ)⁻¹
    change
      (a * a * (I * I) - e n + a * I * e n) * (1 + a * I + e n)⁻¹ =
        (1 + a * I + e n)⁻¹ - (1 - a * I)
    have hneI : 1 + a * I + e n ≠ 0 := by simpa [I] using hne
    field_simp [hneI]
    ring
  · filter_upwards with n
    ring

theorem ternaryGammaNormalizedProduct_secondOrder :
    (fun n : ℕ =>
      ternaryGammaNormalizedProduct n -
        (1 + ternaryRelativeSecondConstant * (n : ℝ)⁻¹))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  let c₁ : ℝ := gammaRatioSecondCoeff (1 / 3 : ℝ)
  let c₂ : ℝ := gammaRatioSecondCoeff (2 / 3 : ℝ)
  let c₃ : ℝ := gammaRatioSecondCoeff (3 / 2 : ℝ)
  let e₁ : ℕ → ℝ := gammaRatioNormalizedError (1 / 3 : ℝ)
  let e₂ : ℕ → ℝ := gammaRatioNormalizedError (2 / 3 : ℝ)
  let e₃ : ℕ → ℝ := gammaRatioNormalizedError (3 / 2 : ℝ)
  let e₁₂ : ℕ → ℝ := fun n =>
    (1 + c₁ * (n : ℝ)⁻¹ + e₁ n) * (1 + c₂ * (n : ℝ)⁻¹ + e₂ n) -
      (1 + (c₁ + c₂) * (n : ℝ)⁻¹)
  let e₃inv : ℕ → ℝ := fun n =>
    (1 + c₃ * (n : ℝ)⁻¹ + e₃ n)⁻¹ - (1 - c₃ * (n : ℝ)⁻¹)
  have he₁ : e₁ =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
    simpa [e₁] using
      gammaRatioNormalizedError_isBigO_inv_sq
        (α := (1 / 3 : ℝ)) (by norm_num : (0 : ℝ) < 1 / 3)
  have he₂ : e₂ =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
    simpa [e₂] using
      gammaRatioNormalizedError_isBigO_inv_sq
        (α := (2 / 3 : ℝ)) (by norm_num : (0 : ℝ) < 2 / 3)
  have he₃ : e₃ =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
    simpa [e₃] using
      gammaRatioNormalizedError_isBigO_inv_sq
        (α := (3 / 2 : ℝ)) (by norm_num : (0 : ℝ) < 3 / 2)
  have he₁₂ : e₁₂ =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
    simpa [e₁₂] using
      linear_error_mul_isBigO_inv_sq (a := c₁) (b := c₂) he₁ he₂
  have he₃inv : e₃inv =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
    simpa [e₃inv] using
      linear_error_inv_isBigO_inv_sq (a := c₃) he₃
  have hprod :=
    linear_error_mul_isBigO_inv_sq
      (e := e₁₂) (f := e₃inv) (a := c₁ + c₂) (b := -c₃) he₁₂ he₃inv
  have hcorr : c₁ + c₂ - c₃ = ternaryRelativeSecondConstant := by
    simpa [c₁, c₂, c₃] using ternary_gamma_ratio_correction
  refine hprod.congr_left ?_
  intro n
  unfold ternaryGammaNormalizedProduct gammaRatioNormalizedFactor
  dsimp [e₁, e₂, e₃, e₁₂, e₃inv, c₁, c₂, c₃]
  rw [← hcorr]
  ring

theorem ternaryGammaProduct_normalized_secondOrder :
    (fun n : ℕ =>
      (ternaryGammaRatio (1 / 3 : ℝ) n *
          ternaryGammaRatio (2 / 3 : ℝ) n /
          ternaryGammaRatio (3 / 2 : ℝ) n) /
        ((n : ℝ) ^ (-(3 / 2 : ℝ))) -
        (1 + ternaryRelativeSecondConstant * (n : ℝ)⁻¹))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  refine ternaryGammaNormalizedProduct_secondOrder.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [ternaryGammaProduct_normalized_eq_of_one_le hn]

theorem ternaryTreeCount_normalized_secondOrder :
    (fun n : ℕ =>
      (ternaryTreeCount n : ℝ) /
          ((27 / 4 : ℝ) ^ n * ternaryAsymptoticConstant *
            (n : ℝ) ^ (-(3 / 2 : ℝ))) -
        (1 + ternaryRelativeSecondConstant * (n : ℝ)⁻¹))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  refine ternaryGammaProduct_normalized_secondOrder.congr' ?_ (EventuallyEq.refl _ _)
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
