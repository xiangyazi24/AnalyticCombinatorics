import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace DominantSingularity

/-!
Dominant singularity analysis from Chapter IV of Analytic Combinatorics.

This file formalizes computable aspects of:

* Pringsheim's theorem for power series with nonneg coefficients,
* locating and classifying the dominant singularity,
* Darboux's method and singular expansions,
* transfer theorems for algebraic and logarithmic singularities,
* coefficient ratio convergence to `1/ρ`.
-/

/-! ## 1. Singularity classification and Pringsheim's theorem -/

inductive SingularityType where
  | pole (order : ℕ)
  | algebraicBranch (alpha : ℚ)
  | logarithmic
  | essential
deriving DecidableEq, Repr

structure DominantSingularityData where
  family : String
  radiusRat : ℚ
  singType : SingularityType
  asymptoticForm : String
deriving DecidableEq, Repr

def pringsheimStatement : String :=
  "If f(z) = Σ aₙ zⁿ with aₙ ≥ 0 and finite radius R, then z = R is a singularity of f."

def darbouxTransferStatement : String :=
  "[zⁿ](1 - z/ρ)^(-α) ~ ρ^(-n) · n^(α-1) / Γ(α) as n → ∞"

/-! ## 2. Dominant singularity data for standard families -/

def catalanSingularity : DominantSingularityData :=
  { family := "Catalan numbers"
    radiusRat := 1 / 4
    singType := SingularityType.algebraicBranch (1 / 2)
    asymptoticForm := "[zⁿ] ~ 4ⁿ / (n^(3/2) √π)" }

def binaryTreeSingularity : DominantSingularityData :=
  { family := "Binary trees T(z) = (1 - √(1-4z))/2"
    radiusRat := 1 / 4
    singType := SingularityType.algebraicBranch (1 / 2)
    asymptoticForm := "[zⁿ] ~ 4ⁿ / (2 √π n^(3/2))" }

def geometricSingularity : DominantSingularityData :=
  { family := "Geometric series 1/(1-z)"
    radiusRat := 1
    singType := SingularityType.pole 1
    asymptoticForm := "[zⁿ] = 1" }

def motzkinSingularity : DominantSingularityData :=
  { family := "Motzkin numbers"
    radiusRat := 1 / 3
    singType := SingularityType.algebraicBranch (1 / 2)
    asymptoticForm := "[zⁿ] ~ c · 3ⁿ / n^(3/2)" }

def partitionSingularity : DominantSingularityData :=
  { family := "Integer partitions"
    radiusRat := 1
    singType := SingularityType.essential
    asymptoticForm := "[zⁿ] ~ exp(π√(2n/3)) / (4n√3)" }

theorem catalan_singularity_is_algebraic :
    catalanSingularity.singType = SingularityType.algebraicBranch (1 / 2) := by native_decide

theorem geometric_singularity_is_simple_pole :
    geometricSingularity.singType = SingularityType.pole 1 := by native_decide

theorem partition_singularity_is_essential :
    partitionSingularity.singType = SingularityType.essential := by native_decide

theorem catalan_radius_is_quarter :
    catalanSingularity.radiusRat = 1 / 4 := by native_decide

theorem binary_tree_same_radius_as_catalan :
    binaryTreeSingularity.radiusRat = catalanSingularity.radiusRat := by native_decide

theorem motzkin_radius_is_third :
    motzkinSingularity.radiusRat = 1 / 3 := by native_decide

/-! ## 3. Darboux's method: algebraic singularity coefficients -/

def algebraicSingCoeff (alpha n : ℕ) : ℕ :=
  Nat.choose (n + alpha - 1) (alpha - 1)

def algebraicAlpha2Table : Fin 10 → ℕ :=
  ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

def algebraicAlpha3Table : Fin 10 → ℕ :=
  ![1, 3, 6, 10, 15, 21, 28, 36, 45, 55]

def algebraicAlpha4Table : Fin 8 → ℕ :=
  ![1, 4, 10, 20, 35, 56, 84, 120]

theorem algebraic_alpha2_checked :
    ∀ n : Fin 10, algebraicSingCoeff 2 n.val = algebraicAlpha2Table n := by native_decide

theorem algebraic_alpha3_checked :
    ∀ n : Fin 10, algebraicSingCoeff 3 n.val = algebraicAlpha3Table n := by native_decide

theorem algebraic_alpha4_checked :
    ∀ n : Fin 8, algebraicSingCoeff 4 n.val = algebraicAlpha4Table n := by native_decide

theorem algebraic_alpha2_formula :
    ∀ n : Fin 16, algebraicSingCoeff 2 n.val = n.val + 1 := by native_decide

theorem algebraic_alpha3_formula :
    ∀ n : Fin 16,
      algebraicSingCoeff 3 n.val = (n.val + 1) * (n.val + 2) / 2 := by native_decide

def centralBinomial (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n

def centralBinomialScaled (n : ℕ) : ℚ :=
  (centralBinomial n : ℚ) / (4 ^ n : ℚ)

theorem central_binomial_scaled_decreasing :
    ∀ n : Fin 12,
      centralBinomialScaled (n.val + 1) ≤ centralBinomialScaled n.val := by native_decide

theorem central_binomial_bounded_by_growth :
    ∀ n : Fin 14, centralBinomial n.val ≤ 4 ^ n.val := by native_decide

/-! ## 4. Transfer theorems -/

structure TransferTheorem where
  singularForm : String
  coeffAsymptotic : String
  conditions : String
deriving DecidableEq, Repr

def transferAlgebraic : TransferTheorem :=
  { singularForm := "f(z) ~ c · (1 - z/ρ)^(-α)"
    coeffAsymptotic := "[zⁿ]f ~ c · ρ^(-n) · n^(α-1) / Γ(α)"
    conditions := "f analytic in Δ-domain at ρ, α ∉ {0,-1,-2,…}" }

def transferAlgebraicLog : TransferTheorem :=
  { singularForm := "f(z) ~ c · (1 - z/ρ)^(-α) · log(1/(1-z/ρ))^β"
    coeffAsymptotic := "[zⁿ]f ~ c · ρ^(-n) · n^(α-1) · (log n)^β / Γ(α)"
    conditions := "f analytic in Δ-domain at ρ, β ∈ ℝ" }

def transferPureLog : TransferTheorem :=
  { singularForm := "f(z) ~ c · log(1/(1-z/ρ))"
    coeffAsymptotic := "[zⁿ]f ~ c / (ρⁿ · n)"
    conditions := "f analytic in Δ-domain at ρ" }

/-! ## 5. Logarithmic singularity coefficients -/

def logSingCoeff (n : ℕ) : ℚ :=
  if n = 0 then 0 else 1 / (n : ℚ)

def harmonicNumber (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, 1 / ((k + 1 : ℕ) : ℚ)

def harmonicTable : Fin 8 → ℚ :=
  ![(0 : ℚ), 1, 3 / 2, 11 / 6, 25 / 12, 137 / 60, 49 / 20, 363 / 140]

theorem harmonic_table_checked :
    ∀ n : Fin 8, harmonicNumber n.val = harmonicTable n := by native_decide

def logSingPartialSum (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), logSingCoeff k

theorem log_sing_partial_sum_is_harmonic :
    ∀ n : Fin 10, logSingPartialSum n.val = harmonicNumber n.val := by native_decide

theorem harmonic_monotone_small :
    ∀ n : Fin 12, harmonicNumber n.val ≤ harmonicNumber (n.val + 1) := by native_decide

def harmonicTimesN (n : ℕ) : ℚ :=
  (n : ℚ) * harmonicNumber n

def harmonicTimesNTable : Fin 7 → ℚ :=
  ![(0 : ℚ), 1, 3, 11 / 2, 25 / 3, 137 / 12, 147 / 10]

theorem harmonic_times_n_checked :
    ∀ n : Fin 7, harmonicTimesN n.val = harmonicTimesNTable n := by
  sorry

/-! ## 6. Coefficient ratio convergence to `1/ρ` -/

def catalanNumber (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

def coeffRatio (a : ℕ → ℕ) (n : ℕ) : ℚ :=
  if a n = 0 then 0 else (a (n + 1) : ℚ) / (a n : ℚ)

def catalanRatioTable : Fin 8 → ℚ :=
  ![(1 : ℚ), 2, 5 / 2, 14 / 5, 3, 22 / 7, 13 / 4, 10 / 3]

theorem catalan_ratio_table_checked :
    ∀ n : Fin 8, coeffRatio catalanNumber n.val = catalanRatioTable n := by native_decide

theorem catalan_ratios_below_four :
    ∀ n : Fin 10, coeffRatio catalanNumber n.val < 4 := by native_decide

theorem catalan_ratios_increasing :
    ∀ n : Fin 9,
      coeffRatio catalanNumber n.val ≤ coeffRatio catalanNumber (n.val + 1) := by native_decide

def catalanRatioError (n : ℕ) : ℚ :=
  4 - coeffRatio catalanNumber (n + 1)

def catalanRatioErrorTable : Fin 6 → ℚ :=
  ![(2 : ℚ), 3 / 2, 6 / 5, 1, 6 / 7, 3 / 4]

theorem catalan_ratio_error_checked :
    ∀ n : Fin 6,
      catalanRatioError n.val = catalanRatioErrorTable n := by native_decide

theorem catalan_ratio_error_decreasing :
    ∀ n : Fin 8,
      catalanRatioError (n.val + 1) ≤ catalanRatioError n.val := by native_decide

/-! ## 7. Dominance ordering and Pringsheim verification -/

example : catalanSingularity.radiusRat < motzkinSingularity.radiusRat := by native_decide
example : motzkinSingularity.radiusRat < geometricSingularity.radiusRat := by native_decide
example : catalanSingularity.radiusRat < geometricSingularity.radiusRat := by native_decide

theorem catalan_nonneg_small :
    ∀ n : Fin 12, 0 < catalanNumber (n.val + 1) := by native_decide

def motzkinNumber : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 =>
      ((2 * n + 5) * motzkinNumber (n + 1) + (3 * n + 3) * motzkinNumber n) / (n + 4)

theorem motzkin_nonneg_small :
    ∀ n : Fin 10, 0 < motzkinNumber n.val := by native_decide

def motzkinRatio (n : ℕ) : ℚ :=
  (motzkinNumber (n + 1) : ℚ) / (motzkinNumber n : ℚ)

theorem motzkin_ratios_below_three :
    ∀ n : Fin 8, motzkinRatio n.val < 3 := by native_decide

end DominantSingularity
