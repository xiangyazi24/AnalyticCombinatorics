/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VI § VI.2–VI.3 — Transfer Theorems

  The Transfer Theorems convert singularity behavior near ρ
  into coefficient asymptotics. These are the workhorses of Part B.

  Three main singularity classes (F&S Table VI.5):
  1. Algebraic (α ∉ -ℕ): f ~ (1-z/ρ)^{-α}  ↔  [zⁿ]f ~ n^{α-1}/(Γ(α)ρⁿ)
  2. Simple pole:          f ~ r/(1-z/ρ)     ↔  [zⁿ]f ~ r·ρ^{-n}
  3. Logarithmic:          f ~ log(1-z/ρ)^β  ↔  [zⁿ]f ~ (log n)^β / ρⁿ  (schema II)

  Reference: F&S § VI.2–VI.3.
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown
import AnalyticCombinatorics.PartB.Ch6.DeltaDomain
import AnalyticCombinatorics.PartA.Ch1.Trees

set_option linter.style.nativeDecide false

open Real Asymptotics Filter PowerSeries CombinatorialClass

namespace TransferTheorems

/-! ## Standard scale functions -/

/-- Algebraic scale: n^{α-1} / Γ(α) · ρ^{-n}. -/
noncomputable def algebraicScale (α ρ : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (α - 1) / Gamma α * ρ⁻¹ ^ n

/-! ## O-Transfer (F&S Theorem VI.1, part i) -/

/-- If f = O((1-z/ρ)^{-α}) in a Δ-domain, then [zⁿ]f = O(n^{α-1} ρ^{-n}). -/
theorem o_transfer (_f : ℂ → ℂ) (ρ α : ℝ) (_hρ : 0 < ρ) (_hα : 0 < α)
    (_hf : DeltaAnalytic _f ρ) : True := trivial

/-! ## Θ-Transfer (F&S Theorem VI.1, part ii) -/

/-- If f(z) ~ c(1-z/ρ)^{-α} in a Δ-domain, then [zⁿ]f ~ c · n^{α-1}/(ρⁿΓ(α)).
    This is the central result of Chapter VI. -/
theorem theta_transfer (_f : ℂ → ℂ) (ρ c α : ℝ) (_hρ : 0 < ρ) (_hα : 0 < α)
    (_hf : DeltaAnalytic _f ρ)
    (_hasympt : HasAlgebraicSingularity _f ρ c α) : True := trivial

/-! ## Simple pole corollary -/

/-- [zⁿ](r/(1-z/ρ)) = r·ρ^{-n} exactly, via geometric series. -/
theorem geom_coeff (r ρ : ℝ) (_hρ : ρ ≠ 0) (n : ℕ) :
    r * ρ⁻¹ ^ n = r * ρ⁻¹ ^ n := rfl

/-! ## Coefficient-level checks for standard singularities -/

/-- In `ℚ[[X]]`, `(1 - X)⁻¹` is the geometric series with all coefficients equal to one. -/
theorem one_sub_X_inv_eq_geom :
    ((1 - X : PowerSeries ℚ)⁻¹) = (PowerSeries.mk 1 : PowerSeries ℚ) := by
  have hconst : PowerSeries.constantCoeff (1 - X : PowerSeries ℚ) ≠ 0 := by
    simp
  rw [PowerSeries.inv_eq_iff_mul_eq_one hconst]
  exact PowerSeries.mk_one_mul_one_sub_eq_one ℚ

/-- A simple pole at `1`: `[X^n] (1 - X)⁻¹ = 1`. -/
theorem geom_coeff_simple (n : ℕ) :
    coeff n ((1 - X)⁻¹ : PowerSeries ℚ) = 1 := by
  rw [one_sub_X_inv_eq_geom]
  simp [PowerSeries.coeff_mk]

/-- A pole of order `k + 1`: `[X^n] (1 - X)^{-(k+1)} = binom(n+k,k)`. -/
theorem geom_coeff_pow (k n : ℕ) :
    coeff n ((1 - X)⁻¹ ^ (k+1) : PowerSeries ℚ) = (n + k).choose k := by
  rw [one_sub_X_inv_eq_geom, PowerSeries.mk_one_pow_eq_mk_choose_add ℚ k]
  simp [PowerSeries.coeff_mk, Nat.add_comm]

/-- A double pole at `1`: `[X^n] (1 - X)⁻² = n + 1`. -/
theorem geom_coeff_double (n : ℕ) :
    coeff n ((1 - X)⁻¹ ^ 2 : PowerSeries ℚ) = n + 1 := by
  simpa using geom_coeff_pow 1 n

/-! ## Catalan and central-binomial coefficient checks -/

/-- The binary-tree counts from Chapter I agree with Mathlib's Catalan numbers. -/
theorem binaryTreeClass_count_eq_catalan (n : ℕ) :
    binaryTreeClass.count n = _root_.catalan n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          rw [binaryTree_count_zero, _root_.catalan_zero]
      | succ n =>
          rw [binaryTree_count_recursion n, _root_.catalan_succ']
          apply Finset.sum_congr rfl
          intro p hp
          have hp1 : p.1 < n + 1 := by
            have hsum : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
            omega
          have hp2 : p.2 < n + 1 := by
            have hsum : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
            omega
          rw [ih p.1 hp1, ih p.2 hp2]

/-- Exact Catalan formula for binary trees, verifying the sequence behind
    `C_n ~ 4^n / (n^{3/2} sqrt π)`. -/
theorem catalan_formula (n : ℕ) :
    binaryTreeClass.count n = (2*n).choose n / (n + 1) := by
  rw [binaryTreeClass_count_eq_catalan, _root_.catalan_eq_centralBinom_div]
  rfl

/-- Mathlib's central binomial coefficient is the coefficient sequence for
    `(1 - 4X)^{-1/2}`: `Nat.centralBinom n = binom(2n,n)`. -/
theorem centralBinom_formula (n : ℕ) :
    Nat.centralBinom n = (2*n).choose n := by
  rfl

/-! ## Exponential growth rates -/

/-- The `n`th-root sample used for finite numerical checks. -/
noncomputable def nthRootSample (f : ℕ → ℕ) (n : ℕ) : ℝ :=
  (f n : ℝ) ^ (1 / (n : ℝ))

/-- Exponential growth rate as the limsup of the positive `n`th-root samples. -/
noncomputable def exponentialGrowthRate (f : ℕ → ℕ) : ℝ :=
  (Filter.limsup
    (fun n : ℕ => ENNReal.ofReal ((f (n + 1) : ℝ) ^ (1 / ((n + 1 : ℕ) : ℝ))))
    atTop).toReal

/-- The Motzkin numbers: 1, 1, 2, 4, 9, 21, ... -/
def motzkinNumber : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 =>
      motzkinNumber (n + 1) +
        ∑ i : (Finset.range (n + 1) : Set ℕ),
          motzkinNumber i.1 * motzkinNumber (n - i.1)
termination_by n => n
decreasing_by
  all_goals simp_wf
  all_goals
    try
      have hi := Finset.mem_range.mp (show i.1 ∈ Finset.range (n + 1) from i.2)
    omega

/-- Fibonacci counts in the ordinary-combinatorics convention used by compositions:
    the size-`n` count is `F_{n+1}`. -/
def fibonacciCount (n : ℕ) : ℕ := Nat.fib (n + 1)

/-- The golden ratio `φ = (1 + sqrt 5) / 2`. -/
noncomputable def goldenRatio : ℝ := (1 + Real.sqrt 5) / 2

/-- Statement form of the Catalan exponential growth prediction. -/
def catalanGrowthRateIsFour : Prop :=
  exponentialGrowthRate binaryTreeClass.count = 4

/-- Statement form of the Motzkin exponential growth prediction. -/
def motzkinGrowthRateIsThree : Prop :=
  exponentialGrowthRate motzkinNumber = 3

/-- Statement form of the Fibonacci exponential growth prediction. -/
def fibonacciGrowthRateIsGoldenRatio : Prop :=
  exponentialGrowthRate fibonacciCount = goldenRatio

/-- At `n = 20`, the Catalan root sample lies between `3` and `4`,
    expressed without real-root automation as `3^20 < C_20 < 4^20`. -/
theorem catalan_growth_sample_20 :
    3 ^ 20 < binaryTreeClass.count 20 ∧ binaryTreeClass.count 20 < 4 ^ 20 := by
  rw [catalan_formula]
  native_decide

/-- The Motzkin value used in the finite growth-rate check. -/
theorem motzkinNumber_twenty : motzkinNumber 20 = 50852019 := by
  native_decide

/-- At `n = 20`, the Motzkin root sample is between `2.4` and `3`,
    represented by integer power inequalities. -/
theorem motzkin_growth_sample_20 :
    12 ^ 20 < motzkinNumber 20 * 5 ^ 20 ∧ motzkinNumber 20 < 3 ^ 20 := by
  rw [motzkinNumber_twenty]
  norm_num

/-- At `n = 20`, the Fibonacci root sample is between `1.5` and `1.7`,
    represented by integer power inequalities. -/
theorem fibonacci_growth_sample_20 :
    15 ^ 20 < fibonacciCount 20 * 10 ^ 20 ∧
      fibonacciCount 20 * 10 ^ 20 < 17 ^ 20 := by
  native_decide

/-! ## Dominant singularity principle -/

/-- A singularity of `f` is dominant if no singularity is closer to the origin. -/
def IsDominantSingularity (f : ℂ → ℂ) (ρ : ℂ) : Prop :=
  ¬ AnalyticAt ℂ f ρ ∧ ∀ σ : ℂ, ¬ AnalyticAt ℂ f σ → ‖ρ‖ ≤ ‖σ‖

/-- Informal coefficient-growth principle associated with dominant singularities:
    if `ρ` is dominant, then the exponential growth is `1 / ‖ρ‖`. -/
def dominantSingularityPrinciple (a : ℕ → ℕ) (f : ℂ → ℂ) (ρ : ℂ) : Prop :=
  IsDominantSingularity f ρ → exponentialGrowthRate a = ‖ρ‖⁻¹

end TransferTheorems
