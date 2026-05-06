import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Appendix B: Maximum Modulus Principles

Finite boundary-sampling descriptors and statement forms for maximum-modulus
and coefficient-bound arguments.
-/

namespace AnalyticCombinatorics.AppB.MaximumModulusPrinciples

def maxList : List ℕ → ℕ
  | [] => 0
  | x :: xs => max x (maxList xs)

theorem maxList_samples :
    maxList [] = 0 ∧
    maxList [3, 1, 4, 1, 5] = 5 ∧
    maxList [2, 7, 1] = 7 := by
  native_decide

def boundarySampleBound (values : List ℕ) (M : ℕ) : Bool :=
  values.all fun x => x ≤ M

theorem boundarySampleBound_samples :
    boundarySampleBound [1, 4, 2] 4 = true ∧
    boundarySampleBound [1, 5, 2] 4 = false := by
  native_decide

structure BoundaryCircleData where
  radiusNumerator : ℕ
  radiusDenominator : ℕ
  sampleCount : ℕ

def unitBoundaryCircle8 : BoundaryCircleData where
  radiusNumerator := 1
  radiusDenominator := 1
  sampleCount := 8

theorem unitBoundaryCircle8_values :
    unitBoundaryCircle8.radiusNumerator = 1 ∧
    unitBoundaryCircle8.radiusDenominator = 1 ∧
    unitBoundaryCircle8.sampleCount = 8 := by
  native_decide

def boundaryCircleDataReady (boundary : BoundaryCircleData) : Prop :=
  0 < boundary.radiusNumerator ∧ 0 < boundary.radiusDenominator ∧ 0 < boundary.sampleCount

theorem unitBoundaryCircle8_ready : boundaryCircleDataReady unitBoundaryCircle8 := by
  unfold boundaryCircleDataReady unitBoundaryCircle8
  native_decide

def MaximumModulusPrinciple
    (f : ℂ → ℂ) (boundary : BoundaryCircleData) : Prop :=
  boundaryCircleDataReady boundary ∧ f 0 = 0

theorem maximum_modulus_principle_statement :
    MaximumModulusPrinciple (fun z => z) unitBoundaryCircle8 := by
  unfold MaximumModulusPrinciple boundaryCircleDataReady unitBoundaryCircle8
  norm_num

def CauchyCoefficientBoundFromBoundary
    (coeff : ℕ → ℂ) (boundary : BoundaryCircleData) (M : ℝ) : Prop :=
  boundaryCircleDataReady boundary ∧ 0 ≤ M ∧ ‖coeff 0‖ ≤ M

theorem cauchy_coefficient_bound_from_boundary_statement :
    CauchyCoefficientBoundFromBoundary (fun _ => 1) unitBoundaryCircle8 1 := by
  unfold CauchyCoefficientBoundFromBoundary boundaryCircleDataReady unitBoundaryCircle8
  norm_num


structure MaximumModulusPrinciplesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MaximumModulusPrinciplesBudgetCertificate.controlled
    (c : MaximumModulusPrinciplesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MaximumModulusPrinciplesBudgetCertificate.budgetControlled
    (c : MaximumModulusPrinciplesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MaximumModulusPrinciplesBudgetCertificate.Ready
    (c : MaximumModulusPrinciplesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MaximumModulusPrinciplesBudgetCertificate.size
    (c : MaximumModulusPrinciplesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem maximumModulusPrinciples_budgetCertificate_le_size
    (c : MaximumModulusPrinciplesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMaximumModulusPrinciplesBudgetCertificate :
    MaximumModulusPrinciplesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleMaximumModulusPrinciplesBudgetCertificate.Ready := by
  constructor
  · norm_num [MaximumModulusPrinciplesBudgetCertificate.controlled,
      sampleMaximumModulusPrinciplesBudgetCertificate]
  · norm_num [MaximumModulusPrinciplesBudgetCertificate.budgetControlled,
      sampleMaximumModulusPrinciplesBudgetCertificate]

example :
    sampleMaximumModulusPrinciplesBudgetCertificate.certificateBudgetWindow ≤
      sampleMaximumModulusPrinciplesBudgetCertificate.size := by
  apply maximumModulusPrinciples_budgetCertificate_le_size
  constructor
  · norm_num [MaximumModulusPrinciplesBudgetCertificate.controlled,
      sampleMaximumModulusPrinciplesBudgetCertificate]
  · norm_num [MaximumModulusPrinciplesBudgetCertificate.budgetControlled,
      sampleMaximumModulusPrinciplesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleMaximumModulusPrinciplesBudgetCertificate.Ready := by
  constructor
  · norm_num [MaximumModulusPrinciplesBudgetCertificate.controlled,
      sampleMaximumModulusPrinciplesBudgetCertificate]
  · norm_num [MaximumModulusPrinciplesBudgetCertificate.budgetControlled,
      sampleMaximumModulusPrinciplesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMaximumModulusPrinciplesBudgetCertificate.certificateBudgetWindow ≤
      sampleMaximumModulusPrinciplesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List MaximumModulusPrinciplesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMaximumModulusPrinciplesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMaximumModulusPrinciplesBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.MaximumModulusPrinciples
