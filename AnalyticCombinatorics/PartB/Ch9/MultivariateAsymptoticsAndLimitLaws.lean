import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Multivariate asymptotics and limit laws
-/

namespace AnalyticCombinatorics.PartB.Ch9.MultivariateAsymptoticsAndLimitLaws

/-- Finite bivariate mass table over a sampled rectangle. -/
def bivariateMassTotal (mass : ℕ → ℕ → ℚ) (N K : ℕ) : ℚ :=
  (List.range (N + 1)).foldl
    (fun total n =>
      total + (List.range (K + 1)).foldl
        (fun row k => row + mass n k) 0) 0

def diagonalPointMass (n k : ℕ) : ℚ :=
  if n = 0 ∧ k = 0 then 1 else 0

theorem diagonalPointMass_total :
    bivariateMassTotal diagonalPointMass 3 3 = 1 := by
  unfold bivariateMassTotal diagonalPointMass
  native_decide

/-- First coordinate moment over a sampled bivariate distribution. -/
def firstCoordinateMoment (mass : ℕ → ℕ → ℚ) (N K : ℕ) : ℚ :=
  (List.range (N + 1)).foldl
    (fun total (n : ℕ) =>
      total + (List.range (K + 1)).foldl
        (fun row (k : ℕ) => row + (n : ℚ) * mass n k) 0) 0

theorem diagonalPointMass_firstMoment :
    firstCoordinateMoment diagonalPointMass 3 3 = 0 := by
  unfold firstCoordinateMoment diagonalPointMass
  native_decide

/-- Product-form table for independent finite laws. -/
def productMass (a b : ℕ → ℚ) (n k : ℕ) : ℚ :=
  a n * b k

theorem productMass_point_total :
    bivariateMassTotal (productMass (fun n => if n = 0 then 1 else 0)
      (fun k => if k = 0 then 1 else 0)) 3 3 = 1 := by
  unfold bivariateMassTotal productMass
  native_decide

structure MultivariateLimitWindow where
  variableWindow : ℕ
  asymptoticWindow : ℕ
  limitLawWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MultivariateLimitWindow.ready (w : MultivariateLimitWindow) : Prop :=
  0 < w.variableWindow ∧
    w.limitLawWindow ≤ w.variableWindow + w.asymptoticWindow + w.slack

def sampleMultivariateLimitWindow : MultivariateLimitWindow :=
  { variableWindow := 3, asymptoticWindow := 5,
    limitLawWindow := 9, slack := 1 }

example : sampleMultivariateLimitWindow.ready := by
  norm_num [MultivariateLimitWindow.ready, sampleMultivariateLimitWindow]

structure BudgetCertificate where
  variableWindow : ℕ
  lawWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.variableWindow ∧ c.lawWindow ≤ c.variableWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.variableWindow + c.lawWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.variableWindow + c.lawWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { variableWindow := 5, lawWindow := 6,
    certificateBudgetWindow := 12, slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled,
      sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled,
      sampleBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

def budgetCertificateListReady (data : List BudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch9.MultivariateAsymptoticsAndLimitLaws
