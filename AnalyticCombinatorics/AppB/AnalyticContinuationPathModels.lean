import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite bookkeeping for analytic-continuation paths.

The analytic content is represented by local continuation flags; this file
records how a finite chain of charts is accepted.
-/

namespace AnalyticCombinatorics.AppB.AnalyticContinuationPathModels

structure ContinuationStep where
  overlapNonempty : Prop
  singularityAvoided : Prop
  radiusBudget : ℕ
deriving Repr

def stepReady (s : ContinuationStep) : Prop :=
  s.overlapNonempty ∧ s.singularityAvoided ∧ 0 < s.radiusBudget

def pathReady (steps : List ContinuationStep) : Prop :=
  ∀ s ∈ steps, stepReady s

def totalRadiusBudget (steps : List ContinuationStep) : ℕ :=
  steps.map ContinuationStep.radiusBudget |>.sum

theorem pathReady_tail {s : ContinuationStep} {steps : List ContinuationStep}
    (h : pathReady (s :: steps)) :
    pathReady steps := by
  intro t ht
  exact h t (by simp [ht])

theorem pathReady_head {s : ContinuationStep} {steps : List ContinuationStep}
    (h : pathReady (s :: steps)) :
    stepReady s := by
  exact h s (by simp)

def sampleStep : ContinuationStep :=
  { overlapNonempty := 0 < 4, singularityAvoided := 3 ≤ 4, radiusBudget := 4 }

def samplePath : List ContinuationStep :=
  [ sampleStep
  , { overlapNonempty := 0 < 3, singularityAvoided := 2 ≤ 3, radiusBudget := 3 }
  ]

example : stepReady sampleStep := by
  norm_num [stepReady, sampleStep]

example :
    totalRadiusBudget samplePath = 7 := by
  native_decide

theorem samplePath_readyWindow :
    pathReady samplePath := by
  intro s hs
  have hs' := by
    simpa [samplePath] using hs
  rcases hs' with h | h
  · subst h
    norm_num [stepReady, sampleStep]
  · subst h
    norm_num [stepReady]


structure AnalyticContinuationPathModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticContinuationPathModelsBudgetCertificate.controlled
    (c : AnalyticContinuationPathModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticContinuationPathModelsBudgetCertificate.budgetControlled
    (c : AnalyticContinuationPathModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticContinuationPathModelsBudgetCertificate.Ready
    (c : AnalyticContinuationPathModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticContinuationPathModelsBudgetCertificate.size
    (c : AnalyticContinuationPathModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticContinuationPathModels_budgetCertificate_le_size
    (c : AnalyticContinuationPathModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticContinuationPathModelsBudgetCertificate :
    AnalyticContinuationPathModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticContinuationPathModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticContinuationPathModelsBudgetCertificate.controlled,
      sampleAnalyticContinuationPathModelsBudgetCertificate]
  · norm_num [AnalyticContinuationPathModelsBudgetCertificate.budgetControlled,
      sampleAnalyticContinuationPathModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticContinuationPathModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticContinuationPathModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticContinuationPathModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticContinuationPathModelsBudgetCertificate.controlled,
      sampleAnalyticContinuationPathModelsBudgetCertificate]
  · norm_num [AnalyticContinuationPathModelsBudgetCertificate.budgetControlled,
      sampleAnalyticContinuationPathModelsBudgetCertificate]

example :
    sampleAnalyticContinuationPathModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticContinuationPathModelsBudgetCertificate.size := by
  apply analyticContinuationPathModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticContinuationPathModelsBudgetCertificate.controlled,
      sampleAnalyticContinuationPathModelsBudgetCertificate]
  · norm_num [AnalyticContinuationPathModelsBudgetCertificate.budgetControlled,
      sampleAnalyticContinuationPathModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List AnalyticContinuationPathModelsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticContinuationPathModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleAnalyticContinuationPathModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.AnalyticContinuationPathModels
