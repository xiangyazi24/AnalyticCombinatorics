import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform argument principle window models.

This module records finite bookkeeping for uniform argument principle windows.
-/

namespace AnalyticCombinatorics.AppB.UniformArgumentPrincipleWindowModels

structure ArgumentPrincipleWindowData where
  contourTurns : ℕ
  argumentWindow : ℕ
  contourSlack : ℕ
deriving DecidableEq, Repr

def hasContourTurns (d : ArgumentPrincipleWindowData) : Prop :=
  0 < d.contourTurns

def argumentWindowControlled
    (d : ArgumentPrincipleWindowData) : Prop :=
  d.argumentWindow ≤ d.contourTurns + d.contourSlack

def argumentPrincipleWindowReady
    (d : ArgumentPrincipleWindowData) : Prop :=
  hasContourTurns d ∧ argumentWindowControlled d

def argumentPrincipleWindowBudget
    (d : ArgumentPrincipleWindowData) : ℕ :=
  d.contourTurns + d.argumentWindow + d.contourSlack

theorem argumentPrincipleWindowReady.hasContourTurns
    {d : ArgumentPrincipleWindowData}
    (h : argumentPrincipleWindowReady d) :
    hasContourTurns d ∧ argumentWindowControlled d ∧
      d.argumentWindow ≤ argumentPrincipleWindowBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold argumentPrincipleWindowBudget
  omega

theorem argumentWindow_le_budget
    (d : ArgumentPrincipleWindowData) :
    d.argumentWindow ≤ argumentPrincipleWindowBudget d := by
  unfold argumentPrincipleWindowBudget
  omega

def sampleArgumentPrincipleWindowData :
    ArgumentPrincipleWindowData :=
  { contourTurns := 5, argumentWindow := 7, contourSlack := 2 }

example : argumentPrincipleWindowReady
    sampleArgumentPrincipleWindowData := by
  norm_num [argumentPrincipleWindowReady, hasContourTurns]
  norm_num [argumentWindowControlled, sampleArgumentPrincipleWindowData]

example :
    argumentPrincipleWindowBudget sampleArgumentPrincipleWindowData = 14 := by
  native_decide


structure UniformArgumentPrincipleWindowModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformArgumentPrincipleWindowModelsBudgetCertificate.controlled
    (c : UniformArgumentPrincipleWindowModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformArgumentPrincipleWindowModelsBudgetCertificate.budgetControlled
    (c : UniformArgumentPrincipleWindowModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformArgumentPrincipleWindowModelsBudgetCertificate.Ready
    (c : UniformArgumentPrincipleWindowModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformArgumentPrincipleWindowModelsBudgetCertificate.size
    (c : UniformArgumentPrincipleWindowModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformArgumentPrincipleWindowModels_budgetCertificate_le_size
    (c : UniformArgumentPrincipleWindowModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformArgumentPrincipleWindowModelsBudgetCertificate :
    UniformArgumentPrincipleWindowModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformArgumentPrincipleWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformArgumentPrincipleWindowModelsBudgetCertificate.controlled,
      sampleUniformArgumentPrincipleWindowModelsBudgetCertificate]
  · norm_num [UniformArgumentPrincipleWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformArgumentPrincipleWindowModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformArgumentPrincipleWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformArgumentPrincipleWindowModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformArgumentPrincipleWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformArgumentPrincipleWindowModelsBudgetCertificate.controlled,
      sampleUniformArgumentPrincipleWindowModelsBudgetCertificate]
  · norm_num [UniformArgumentPrincipleWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformArgumentPrincipleWindowModelsBudgetCertificate]

example :
    sampleUniformArgumentPrincipleWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformArgumentPrincipleWindowModelsBudgetCertificate.size := by
  apply uniformArgumentPrincipleWindowModels_budgetCertificate_le_size
  constructor
  · norm_num [UniformArgumentPrincipleWindowModelsBudgetCertificate.controlled,
      sampleUniformArgumentPrincipleWindowModelsBudgetCertificate]
  · norm_num [UniformArgumentPrincipleWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformArgumentPrincipleWindowModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List UniformArgumentPrincipleWindowModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformArgumentPrincipleWindowModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleUniformArgumentPrincipleWindowModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.UniformArgumentPrincipleWindowModels
