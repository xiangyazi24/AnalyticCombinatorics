import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform pole separation models.

This module records finite bookkeeping for pole separation windows.
-/

namespace AnalyticCombinatorics.AppB.UniformPoleSeparationModels

structure PoleSeparationData where
  poleCount : ℕ
  separationWindow : ℕ
  marginSlack : ℕ
deriving DecidableEq, Repr

def hasPoleCount (d : PoleSeparationData) : Prop :=
  0 < d.poleCount

def separationWindowControlled (d : PoleSeparationData) : Prop :=
  d.separationWindow ≤ d.poleCount + d.marginSlack

def poleSeparationReady (d : PoleSeparationData) : Prop :=
  hasPoleCount d ∧ separationWindowControlled d

def poleSeparationBudget (d : PoleSeparationData) : ℕ :=
  d.poleCount + d.separationWindow + d.marginSlack

theorem poleSeparationReady.hasPoleCount {d : PoleSeparationData}
    (h : poleSeparationReady d) :
    hasPoleCount d ∧ separationWindowControlled d ∧
      d.separationWindow ≤ poleSeparationBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold poleSeparationBudget
  omega

theorem separationWindow_le_budget (d : PoleSeparationData) :
    d.separationWindow ≤ poleSeparationBudget d := by
  unfold poleSeparationBudget
  omega

def samplePoleSeparationData : PoleSeparationData :=
  { poleCount := 6, separationWindow := 8, marginSlack := 3 }

example : poleSeparationReady samplePoleSeparationData := by
  norm_num [poleSeparationReady, hasPoleCount]
  norm_num [separationWindowControlled, samplePoleSeparationData]

example : poleSeparationBudget samplePoleSeparationData = 17 := by
  native_decide

structure UniformPoleSeparationWindow where
  poleWindow : ℕ
  separationWindow : ℕ
  marginSlack : ℕ
  separationBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformPoleSeparationWindow.separationControlled
    (w : UniformPoleSeparationWindow) : Prop :=
  w.separationWindow ≤ w.poleWindow + w.marginSlack + w.slack

def uniformPoleSeparationWindowReady (w : UniformPoleSeparationWindow) : Prop :=
  0 < w.poleWindow ∧ w.separationControlled ∧
    w.separationBudget ≤ w.poleWindow + w.separationWindow + w.slack

def UniformPoleSeparationWindow.certificate (w : UniformPoleSeparationWindow) : ℕ :=
  w.poleWindow + w.separationWindow + w.marginSlack + w.separationBudget + w.slack

theorem uniformPoleSeparation_separationBudget_le_certificate
    (w : UniformPoleSeparationWindow) :
    w.separationBudget ≤ w.certificate := by
  unfold UniformPoleSeparationWindow.certificate
  omega

def sampleUniformPoleSeparationWindow : UniformPoleSeparationWindow :=
  { poleWindow := 5, separationWindow := 7, marginSlack := 2,
    separationBudget := 14, slack := 2 }

example : uniformPoleSeparationWindowReady sampleUniformPoleSeparationWindow := by
  norm_num [uniformPoleSeparationWindowReady,
    UniformPoleSeparationWindow.separationControlled, sampleUniformPoleSeparationWindow]


structure UniformPoleSeparationModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformPoleSeparationModelsBudgetCertificate.controlled
    (c : UniformPoleSeparationModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformPoleSeparationModelsBudgetCertificate.budgetControlled
    (c : UniformPoleSeparationModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformPoleSeparationModelsBudgetCertificate.Ready
    (c : UniformPoleSeparationModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformPoleSeparationModelsBudgetCertificate.size
    (c : UniformPoleSeparationModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformPoleSeparationModels_budgetCertificate_le_size
    (c : UniformPoleSeparationModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformPoleSeparationModelsBudgetCertificate :
    UniformPoleSeparationModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformPoleSeparationModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformPoleSeparationModelsBudgetCertificate.controlled,
      sampleUniformPoleSeparationModelsBudgetCertificate]
  · norm_num [UniformPoleSeparationModelsBudgetCertificate.budgetControlled,
      sampleUniformPoleSeparationModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformPoleSeparationModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformPoleSeparationModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformPoleSeparationModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformPoleSeparationModelsBudgetCertificate.controlled,
      sampleUniformPoleSeparationModelsBudgetCertificate]
  · norm_num [UniformPoleSeparationModelsBudgetCertificate.budgetControlled,
      sampleUniformPoleSeparationModelsBudgetCertificate]

example :
    sampleUniformPoleSeparationModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformPoleSeparationModelsBudgetCertificate.size := by
  apply uniformPoleSeparationModels_budgetCertificate_le_size
  constructor
  · norm_num [UniformPoleSeparationModelsBudgetCertificate.controlled,
      sampleUniformPoleSeparationModelsBudgetCertificate]
  · norm_num [UniformPoleSeparationModelsBudgetCertificate.budgetControlled,
      sampleUniformPoleSeparationModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List UniformPoleSeparationModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformPoleSeparationModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleUniformPoleSeparationModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.UniformPoleSeparationModels
