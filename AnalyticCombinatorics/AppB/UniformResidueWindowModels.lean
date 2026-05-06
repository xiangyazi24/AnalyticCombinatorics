import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform residue window models.

This module records finite bookkeeping for residue windows.
-/

namespace AnalyticCombinatorics.AppB.UniformResidueWindowModels

structure ResidueWindowData where
  residueCount : ℕ
  contourWindow : ℕ
  residueSlack : ℕ
deriving DecidableEq, Repr

def hasResidueCount (d : ResidueWindowData) : Prop :=
  0 < d.residueCount

def contourWindowControlled (d : ResidueWindowData) : Prop :=
  d.contourWindow ≤ d.residueCount + d.residueSlack

def residueWindowReady (d : ResidueWindowData) : Prop :=
  hasResidueCount d ∧ contourWindowControlled d

def residueWindowBudget (d : ResidueWindowData) : ℕ :=
  d.residueCount + d.contourWindow + d.residueSlack

theorem residueWindowReady.hasResidueCount {d : ResidueWindowData}
    (h : residueWindowReady d) :
    hasResidueCount d ∧ contourWindowControlled d ∧
      d.contourWindow ≤ residueWindowBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold residueWindowBudget
  omega

theorem contourWindow_le_budget (d : ResidueWindowData) :
    d.contourWindow ≤ residueWindowBudget d := by
  unfold residueWindowBudget
  omega

def sampleResidueWindowData : ResidueWindowData :=
  { residueCount := 6, contourWindow := 8, residueSlack := 3 }

example : residueWindowReady sampleResidueWindowData := by
  norm_num [residueWindowReady, hasResidueCount]
  norm_num [contourWindowControlled, sampleResidueWindowData]

example : residueWindowBudget sampleResidueWindowData = 17 := by
  native_decide

structure UniformResidueWindow where
  residueWindow : ℕ
  contourWindow : ℕ
  residueSlack : ℕ
  contourBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformResidueWindow.contourControlled (w : UniformResidueWindow) : Prop :=
  w.contourWindow ≤ w.residueWindow + w.residueSlack + w.slack

def uniformResidueWindowReady (w : UniformResidueWindow) : Prop :=
  0 < w.residueWindow ∧ w.contourControlled ∧
    w.contourBudget ≤ w.residueWindow + w.contourWindow + w.slack

def UniformResidueWindow.certificate (w : UniformResidueWindow) : ℕ :=
  w.residueWindow + w.contourWindow + w.residueSlack + w.contourBudget + w.slack

theorem uniformResidue_contourBudget_le_certificate (w : UniformResidueWindow) :
    w.contourBudget ≤ w.certificate := by
  unfold UniformResidueWindow.certificate
  omega

def sampleUniformResidueWindow : UniformResidueWindow :=
  { residueWindow := 5, contourWindow := 7, residueSlack := 2, contourBudget := 14, slack := 2 }

example : uniformResidueWindowReady sampleUniformResidueWindow := by
  norm_num [uniformResidueWindowReady, UniformResidueWindow.contourControlled,
    sampleUniformResidueWindow]


structure UniformResidueWindowModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformResidueWindowModelsBudgetCertificate.controlled
    (c : UniformResidueWindowModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformResidueWindowModelsBudgetCertificate.budgetControlled
    (c : UniformResidueWindowModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformResidueWindowModelsBudgetCertificate.Ready
    (c : UniformResidueWindowModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformResidueWindowModelsBudgetCertificate.size
    (c : UniformResidueWindowModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformResidueWindowModels_budgetCertificate_le_size
    (c : UniformResidueWindowModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformResidueWindowModelsBudgetCertificate :
    UniformResidueWindowModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformResidueWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformResidueWindowModelsBudgetCertificate.controlled,
      sampleUniformResidueWindowModelsBudgetCertificate]
  · norm_num [UniformResidueWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformResidueWindowModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformResidueWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformResidueWindowModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformResidueWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformResidueWindowModelsBudgetCertificate.controlled,
      sampleUniformResidueWindowModelsBudgetCertificate]
  · norm_num [UniformResidueWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformResidueWindowModelsBudgetCertificate]

example :
    sampleUniformResidueWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformResidueWindowModelsBudgetCertificate.size := by
  apply uniformResidueWindowModels_budgetCertificate_le_size
  constructor
  · norm_num [UniformResidueWindowModelsBudgetCertificate.controlled,
      sampleUniformResidueWindowModelsBudgetCertificate]
  · norm_num [UniformResidueWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformResidueWindowModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List UniformResidueWindowModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformResidueWindowModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleUniformResidueWindowModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.UniformResidueWindowModels
