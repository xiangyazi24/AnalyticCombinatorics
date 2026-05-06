import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform residue transfer models.

The finite schema records residue windows, contour budgets, and
uniformity slack.
-/

namespace AnalyticCombinatorics.AppB.UniformResidueTransferModels

structure UniformResidueTransferData where
  residueWindow : ℕ
  contourBudget : ℕ
  uniformitySlack : ℕ
deriving DecidableEq, Repr

def contourBudgetPositive (d : UniformResidueTransferData) : Prop :=
  0 < d.contourBudget

def residueWindowControlled (d : UniformResidueTransferData) : Prop :=
  d.residueWindow ≤ d.contourBudget + d.uniformitySlack

def uniformResidueTransferReady
    (d : UniformResidueTransferData) : Prop :=
  contourBudgetPositive d ∧ residueWindowControlled d

def uniformResidueTransferBudget
    (d : UniformResidueTransferData) : ℕ :=
  d.residueWindow + d.contourBudget + d.uniformitySlack

theorem uniformResidueTransferReady.contour
    {d : UniformResidueTransferData}
    (h : uniformResidueTransferReady d) :
    contourBudgetPositive d ∧ residueWindowControlled d ∧
      d.residueWindow ≤ uniformResidueTransferBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold uniformResidueTransferBudget
  omega

theorem residueWindow_le_uniformResidueTransferBudget
    (d : UniformResidueTransferData) :
    d.residueWindow ≤ uniformResidueTransferBudget d := by
  unfold uniformResidueTransferBudget
  omega

def sampleUniformResidueTransferData : UniformResidueTransferData :=
  { residueWindow := 7, contourBudget := 5, uniformitySlack := 3 }

example : uniformResidueTransferReady sampleUniformResidueTransferData := by
  norm_num [uniformResidueTransferReady, contourBudgetPositive]
  norm_num [residueWindowControlled, sampleUniformResidueTransferData]

example : uniformResidueTransferBudget sampleUniformResidueTransferData = 15 := by
  native_decide


structure UniformResidueTransferModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformResidueTransferModelsBudgetCertificate.controlled
    (c : UniformResidueTransferModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformResidueTransferModelsBudgetCertificate.budgetControlled
    (c : UniformResidueTransferModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformResidueTransferModelsBudgetCertificate.Ready
    (c : UniformResidueTransferModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformResidueTransferModelsBudgetCertificate.size
    (c : UniformResidueTransferModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformResidueTransferModels_budgetCertificate_le_size
    (c : UniformResidueTransferModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformResidueTransferModelsBudgetCertificate :
    UniformResidueTransferModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformResidueTransferModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformResidueTransferModelsBudgetCertificate.controlled,
      sampleUniformResidueTransferModelsBudgetCertificate]
  · norm_num [UniformResidueTransferModelsBudgetCertificate.budgetControlled,
      sampleUniformResidueTransferModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformResidueTransferModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformResidueTransferModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformResidueTransferModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformResidueTransferModelsBudgetCertificate.controlled,
      sampleUniformResidueTransferModelsBudgetCertificate]
  · norm_num [UniformResidueTransferModelsBudgetCertificate.budgetControlled,
      sampleUniformResidueTransferModelsBudgetCertificate]

example :
    sampleUniformResidueTransferModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformResidueTransferModelsBudgetCertificate.size := by
  apply uniformResidueTransferModels_budgetCertificate_le_size
  constructor
  · norm_num [UniformResidueTransferModelsBudgetCertificate.controlled,
      sampleUniformResidueTransferModelsBudgetCertificate]
  · norm_num [UniformResidueTransferModelsBudgetCertificate.budgetControlled,
      sampleUniformResidueTransferModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List UniformResidueTransferModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformResidueTransferModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleUniformResidueTransferModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.UniformResidueTransferModels
