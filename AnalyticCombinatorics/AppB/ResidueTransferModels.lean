import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Residue transfer models.

The finite schema records residue count, coefficient window, and contour
slack.
-/

namespace AnalyticCombinatorics.AppB.ResidueTransferModels

structure ResidueTransferData where
  residueCount : ℕ
  coefficientWindow : ℕ
  contourSlack : ℕ
deriving DecidableEq, Repr

def residueCountPositive (d : ResidueTransferData) : Prop :=
  0 < d.residueCount

def coefficientWindowControlled (d : ResidueTransferData) : Prop :=
  d.coefficientWindow ≤ d.residueCount + d.contourSlack

def residueTransferReady (d : ResidueTransferData) : Prop :=
  residueCountPositive d ∧ coefficientWindowControlled d

def residueTransferBudget (d : ResidueTransferData) : ℕ :=
  d.residueCount + d.coefficientWindow + d.contourSlack

theorem residueTransferReady.residues {d : ResidueTransferData}
    (h : residueTransferReady d) :
    residueCountPositive d ∧ coefficientWindowControlled d ∧
      d.coefficientWindow ≤ residueTransferBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold residueTransferBudget
  omega

theorem coefficientWindow_le_residueTransferBudget
    (d : ResidueTransferData) :
    d.coefficientWindow ≤ residueTransferBudget d := by
  unfold residueTransferBudget
  omega

def sampleResidueTransferData : ResidueTransferData :=
  { residueCount := 4, coefficientWindow := 6, contourSlack := 3 }

example : residueTransferReady sampleResidueTransferData := by
  norm_num [residueTransferReady, residueCountPositive]
  norm_num [coefficientWindowControlled, sampleResidueTransferData]

example : residueTransferBudget sampleResidueTransferData = 13 := by
  native_decide


structure ResidueTransferModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ResidueTransferModelsBudgetCertificate.controlled
    (c : ResidueTransferModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ResidueTransferModelsBudgetCertificate.budgetControlled
    (c : ResidueTransferModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ResidueTransferModelsBudgetCertificate.Ready
    (c : ResidueTransferModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ResidueTransferModelsBudgetCertificate.size
    (c : ResidueTransferModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem residueTransferModels_budgetCertificate_le_size
    (c : ResidueTransferModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleResidueTransferModelsBudgetCertificate :
    ResidueTransferModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleResidueTransferModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [ResidueTransferModelsBudgetCertificate.controlled,
      sampleResidueTransferModelsBudgetCertificate]
  · norm_num [ResidueTransferModelsBudgetCertificate.budgetControlled,
      sampleResidueTransferModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleResidueTransferModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleResidueTransferModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleResidueTransferModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [ResidueTransferModelsBudgetCertificate.controlled,
      sampleResidueTransferModelsBudgetCertificate]
  · norm_num [ResidueTransferModelsBudgetCertificate.budgetControlled,
      sampleResidueTransferModelsBudgetCertificate]

example :
    sampleResidueTransferModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleResidueTransferModelsBudgetCertificate.size := by
  apply residueTransferModels_budgetCertificate_le_size
  constructor
  · norm_num [ResidueTransferModelsBudgetCertificate.controlled,
      sampleResidueTransferModelsBudgetCertificate]
  · norm_num [ResidueTransferModelsBudgetCertificate.budgetControlled,
      sampleResidueTransferModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List ResidueTransferModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleResidueTransferModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleResidueTransferModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.ResidueTransferModels
