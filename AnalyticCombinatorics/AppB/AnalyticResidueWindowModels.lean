import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic residue window models.

The finite abstraction records residue order, coefficient window, and
annular slack.
-/

namespace AnalyticCombinatorics.AppB.AnalyticResidueWindowModels

structure AnalyticResidueWindowData where
  residueOrder : ℕ
  coefficientWindow : ℕ
  annularSlack : ℕ
deriving DecidableEq, Repr

def residueOrderPositive (d : AnalyticResidueWindowData) : Prop :=
  0 < d.residueOrder

def coefficientWindowControlled (d : AnalyticResidueWindowData) : Prop :=
  d.coefficientWindow ≤ d.residueOrder + d.annularSlack

def analyticResidueWindowReady (d : AnalyticResidueWindowData) : Prop :=
  residueOrderPositive d ∧ coefficientWindowControlled d

def analyticResidueWindowBudget (d : AnalyticResidueWindowData) : ℕ :=
  d.residueOrder + d.coefficientWindow + d.annularSlack

theorem analyticResidueWindowReady.order
    {d : AnalyticResidueWindowData}
    (h : analyticResidueWindowReady d) :
    residueOrderPositive d ∧ coefficientWindowControlled d ∧
      d.coefficientWindow ≤ analyticResidueWindowBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold analyticResidueWindowBudget
  omega

theorem coefficientWindow_le_residueWindowBudget
    (d : AnalyticResidueWindowData) :
    d.coefficientWindow ≤ analyticResidueWindowBudget d := by
  unfold analyticResidueWindowBudget
  omega

def sampleAnalyticResidueWindowData : AnalyticResidueWindowData :=
  { residueOrder := 4, coefficientWindow := 6, annularSlack := 3 }

example : analyticResidueWindowReady sampleAnalyticResidueWindowData := by
  norm_num [analyticResidueWindowReady, residueOrderPositive]
  norm_num [coefficientWindowControlled, sampleAnalyticResidueWindowData]

example : analyticResidueWindowBudget sampleAnalyticResidueWindowData = 13 := by
  native_decide


structure AnalyticResidueWindowModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticResidueWindowModelsBudgetCertificate.controlled
    (c : AnalyticResidueWindowModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticResidueWindowModelsBudgetCertificate.budgetControlled
    (c : AnalyticResidueWindowModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticResidueWindowModelsBudgetCertificate.Ready
    (c : AnalyticResidueWindowModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticResidueWindowModelsBudgetCertificate.size
    (c : AnalyticResidueWindowModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticResidueWindowModels_budgetCertificate_le_size
    (c : AnalyticResidueWindowModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticResidueWindowModelsBudgetCertificate :
    AnalyticResidueWindowModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticResidueWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticResidueWindowModelsBudgetCertificate.controlled,
      sampleAnalyticResidueWindowModelsBudgetCertificate]
  · norm_num [AnalyticResidueWindowModelsBudgetCertificate.budgetControlled,
      sampleAnalyticResidueWindowModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticResidueWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticResidueWindowModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticResidueWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticResidueWindowModelsBudgetCertificate.controlled,
      sampleAnalyticResidueWindowModelsBudgetCertificate]
  · norm_num [AnalyticResidueWindowModelsBudgetCertificate.budgetControlled,
      sampleAnalyticResidueWindowModelsBudgetCertificate]

example :
    sampleAnalyticResidueWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticResidueWindowModelsBudgetCertificate.size := by
  apply analyticResidueWindowModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticResidueWindowModelsBudgetCertificate.controlled,
      sampleAnalyticResidueWindowModelsBudgetCertificate]
  · norm_num [AnalyticResidueWindowModelsBudgetCertificate.budgetControlled,
      sampleAnalyticResidueWindowModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AnalyticResidueWindowModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticResidueWindowModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticResidueWindowModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.AnalyticResidueWindowModels
