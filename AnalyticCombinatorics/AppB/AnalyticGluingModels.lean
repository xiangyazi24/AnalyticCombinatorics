import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic gluing models.

The finite abstraction records local pieces, compatibility checks, and
gluing slack.
-/

namespace AnalyticCombinatorics.AppB.AnalyticGluingModels

structure AnalyticGluingData where
  localPieces : ℕ
  compatibilityChecks : ℕ
  gluingSlack : ℕ
deriving DecidableEq, Repr

def localPiecesNonempty (d : AnalyticGluingData) : Prop :=
  0 < d.localPieces

def compatibilityControlled (d : AnalyticGluingData) : Prop :=
  d.compatibilityChecks ≤ d.localPieces + d.gluingSlack

def analyticGluingReady (d : AnalyticGluingData) : Prop :=
  localPiecesNonempty d ∧ compatibilityControlled d

def analyticGluingBudget (d : AnalyticGluingData) : ℕ :=
  d.localPieces + d.compatibilityChecks + d.gluingSlack

theorem analyticGluingReady.local {d : AnalyticGluingData}
    (h : analyticGluingReady d) :
    localPiecesNonempty d ∧ compatibilityControlled d ∧
      d.compatibilityChecks ≤ analyticGluingBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold analyticGluingBudget
  omega

theorem compatibility_le_gluingBudget (d : AnalyticGluingData) :
    d.compatibilityChecks ≤ analyticGluingBudget d := by
  unfold analyticGluingBudget
  omega

def sampleAnalyticGluingData : AnalyticGluingData :=
  { localPieces := 5, compatibilityChecks := 7, gluingSlack := 3 }

example : analyticGluingReady sampleAnalyticGluingData := by
  norm_num [analyticGluingReady, localPiecesNonempty]
  norm_num [compatibilityControlled, sampleAnalyticGluingData]

example : analyticGluingBudget sampleAnalyticGluingData = 15 := by
  native_decide

/-- Finite executable readiness audit for analytic gluing data. -/
def analyticGluingListReady (windows : List AnalyticGluingData) : Bool :=
  windows.all fun d =>
    0 < d.localPieces && d.compatibilityChecks ≤ d.localPieces + d.gluingSlack

theorem analyticGluingList_readyWindow :
    analyticGluingListReady
      [{ localPieces := 3, compatibilityChecks := 4, gluingSlack := 1 },
       { localPieces := 5, compatibilityChecks := 7, gluingSlack := 3 }] = true := by
  unfold analyticGluingListReady
  native_decide


structure AnalyticGluingModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticGluingModelsBudgetCertificate.controlled
    (c : AnalyticGluingModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticGluingModelsBudgetCertificate.budgetControlled
    (c : AnalyticGluingModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticGluingModelsBudgetCertificate.Ready
    (c : AnalyticGluingModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticGluingModelsBudgetCertificate.size
    (c : AnalyticGluingModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticGluingModels_budgetCertificate_le_size
    (c : AnalyticGluingModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticGluingModelsBudgetCertificate :
    AnalyticGluingModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticGluingModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticGluingModelsBudgetCertificate.controlled,
      sampleAnalyticGluingModelsBudgetCertificate]
  · norm_num [AnalyticGluingModelsBudgetCertificate.budgetControlled,
      sampleAnalyticGluingModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticGluingModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticGluingModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticGluingModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticGluingModelsBudgetCertificate.controlled,
      sampleAnalyticGluingModelsBudgetCertificate]
  · norm_num [AnalyticGluingModelsBudgetCertificate.budgetControlled,
      sampleAnalyticGluingModelsBudgetCertificate]

example :
    sampleAnalyticGluingModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticGluingModelsBudgetCertificate.size := by
  apply analyticGluingModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticGluingModelsBudgetCertificate.controlled,
      sampleAnalyticGluingModelsBudgetCertificate]
  · norm_num [AnalyticGluingModelsBudgetCertificate.budgetControlled,
      sampleAnalyticGluingModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List AnalyticGluingModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticGluingModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleAnalyticGluingModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppB.AnalyticGluingModels
