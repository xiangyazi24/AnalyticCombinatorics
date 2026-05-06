import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic compactness models.

The finite schema records compact pieces, cover budget, and boundary
slack.
-/

namespace AnalyticCombinatorics.AppB.AnalyticCompactnessModels

structure AnalyticCompactnessData where
  compactPieces : ℕ
  coverBudget : ℕ
  boundarySlack : ℕ
deriving DecidableEq, Repr

def compactPiecesPositive (d : AnalyticCompactnessData) : Prop :=
  0 < d.compactPieces

def coverBudgetControlled (d : AnalyticCompactnessData) : Prop :=
  d.coverBudget ≤ d.compactPieces + d.boundarySlack

def analyticCompactnessReady (d : AnalyticCompactnessData) : Prop :=
  compactPiecesPositive d ∧ coverBudgetControlled d

def analyticCompactnessBudget (d : AnalyticCompactnessData) : ℕ :=
  d.compactPieces + d.coverBudget + d.boundarySlack

theorem analyticCompactnessReady.pieces {d : AnalyticCompactnessData}
    (h : analyticCompactnessReady d) :
    compactPiecesPositive d ∧ coverBudgetControlled d ∧
      d.coverBudget ≤ analyticCompactnessBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold analyticCompactnessBudget
  omega

theorem coverBudget_le_compactnessBudget (d : AnalyticCompactnessData) :
    d.coverBudget ≤ analyticCompactnessBudget d := by
  unfold analyticCompactnessBudget
  omega

def sampleAnalyticCompactnessData : AnalyticCompactnessData :=
  { compactPieces := 5, coverBudget := 7, boundarySlack := 3 }

example : analyticCompactnessReady sampleAnalyticCompactnessData := by
  norm_num [analyticCompactnessReady, compactPiecesPositive]
  norm_num [coverBudgetControlled, sampleAnalyticCompactnessData]

example : analyticCompactnessBudget sampleAnalyticCompactnessData = 15 := by
  native_decide

/-- Finite executable readiness audit for analytic compactness windows. -/
def analyticCompactnessListReady (windows : List AnalyticCompactnessData) : Bool :=
  windows.all fun d =>
    0 < d.compactPieces && d.coverBudget ≤ d.compactPieces + d.boundarySlack

theorem analyticCompactnessList_readyWindow :
    analyticCompactnessListReady
      [{ compactPieces := 3, coverBudget := 4, boundarySlack := 1 },
       { compactPieces := 5, coverBudget := 7, boundarySlack := 3 }] = true := by
  unfold analyticCompactnessListReady
  native_decide


structure AnalyticCompactnessModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticCompactnessModelsBudgetCertificate.controlled
    (c : AnalyticCompactnessModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticCompactnessModelsBudgetCertificate.budgetControlled
    (c : AnalyticCompactnessModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticCompactnessModelsBudgetCertificate.Ready
    (c : AnalyticCompactnessModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticCompactnessModelsBudgetCertificate.size
    (c : AnalyticCompactnessModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticCompactnessModels_budgetCertificate_le_size
    (c : AnalyticCompactnessModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticCompactnessModelsBudgetCertificate :
    AnalyticCompactnessModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticCompactnessModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticCompactnessModelsBudgetCertificate.controlled,
      sampleAnalyticCompactnessModelsBudgetCertificate]
  · norm_num [AnalyticCompactnessModelsBudgetCertificate.budgetControlled,
      sampleAnalyticCompactnessModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticCompactnessModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticCompactnessModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticCompactnessModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticCompactnessModelsBudgetCertificate.controlled,
      sampleAnalyticCompactnessModelsBudgetCertificate]
  · norm_num [AnalyticCompactnessModelsBudgetCertificate.budgetControlled,
      sampleAnalyticCompactnessModelsBudgetCertificate]

example :
    sampleAnalyticCompactnessModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticCompactnessModelsBudgetCertificate.size := by
  apply analyticCompactnessModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticCompactnessModelsBudgetCertificate.controlled,
      sampleAnalyticCompactnessModelsBudgetCertificate]
  · norm_num [AnalyticCompactnessModelsBudgetCertificate.budgetControlled,
      sampleAnalyticCompactnessModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List AnalyticCompactnessModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticCompactnessModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleAnalyticCompactnessModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppB.AnalyticCompactnessModels
