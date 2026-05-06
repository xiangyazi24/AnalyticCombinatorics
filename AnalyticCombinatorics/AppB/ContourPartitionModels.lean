import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Contour partition models.

The finite schema records contour pieces, junction count, and separation
slack.
-/

namespace AnalyticCombinatorics.AppB.ContourPartitionModels

structure ContourPartitionData where
  contourPieces : ℕ
  junctionCount : ℕ
  separationSlack : ℕ
deriving DecidableEq, Repr

def contourPiecesPositive (d : ContourPartitionData) : Prop :=
  0 < d.contourPieces

def junctionsControlled (d : ContourPartitionData) : Prop :=
  d.junctionCount ≤ d.contourPieces + d.separationSlack

def contourPartitionReady (d : ContourPartitionData) : Prop :=
  contourPiecesPositive d ∧ junctionsControlled d

def contourPartitionBudget (d : ContourPartitionData) : ℕ :=
  d.contourPieces + d.junctionCount + d.separationSlack

theorem contourPartitionReady.pieces {d : ContourPartitionData}
    (h : contourPartitionReady d) :
    contourPiecesPositive d ∧ junctionsControlled d ∧
      d.junctionCount ≤ contourPartitionBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold contourPartitionBudget
  omega

theorem junctionCount_le_contourPartitionBudget
    (d : ContourPartitionData) :
    d.junctionCount ≤ contourPartitionBudget d := by
  unfold contourPartitionBudget
  omega

def sampleContourPartitionData : ContourPartitionData :=
  { contourPieces := 6, junctionCount := 8, separationSlack := 3 }

example : contourPartitionReady sampleContourPartitionData := by
  norm_num [contourPartitionReady, contourPiecesPositive]
  norm_num [junctionsControlled, sampleContourPartitionData]

example : contourPartitionBudget sampleContourPartitionData = 17 := by
  native_decide


structure ContourPartitionModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ContourPartitionModelsBudgetCertificate.controlled
    (c : ContourPartitionModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ContourPartitionModelsBudgetCertificate.budgetControlled
    (c : ContourPartitionModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ContourPartitionModelsBudgetCertificate.Ready
    (c : ContourPartitionModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ContourPartitionModelsBudgetCertificate.size
    (c : ContourPartitionModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem contourPartitionModels_budgetCertificate_le_size
    (c : ContourPartitionModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleContourPartitionModelsBudgetCertificate :
    ContourPartitionModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleContourPartitionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [ContourPartitionModelsBudgetCertificate.controlled,
      sampleContourPartitionModelsBudgetCertificate]
  · norm_num [ContourPartitionModelsBudgetCertificate.budgetControlled,
      sampleContourPartitionModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleContourPartitionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleContourPartitionModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleContourPartitionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [ContourPartitionModelsBudgetCertificate.controlled,
      sampleContourPartitionModelsBudgetCertificate]
  · norm_num [ContourPartitionModelsBudgetCertificate.budgetControlled,
      sampleContourPartitionModelsBudgetCertificate]

example :
    sampleContourPartitionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleContourPartitionModelsBudgetCertificate.size := by
  apply contourPartitionModels_budgetCertificate_le_size
  constructor
  · norm_num [ContourPartitionModelsBudgetCertificate.controlled,
      sampleContourPartitionModelsBudgetCertificate]
  · norm_num [ContourPartitionModelsBudgetCertificate.budgetControlled,
      sampleContourPartitionModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List ContourPartitionModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleContourPartitionModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleContourPartitionModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.ContourPartitionModels
