import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic partition models.

This finite abstraction stores partition pieces, overlap slack, and
regularity budget for analytic decompositions.
-/

namespace AnalyticCombinatorics.AppB.AnalyticPartitionModels

structure AnalyticPartitionData where
  pieces : ℕ
  overlapSlack : ℕ
  regularityBudget : ℕ
deriving DecidableEq, Repr

def piecesNonempty (d : AnalyticPartitionData) : Prop :=
  0 < d.pieces

def overlapsControlled (d : AnalyticPartitionData) : Prop :=
  d.overlapSlack ≤ d.pieces + d.regularityBudget

def analyticPartitionReady (d : AnalyticPartitionData) : Prop :=
  piecesNonempty d ∧ overlapsControlled d

def analyticPartitionBudget (d : AnalyticPartitionData) : ℕ :=
  d.pieces + d.overlapSlack + d.regularityBudget

theorem analyticPartitionReady.pieces {d : AnalyticPartitionData}
    (h : analyticPartitionReady d) :
    piecesNonempty d ∧ overlapsControlled d ∧ d.overlapSlack ≤ analyticPartitionBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold analyticPartitionBudget
  omega

theorem pieces_le_partitionBudget (d : AnalyticPartitionData) :
    d.pieces ≤ analyticPartitionBudget d := by
  unfold analyticPartitionBudget
  omega

def sampleAnalyticPartitionData : AnalyticPartitionData :=
  { pieces := 5, overlapSlack := 7, regularityBudget := 3 }

example : analyticPartitionReady sampleAnalyticPartitionData := by
  norm_num [analyticPartitionReady, piecesNonempty]
  norm_num [overlapsControlled, sampleAnalyticPartitionData]

example : analyticPartitionBudget sampleAnalyticPartitionData = 15 := by
  native_decide

structure AnalyticPartitionWindow where
  pieceWindow : ℕ
  overlapWindow : ℕ
  regularityWindow : ℕ
  partitionBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticPartitionWindow.overlapControlled (w : AnalyticPartitionWindow) : Prop :=
  w.overlapWindow ≤ w.pieceWindow + w.regularityWindow + w.slack

def analyticPartitionWindowReady (w : AnalyticPartitionWindow) : Prop :=
  0 < w.pieceWindow ∧ w.overlapControlled ∧
    w.partitionBudget ≤ w.pieceWindow + w.overlapWindow + w.slack

def AnalyticPartitionWindow.certificate (w : AnalyticPartitionWindow) : ℕ :=
  w.pieceWindow + w.overlapWindow + w.regularityWindow + w.partitionBudget + w.slack

theorem analyticPartition_partitionBudget_le_certificate (w : AnalyticPartitionWindow) :
    w.partitionBudget ≤ w.certificate := by
  unfold AnalyticPartitionWindow.certificate
  omega

def sampleAnalyticPartitionWindow : AnalyticPartitionWindow :=
  { pieceWindow := 5, overlapWindow := 6, regularityWindow := 3,
    partitionBudget := 13, slack := 2 }

example : analyticPartitionWindowReady sampleAnalyticPartitionWindow := by
  norm_num [analyticPartitionWindowReady, AnalyticPartitionWindow.overlapControlled,
    sampleAnalyticPartitionWindow]


structure AnalyticPartitionModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticPartitionModelsBudgetCertificate.controlled
    (c : AnalyticPartitionModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticPartitionModelsBudgetCertificate.budgetControlled
    (c : AnalyticPartitionModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticPartitionModelsBudgetCertificate.Ready
    (c : AnalyticPartitionModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticPartitionModelsBudgetCertificate.size
    (c : AnalyticPartitionModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticPartitionModels_budgetCertificate_le_size
    (c : AnalyticPartitionModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticPartitionModelsBudgetCertificate :
    AnalyticPartitionModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticPartitionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticPartitionModelsBudgetCertificate.controlled,
      sampleAnalyticPartitionModelsBudgetCertificate]
  · norm_num [AnalyticPartitionModelsBudgetCertificate.budgetControlled,
      sampleAnalyticPartitionModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticPartitionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticPartitionModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticPartitionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticPartitionModelsBudgetCertificate.controlled,
      sampleAnalyticPartitionModelsBudgetCertificate]
  · norm_num [AnalyticPartitionModelsBudgetCertificate.budgetControlled,
      sampleAnalyticPartitionModelsBudgetCertificate]

example :
    sampleAnalyticPartitionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticPartitionModelsBudgetCertificate.size := by
  apply analyticPartitionModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticPartitionModelsBudgetCertificate.controlled,
      sampleAnalyticPartitionModelsBudgetCertificate]
  · norm_num [AnalyticPartitionModelsBudgetCertificate.budgetControlled,
      sampleAnalyticPartitionModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AnalyticPartitionModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticPartitionModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticPartitionModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.AnalyticPartitionModels
