import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Multiple-point transfer schemas.

The finite record tracks the number of dominant points, local orders, and
aggregate remainder budgets.
-/

namespace AnalyticCombinatorics.PartB.Ch6.MultiplePointTransferSchemas

structure MultiplePointData where
  pointCount : ℕ
  localOrder : ℕ
  remainderBudget : ℕ
deriving DecidableEq, Repr

def hasDominantPoint (d : MultiplePointData) : Prop :=
  0 < d.pointCount

def positiveLocalOrder (d : MultiplePointData) : Prop :=
  0 < d.localOrder

def multiplePointReady (d : MultiplePointData) : Prop :=
  hasDominantPoint d ∧ positiveLocalOrder d

def totalLocalContribution (d : MultiplePointData) : ℕ :=
  d.pointCount * d.localOrder + d.remainderBudget

theorem multiplePointReady.points {d : MultiplePointData}
    (h : multiplePointReady d) :
    hasDominantPoint d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem totalLocalContribution_ge_remainder (d : MultiplePointData) :
    d.remainderBudget ≤ totalLocalContribution d := by
  unfold totalLocalContribution
  omega

def sampleMultiplePoint : MultiplePointData :=
  { pointCount := 3, localOrder := 2, remainderBudget := 4 }

example : multiplePointReady sampleMultiplePoint := by
  norm_num [multiplePointReady, hasDominantPoint, positiveLocalOrder, sampleMultiplePoint]

example : totalLocalContribution sampleMultiplePoint = 10 := by
  native_decide

structure MultiplePointWindow where
  pointCount : ℕ
  localOrder : ℕ
  remainderBudget : ℕ
  contributionMass : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MultiplePointWindow.contributionControlled (w : MultiplePointWindow) : Prop :=
  w.contributionMass ≤ w.pointCount * w.localOrder + w.remainderBudget + w.slack

def multiplePointWindowReady (w : MultiplePointWindow) : Prop :=
  0 < w.pointCount ∧
    0 < w.localOrder ∧
    w.contributionControlled

def MultiplePointWindow.certificate (w : MultiplePointWindow) : ℕ :=
  w.pointCount * w.localOrder + w.remainderBudget + w.slack

theorem multiplePoint_contributionMass_le_certificate {w : MultiplePointWindow}
    (h : multiplePointWindowReady w) :
    w.contributionMass ≤ w.certificate := by
  rcases h with ⟨_, _, hmass⟩
  exact hmass

def sampleMultiplePointWindow : MultiplePointWindow :=
  { pointCount := 3, localOrder := 2, remainderBudget := 4, contributionMass := 10, slack := 0 }

example : multiplePointWindowReady sampleMultiplePointWindow := by
  norm_num [multiplePointWindowReady, MultiplePointWindow.contributionControlled,
    sampleMultiplePointWindow]

example : sampleMultiplePointWindow.certificate = 10 := by
  native_decide


structure MultiplePointTransferSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MultiplePointTransferSchemasBudgetCertificate.controlled
    (c : MultiplePointTransferSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MultiplePointTransferSchemasBudgetCertificate.budgetControlled
    (c : MultiplePointTransferSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MultiplePointTransferSchemasBudgetCertificate.Ready
    (c : MultiplePointTransferSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MultiplePointTransferSchemasBudgetCertificate.size
    (c : MultiplePointTransferSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem multiplePointTransferSchemas_budgetCertificate_le_size
    (c : MultiplePointTransferSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMultiplePointTransferSchemasBudgetCertificate :
    MultiplePointTransferSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleMultiplePointTransferSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MultiplePointTransferSchemasBudgetCertificate.controlled,
      sampleMultiplePointTransferSchemasBudgetCertificate]
  · norm_num [MultiplePointTransferSchemasBudgetCertificate.budgetControlled,
      sampleMultiplePointTransferSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMultiplePointTransferSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMultiplePointTransferSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleMultiplePointTransferSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MultiplePointTransferSchemasBudgetCertificate.controlled,
      sampleMultiplePointTransferSchemasBudgetCertificate]
  · norm_num [MultiplePointTransferSchemasBudgetCertificate.budgetControlled,
      sampleMultiplePointTransferSchemasBudgetCertificate]

example :
    sampleMultiplePointTransferSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMultiplePointTransferSchemasBudgetCertificate.size := by
  apply multiplePointTransferSchemas_budgetCertificate_le_size
  constructor
  · norm_num [MultiplePointTransferSchemasBudgetCertificate.controlled,
      sampleMultiplePointTransferSchemasBudgetCertificate]
  · norm_num [MultiplePointTransferSchemasBudgetCertificate.budgetControlled,
      sampleMultiplePointTransferSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List MultiplePointTransferSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMultiplePointTransferSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMultiplePointTransferSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.MultiplePointTransferSchemas
