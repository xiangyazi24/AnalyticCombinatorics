import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Truncated moment schema bookkeeping.

The finite data records truncation cutoff, moment order, and residual
budget.
-/

namespace AnalyticCombinatorics.AppC.TruncatedMomentSchemas

structure TruncatedMomentData where
  cutoff : ℕ
  momentOrder : ℕ
  residualBudget : ℕ
deriving DecidableEq, Repr

def positiveCutoff (d : TruncatedMomentData) : Prop :=
  0 < d.cutoff

def positiveMomentOrder (d : TruncatedMomentData) : Prop :=
  0 < d.momentOrder

def truncatedMomentReady (d : TruncatedMomentData) : Prop :=
  positiveCutoff d ∧ positiveMomentOrder d

def truncatedMomentBudget (d : TruncatedMomentData) : ℕ :=
  d.cutoff * d.momentOrder + d.residualBudget

theorem truncatedMomentReady.order {d : TruncatedMomentData}
    (h : truncatedMomentReady d) :
    positiveMomentOrder d := by
  rcases h with ⟨hleft, hright⟩
  exact hright

theorem residualBudget_le_total (d : TruncatedMomentData) :
    d.residualBudget ≤ truncatedMomentBudget d := by
  unfold truncatedMomentBudget
  omega

def sampleTruncatedMoment : TruncatedMomentData :=
  { cutoff := 4, momentOrder := 3, residualBudget := 2 }

example : truncatedMomentReady sampleTruncatedMoment := by
  norm_num [truncatedMomentReady, positiveCutoff, positiveMomentOrder, sampleTruncatedMoment]

example : truncatedMomentBudget sampleTruncatedMoment = 14 := by
  native_decide

structure TruncatedMomentWindow where
  cutoff : ℕ
  momentOrder : ℕ
  residualBudget : ℕ
  truncatedMass : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TruncatedMomentWindow.positiveReady (w : TruncatedMomentWindow) : Prop :=
  0 < w.cutoff ∧ 0 < w.momentOrder

def TruncatedMomentWindow.massControlled (w : TruncatedMomentWindow) : Prop :=
  w.truncatedMass ≤ w.cutoff * w.momentOrder + w.residualBudget + w.slack

def TruncatedMomentWindow.ready (w : TruncatedMomentWindow) : Prop :=
  w.positiveReady ∧ w.massControlled

def TruncatedMomentWindow.certificate (w : TruncatedMomentWindow) : ℕ :=
  w.cutoff + w.momentOrder + w.residualBudget + w.truncatedMass + w.slack

theorem truncatedMass_le_certificate (w : TruncatedMomentWindow) :
    w.truncatedMass ≤ w.certificate := by
  unfold TruncatedMomentWindow.certificate
  omega

def sampleTruncatedMomentWindow : TruncatedMomentWindow :=
  { cutoff := 4, momentOrder := 3, residualBudget := 2, truncatedMass := 12, slack := 0 }

example : sampleTruncatedMomentWindow.ready := by
  norm_num [sampleTruncatedMomentWindow, TruncatedMomentWindow.ready,
    TruncatedMomentWindow.positiveReady, TruncatedMomentWindow.massControlled]

structure TruncatedMomentRefinementWindow where
  cutoffWindow : ℕ
  orderWindow : ℕ
  residualWindow : ℕ
  truncatedWindow : ℕ
  momentBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TruncatedMomentRefinementWindow.massControlled
    (w : TruncatedMomentRefinementWindow) : Prop :=
  w.truncatedWindow ≤ w.cutoffWindow * w.orderWindow + w.residualWindow + w.slack

def truncatedMomentRefinementWindowReady
    (w : TruncatedMomentRefinementWindow) : Prop :=
  0 < w.cutoffWindow ∧ 0 < w.orderWindow ∧ w.massControlled ∧
    w.momentBudget ≤ w.cutoffWindow + w.orderWindow + w.truncatedWindow + w.slack

def TruncatedMomentRefinementWindow.certificate
    (w : TruncatedMomentRefinementWindow) : ℕ :=
  w.cutoffWindow + w.orderWindow + w.residualWindow + w.truncatedWindow +
    w.momentBudget + w.slack

theorem truncatedMomentRefinement_budget_le_certificate
    (w : TruncatedMomentRefinementWindow) :
    w.momentBudget ≤ w.certificate := by
  unfold TruncatedMomentRefinementWindow.certificate
  omega

def sampleTruncatedMomentRefinementWindow :
    TruncatedMomentRefinementWindow :=
  { cutoffWindow := 4, orderWindow := 3, residualWindow := 2,
    truncatedWindow := 12, momentBudget := 20, slack := 1 }

example : truncatedMomentRefinementWindowReady
    sampleTruncatedMomentRefinementWindow := by
  norm_num [truncatedMomentRefinementWindowReady,
    TruncatedMomentRefinementWindow.massControlled, sampleTruncatedMomentRefinementWindow]


structure TruncatedMomentSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TruncatedMomentSchemasBudgetCertificate.controlled
    (c : TruncatedMomentSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def TruncatedMomentSchemasBudgetCertificate.budgetControlled
    (c : TruncatedMomentSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def TruncatedMomentSchemasBudgetCertificate.Ready
    (c : TruncatedMomentSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TruncatedMomentSchemasBudgetCertificate.size
    (c : TruncatedMomentSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem truncatedMomentSchemas_budgetCertificate_le_size
    (c : TruncatedMomentSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleTruncatedMomentSchemasBudgetCertificate :
    TruncatedMomentSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleTruncatedMomentSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [TruncatedMomentSchemasBudgetCertificate.controlled,
      sampleTruncatedMomentSchemasBudgetCertificate]
  · norm_num [TruncatedMomentSchemasBudgetCertificate.budgetControlled,
      sampleTruncatedMomentSchemasBudgetCertificate]

example :
    sampleTruncatedMomentSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleTruncatedMomentSchemasBudgetCertificate.size := by
  apply truncatedMomentSchemas_budgetCertificate_le_size
  constructor
  · norm_num [TruncatedMomentSchemasBudgetCertificate.controlled,
      sampleTruncatedMomentSchemasBudgetCertificate]
  · norm_num [TruncatedMomentSchemasBudgetCertificate.budgetControlled,
      sampleTruncatedMomentSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleTruncatedMomentSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [TruncatedMomentSchemasBudgetCertificate.controlled,
      sampleTruncatedMomentSchemasBudgetCertificate]
  · norm_num [TruncatedMomentSchemasBudgetCertificate.budgetControlled,
      sampleTruncatedMomentSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleTruncatedMomentSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleTruncatedMomentSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List TruncatedMomentSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleTruncatedMomentSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleTruncatedMomentSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.TruncatedMomentSchemas
