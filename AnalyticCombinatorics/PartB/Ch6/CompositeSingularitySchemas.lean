import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Composite singularity schemas.

The finite abstraction records outer singular order, inner singular
order, and composition slack.
-/

namespace AnalyticCombinatorics.PartB.Ch6.CompositeSingularitySchemas

structure CompositeSingularityData where
  outerOrder : ℕ
  innerOrder : ℕ
  compositionSlack : ℕ
deriving DecidableEq, Repr

def outerOrderPositive (d : CompositeSingularityData) : Prop :=
  0 < d.outerOrder

def innerOrderControlled (d : CompositeSingularityData) : Prop :=
  d.innerOrder ≤ d.outerOrder + d.compositionSlack

def compositeSingularityReady (d : CompositeSingularityData) : Prop :=
  outerOrderPositive d ∧ innerOrderControlled d

def compositeSingularityBudget (d : CompositeSingularityData) : ℕ :=
  d.outerOrder + d.innerOrder + d.compositionSlack

theorem compositeSingularityReady.outer {d : CompositeSingularityData}
    (h : compositeSingularityReady d) :
    outerOrderPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem innerOrder_le_compositeBudget (d : CompositeSingularityData) :
    d.innerOrder ≤ compositeSingularityBudget d := by
  unfold compositeSingularityBudget
  omega

def sampleCompositeSingularityData : CompositeSingularityData :=
  { outerOrder := 4, innerOrder := 6, compositionSlack := 3 }

example : compositeSingularityReady sampleCompositeSingularityData := by
  norm_num [compositeSingularityReady, outerOrderPositive]
  norm_num [innerOrderControlled, sampleCompositeSingularityData]

example : compositeSingularityBudget sampleCompositeSingularityData = 13 := by
  native_decide

structure CompositeSingularityWindow where
  outerOrder : ℕ
  innerOrder : ℕ
  compositionSlack : ℕ
  transferBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CompositeSingularityWindow.innerControlled (w : CompositeSingularityWindow) : Prop :=
  w.innerOrder ≤ w.outerOrder + w.compositionSlack + w.slack

def CompositeSingularityWindow.transferControlled (w : CompositeSingularityWindow) : Prop :=
  w.transferBudget ≤ w.outerOrder + w.innerOrder + w.compositionSlack + w.slack

def compositeSingularityWindowReady (w : CompositeSingularityWindow) : Prop :=
  0 < w.outerOrder ∧
    w.innerControlled ∧
    w.transferControlled

def CompositeSingularityWindow.certificate (w : CompositeSingularityWindow) : ℕ :=
  w.outerOrder + w.innerOrder + w.compositionSlack + w.slack

theorem compositeSingularity_transferBudget_le_certificate {w : CompositeSingularityWindow}
    (h : compositeSingularityWindowReady w) :
    w.transferBudget ≤ w.certificate := by
  rcases h with ⟨_, _, htransfer⟩
  exact htransfer

def sampleCompositeSingularityWindow : CompositeSingularityWindow :=
  { outerOrder := 4, innerOrder := 6, compositionSlack := 3, transferBudget := 12, slack := 0 }

example : compositeSingularityWindowReady sampleCompositeSingularityWindow := by
  norm_num [compositeSingularityWindowReady, CompositeSingularityWindow.innerControlled,
    CompositeSingularityWindow.transferControlled, sampleCompositeSingularityWindow]

example : sampleCompositeSingularityWindow.certificate = 13 := by
  native_decide


structure CompositeSingularitySchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CompositeSingularitySchemasBudgetCertificate.controlled
    (c : CompositeSingularitySchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CompositeSingularitySchemasBudgetCertificate.budgetControlled
    (c : CompositeSingularitySchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CompositeSingularitySchemasBudgetCertificate.Ready
    (c : CompositeSingularitySchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CompositeSingularitySchemasBudgetCertificate.size
    (c : CompositeSingularitySchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem compositeSingularitySchemas_budgetCertificate_le_size
    (c : CompositeSingularitySchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCompositeSingularitySchemasBudgetCertificate :
    CompositeSingularitySchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCompositeSingularitySchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CompositeSingularitySchemasBudgetCertificate.controlled,
      sampleCompositeSingularitySchemasBudgetCertificate]
  · norm_num [CompositeSingularitySchemasBudgetCertificate.budgetControlled,
      sampleCompositeSingularitySchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCompositeSingularitySchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCompositeSingularitySchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleCompositeSingularitySchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CompositeSingularitySchemasBudgetCertificate.controlled,
      sampleCompositeSingularitySchemasBudgetCertificate]
  · norm_num [CompositeSingularitySchemasBudgetCertificate.budgetControlled,
      sampleCompositeSingularitySchemasBudgetCertificate]

example :
    sampleCompositeSingularitySchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCompositeSingularitySchemasBudgetCertificate.size := by
  apply compositeSingularitySchemas_budgetCertificate_le_size
  constructor
  · norm_num [CompositeSingularitySchemasBudgetCertificate.controlled,
      sampleCompositeSingularitySchemasBudgetCertificate]
  · norm_num [CompositeSingularitySchemasBudgetCertificate.budgetControlled,
      sampleCompositeSingularitySchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List CompositeSingularitySchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCompositeSingularitySchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCompositeSingularitySchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.CompositeSingularitySchemas
