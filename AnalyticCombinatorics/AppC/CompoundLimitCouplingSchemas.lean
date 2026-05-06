import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Compound limit coupling schemas.

This module records finite bookkeeping for compound limit couplings.
-/

namespace AnalyticCombinatorics.AppC.CompoundLimitCouplingSchemas

structure CompoundLimitCouplingData where
  componentCount : ℕ
  couplingWindow : ℕ
  compoundSlack : ℕ
deriving DecidableEq, Repr

def hasComponentCount (d : CompoundLimitCouplingData) : Prop :=
  0 < d.componentCount

def couplingWindowControlled (d : CompoundLimitCouplingData) : Prop :=
  d.couplingWindow ≤ d.componentCount + d.compoundSlack

def compoundLimitCouplingReady (d : CompoundLimitCouplingData) : Prop :=
  hasComponentCount d ∧ couplingWindowControlled d

def compoundLimitCouplingBudget (d : CompoundLimitCouplingData) : ℕ :=
  d.componentCount + d.couplingWindow + d.compoundSlack

theorem compoundLimitCouplingReady.hasComponentCount
    {d : CompoundLimitCouplingData}
    (h : compoundLimitCouplingReady d) :
    hasComponentCount d ∧ couplingWindowControlled d ∧
      d.couplingWindow ≤ compoundLimitCouplingBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold compoundLimitCouplingBudget
  omega

theorem couplingWindow_le_budget (d : CompoundLimitCouplingData) :
    d.couplingWindow ≤ compoundLimitCouplingBudget d := by
  unfold compoundLimitCouplingBudget
  omega

def sampleCompoundLimitCouplingData : CompoundLimitCouplingData :=
  { componentCount := 6, couplingWindow := 8, compoundSlack := 3 }

example : compoundLimitCouplingReady sampleCompoundLimitCouplingData := by
  norm_num [compoundLimitCouplingReady, hasComponentCount]
  norm_num [couplingWindowControlled, sampleCompoundLimitCouplingData]

example : compoundLimitCouplingBudget sampleCompoundLimitCouplingData = 17 := by
  native_decide

structure CompoundLimitCouplingWindow where
  componentWindow : ℕ
  couplingWindow : ℕ
  compoundSlack : ℕ
  compoundBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CompoundLimitCouplingWindow.couplingControlled
    (w : CompoundLimitCouplingWindow) : Prop :=
  w.couplingWindow ≤ w.componentWindow + w.compoundSlack + w.slack

def compoundLimitCouplingWindowReady (w : CompoundLimitCouplingWindow) : Prop :=
  0 < w.componentWindow ∧ w.couplingControlled ∧
    w.compoundBudget ≤ w.componentWindow + w.couplingWindow + w.slack

def CompoundLimitCouplingWindow.certificate (w : CompoundLimitCouplingWindow) : ℕ :=
  w.componentWindow + w.couplingWindow + w.compoundSlack + w.compoundBudget + w.slack

theorem compoundLimitCoupling_compoundBudget_le_certificate
    (w : CompoundLimitCouplingWindow) :
    w.compoundBudget ≤ w.certificate := by
  unfold CompoundLimitCouplingWindow.certificate
  omega

def sampleCompoundLimitCouplingWindow : CompoundLimitCouplingWindow :=
  { componentWindow := 5, couplingWindow := 7, compoundSlack := 2,
    compoundBudget := 14, slack := 2 }

example : compoundLimitCouplingWindowReady sampleCompoundLimitCouplingWindow := by
  norm_num [compoundLimitCouplingWindowReady,
    CompoundLimitCouplingWindow.couplingControlled, sampleCompoundLimitCouplingWindow]


structure CompoundLimitCouplingSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CompoundLimitCouplingSchemasBudgetCertificate.controlled
    (c : CompoundLimitCouplingSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CompoundLimitCouplingSchemasBudgetCertificate.budgetControlled
    (c : CompoundLimitCouplingSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CompoundLimitCouplingSchemasBudgetCertificate.Ready
    (c : CompoundLimitCouplingSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CompoundLimitCouplingSchemasBudgetCertificate.size
    (c : CompoundLimitCouplingSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem compoundLimitCouplingSchemas_budgetCertificate_le_size
    (c : CompoundLimitCouplingSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCompoundLimitCouplingSchemasBudgetCertificate :
    CompoundLimitCouplingSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCompoundLimitCouplingSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CompoundLimitCouplingSchemasBudgetCertificate.controlled,
      sampleCompoundLimitCouplingSchemasBudgetCertificate]
  · norm_num [CompoundLimitCouplingSchemasBudgetCertificate.budgetControlled,
      sampleCompoundLimitCouplingSchemasBudgetCertificate]

example : sampleCompoundLimitCouplingSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CompoundLimitCouplingSchemasBudgetCertificate.controlled,
      sampleCompoundLimitCouplingSchemasBudgetCertificate]
  · norm_num [CompoundLimitCouplingSchemasBudgetCertificate.budgetControlled,
      sampleCompoundLimitCouplingSchemasBudgetCertificate]

example :
    sampleCompoundLimitCouplingSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCompoundLimitCouplingSchemasBudgetCertificate.size := by
  apply compoundLimitCouplingSchemas_budgetCertificate_le_size
  constructor
  · norm_num [CompoundLimitCouplingSchemasBudgetCertificate.controlled,
      sampleCompoundLimitCouplingSchemasBudgetCertificate]
  · norm_num [CompoundLimitCouplingSchemasBudgetCertificate.budgetControlled,
      sampleCompoundLimitCouplingSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleCompoundLimitCouplingSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCompoundLimitCouplingSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List CompoundLimitCouplingSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCompoundLimitCouplingSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCompoundLimitCouplingSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.CompoundLimitCouplingSchemas
