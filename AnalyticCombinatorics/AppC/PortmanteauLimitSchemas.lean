import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Portmanteau limit schemas.

This module records finite bookkeeping for Portmanteau limit criteria.
-/

namespace AnalyticCombinatorics.AppC.PortmanteauLimitSchemas

structure PortmanteauLimitData where
  testSets : ℕ
  limitWindow : ℕ
  boundarySlack : ℕ
deriving DecidableEq, Repr

def hasTestSets (d : PortmanteauLimitData) : Prop :=
  0 < d.testSets

def limitWindowControlled (d : PortmanteauLimitData) : Prop :=
  d.limitWindow ≤ d.testSets + d.boundarySlack

def portmanteauLimitReady (d : PortmanteauLimitData) : Prop :=
  hasTestSets d ∧ limitWindowControlled d

def portmanteauLimitBudget (d : PortmanteauLimitData) : ℕ :=
  d.testSets + d.limitWindow + d.boundarySlack

theorem portmanteauLimitReady.hasTestSets
    {d : PortmanteauLimitData}
    (h : portmanteauLimitReady d) :
    hasTestSets d ∧ limitWindowControlled d ∧ d.limitWindow ≤ portmanteauLimitBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold portmanteauLimitBudget
  omega

theorem limitWindow_le_budget (d : PortmanteauLimitData) :
    d.limitWindow ≤ portmanteauLimitBudget d := by
  unfold portmanteauLimitBudget
  omega

def samplePortmanteauLimitData : PortmanteauLimitData :=
  { testSets := 7, limitWindow := 9, boundarySlack := 3 }

example : portmanteauLimitReady samplePortmanteauLimitData := by
  norm_num [portmanteauLimitReady, hasTestSets]
  norm_num [limitWindowControlled, samplePortmanteauLimitData]

example : portmanteauLimitBudget samplePortmanteauLimitData = 19 := by
  native_decide

structure PortmanteauLimitWindow where
  testSetWindow : ℕ
  limitWindow : ℕ
  boundarySlack : ℕ
  portmanteauBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PortmanteauLimitWindow.limitControlled (w : PortmanteauLimitWindow) : Prop :=
  w.limitWindow ≤ w.testSetWindow + w.boundarySlack + w.slack

def portmanteauLimitWindowReady (w : PortmanteauLimitWindow) : Prop :=
  0 < w.testSetWindow ∧ w.limitControlled ∧
    w.portmanteauBudget ≤ w.testSetWindow + w.limitWindow + w.slack

def PortmanteauLimitWindow.certificate (w : PortmanteauLimitWindow) : ℕ :=
  w.testSetWindow + w.limitWindow + w.boundarySlack + w.portmanteauBudget + w.slack

theorem portmanteauLimit_portmanteauBudget_le_certificate
    (w : PortmanteauLimitWindow) :
    w.portmanteauBudget ≤ w.certificate := by
  unfold PortmanteauLimitWindow.certificate
  omega

def samplePortmanteauLimitWindow : PortmanteauLimitWindow :=
  { testSetWindow := 6, limitWindow := 8, boundarySlack := 2,
    portmanteauBudget := 15, slack := 1 }

example : portmanteauLimitWindowReady samplePortmanteauLimitWindow := by
  norm_num [portmanteauLimitWindowReady, PortmanteauLimitWindow.limitControlled,
    samplePortmanteauLimitWindow]


structure PortmanteauLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PortmanteauLimitSchemasBudgetCertificate.controlled
    (c : PortmanteauLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PortmanteauLimitSchemasBudgetCertificate.budgetControlled
    (c : PortmanteauLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PortmanteauLimitSchemasBudgetCertificate.Ready
    (c : PortmanteauLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PortmanteauLimitSchemasBudgetCertificate.size
    (c : PortmanteauLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem portmanteauLimitSchemas_budgetCertificate_le_size
    (c : PortmanteauLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePortmanteauLimitSchemasBudgetCertificate :
    PortmanteauLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    samplePortmanteauLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PortmanteauLimitSchemasBudgetCertificate.controlled,
      samplePortmanteauLimitSchemasBudgetCertificate]
  · norm_num [PortmanteauLimitSchemasBudgetCertificate.budgetControlled,
      samplePortmanteauLimitSchemasBudgetCertificate]

example : samplePortmanteauLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PortmanteauLimitSchemasBudgetCertificate.controlled,
      samplePortmanteauLimitSchemasBudgetCertificate]
  · norm_num [PortmanteauLimitSchemasBudgetCertificate.budgetControlled,
      samplePortmanteauLimitSchemasBudgetCertificate]

example :
    samplePortmanteauLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePortmanteauLimitSchemasBudgetCertificate.size := by
  apply portmanteauLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [PortmanteauLimitSchemasBudgetCertificate.controlled,
      samplePortmanteauLimitSchemasBudgetCertificate]
  · norm_num [PortmanteauLimitSchemasBudgetCertificate.budgetControlled,
      samplePortmanteauLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    samplePortmanteauLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePortmanteauLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List PortmanteauLimitSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePortmanteauLimitSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePortmanteauLimitSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.PortmanteauLimitSchemas
