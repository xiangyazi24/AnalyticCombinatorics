import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Drmota Lalley Woods remainder schemas.

This module records finite bookkeeping for DLW remainder windows.
-/

namespace AnalyticCombinatorics.PartB.Ch7.DrmotaLalleyWoodsRemainderSchemas

structure DrmotaLalleyWoodsRemainderData where
  systemSize : ℕ
  remainderWindow : ℕ
  criticalSlack : ℕ
deriving DecidableEq, Repr

def hasSystemSize (d : DrmotaLalleyWoodsRemainderData) : Prop :=
  0 < d.systemSize

def remainderWindowControlled
    (d : DrmotaLalleyWoodsRemainderData) : Prop :=
  d.remainderWindow ≤ d.systemSize + d.criticalSlack

def drmotaLalleyWoodsRemainderReady
    (d : DrmotaLalleyWoodsRemainderData) : Prop :=
  hasSystemSize d ∧ remainderWindowControlled d

def drmotaLalleyWoodsRemainderBudget
    (d : DrmotaLalleyWoodsRemainderData) : ℕ :=
  d.systemSize + d.remainderWindow + d.criticalSlack

theorem drmotaLalleyWoodsRemainderReady.hasSystemSize
    {d : DrmotaLalleyWoodsRemainderData}
    (h : drmotaLalleyWoodsRemainderReady d) :
    hasSystemSize d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem remainderWindow_le_budget
    (d : DrmotaLalleyWoodsRemainderData) :
    d.remainderWindow ≤ drmotaLalleyWoodsRemainderBudget d := by
  unfold drmotaLalleyWoodsRemainderBudget
  omega

def sampleDrmotaLalleyWoodsRemainderData :
    DrmotaLalleyWoodsRemainderData :=
  { systemSize := 7, remainderWindow := 9, criticalSlack := 3 }

example : drmotaLalleyWoodsRemainderReady
    sampleDrmotaLalleyWoodsRemainderData := by
  norm_num [drmotaLalleyWoodsRemainderReady, hasSystemSize]
  norm_num [remainderWindowControlled, sampleDrmotaLalleyWoodsRemainderData]

example :
    drmotaLalleyWoodsRemainderBudget sampleDrmotaLalleyWoodsRemainderData = 19 := by
  native_decide


structure DrmotaLalleyWoodsRemainderSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DrmotaLalleyWoodsRemainderSchemasBudgetCertificate.controlled
    (c : DrmotaLalleyWoodsRemainderSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def DrmotaLalleyWoodsRemainderSchemasBudgetCertificate.budgetControlled
    (c : DrmotaLalleyWoodsRemainderSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DrmotaLalleyWoodsRemainderSchemasBudgetCertificate.Ready
    (c : DrmotaLalleyWoodsRemainderSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DrmotaLalleyWoodsRemainderSchemasBudgetCertificate.size
    (c : DrmotaLalleyWoodsRemainderSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem drmotaLalleyWoodsRemainderSchemas_budgetCertificate_le_size
    (c : DrmotaLalleyWoodsRemainderSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDrmotaLalleyWoodsRemainderSchemasBudgetCertificate :
    DrmotaLalleyWoodsRemainderSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleDrmotaLalleyWoodsRemainderSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DrmotaLalleyWoodsRemainderSchemasBudgetCertificate.controlled,
      sampleDrmotaLalleyWoodsRemainderSchemasBudgetCertificate]
  · norm_num [DrmotaLalleyWoodsRemainderSchemasBudgetCertificate.budgetControlled,
      sampleDrmotaLalleyWoodsRemainderSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDrmotaLalleyWoodsRemainderSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDrmotaLalleyWoodsRemainderSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleDrmotaLalleyWoodsRemainderSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DrmotaLalleyWoodsRemainderSchemasBudgetCertificate.controlled,
      sampleDrmotaLalleyWoodsRemainderSchemasBudgetCertificate]
  · norm_num [DrmotaLalleyWoodsRemainderSchemasBudgetCertificate.budgetControlled,
      sampleDrmotaLalleyWoodsRemainderSchemasBudgetCertificate]

example :
    sampleDrmotaLalleyWoodsRemainderSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDrmotaLalleyWoodsRemainderSchemasBudgetCertificate.size := by
  apply drmotaLalleyWoodsRemainderSchemas_budgetCertificate_le_size
  constructor
  · norm_num [DrmotaLalleyWoodsRemainderSchemasBudgetCertificate.controlled,
      sampleDrmotaLalleyWoodsRemainderSchemasBudgetCertificate]
  · norm_num [DrmotaLalleyWoodsRemainderSchemasBudgetCertificate.budgetControlled,
      sampleDrmotaLalleyWoodsRemainderSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List DrmotaLalleyWoodsRemainderSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDrmotaLalleyWoodsRemainderSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleDrmotaLalleyWoodsRemainderSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.DrmotaLalleyWoodsRemainderSchemas
