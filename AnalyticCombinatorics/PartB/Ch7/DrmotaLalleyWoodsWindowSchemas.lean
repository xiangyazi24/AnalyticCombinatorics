import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Drmota-Lalley-Woods window schemas.

This module records finite bookkeeping for DLW-type critical windows.
-/

namespace AnalyticCombinatorics.PartB.Ch7.DrmotaLalleyWoodsWindowSchemas

structure DLWWindowData where
  dependencyClasses : ℕ
  criticalWindow : ℕ
  schemaSlack : ℕ
deriving DecidableEq, Repr

def hasDependencyClasses (d : DLWWindowData) : Prop :=
  0 < d.dependencyClasses

def criticalWindowControlled (d : DLWWindowData) : Prop :=
  d.criticalWindow ≤ d.dependencyClasses + d.schemaSlack

def dlwWindowReady (d : DLWWindowData) : Prop :=
  hasDependencyClasses d ∧ criticalWindowControlled d

def dlwWindowBudget (d : DLWWindowData) : ℕ :=
  d.dependencyClasses + d.criticalWindow + d.schemaSlack

theorem dlwWindowReady.hasDependencyClasses {d : DLWWindowData}
    (h : dlwWindowReady d) :
    hasDependencyClasses d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem criticalWindow_le_budget (d : DLWWindowData) :
    d.criticalWindow ≤ dlwWindowBudget d := by
  unfold dlwWindowBudget
  omega

def sampleDLWWindowData : DLWWindowData :=
  { dependencyClasses := 6, criticalWindow := 8, schemaSlack := 3 }

example : dlwWindowReady sampleDLWWindowData := by
  norm_num [dlwWindowReady, hasDependencyClasses]
  norm_num [criticalWindowControlled, sampleDLWWindowData]

example : dlwWindowBudget sampleDLWWindowData = 17 := by
  native_decide

structure DLWCertificateWindow where
  dependencyClasses : ℕ
  criticalWindow : ℕ
  schemaSlack : ℕ
  varianceBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DLWCertificateWindow.criticalControlled (w : DLWCertificateWindow) : Prop :=
  w.criticalWindow ≤ w.dependencyClasses + w.schemaSlack + w.slack

def DLWCertificateWindow.varianceControlled (w : DLWCertificateWindow) : Prop :=
  w.varianceBudget ≤ w.dependencyClasses + w.criticalWindow + w.schemaSlack + w.slack

def dlwCertificateReady (w : DLWCertificateWindow) : Prop :=
  0 < w.dependencyClasses ∧
    w.criticalControlled ∧
    w.varianceControlled

def DLWCertificateWindow.certificate (w : DLWCertificateWindow) : ℕ :=
  w.dependencyClasses + w.criticalWindow + w.schemaSlack + w.slack

theorem dlw_varianceBudget_le_certificate {w : DLWCertificateWindow}
    (h : dlwCertificateReady w) :
    w.varianceBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hvar⟩
  exact hvar

def sampleDLWCertificateWindow : DLWCertificateWindow :=
  { dependencyClasses := 6, criticalWindow := 8, schemaSlack := 3, varianceBudget := 16,
    slack := 0 }

example : dlwCertificateReady sampleDLWCertificateWindow := by
  norm_num [dlwCertificateReady, DLWCertificateWindow.criticalControlled,
    DLWCertificateWindow.varianceControlled, sampleDLWCertificateWindow]

example : sampleDLWCertificateWindow.certificate = 17 := by
  native_decide


structure DrmotaLalleyWoodsWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DrmotaLalleyWoodsWindowSchemasBudgetCertificate.controlled
    (c : DrmotaLalleyWoodsWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def DrmotaLalleyWoodsWindowSchemasBudgetCertificate.budgetControlled
    (c : DrmotaLalleyWoodsWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DrmotaLalleyWoodsWindowSchemasBudgetCertificate.Ready
    (c : DrmotaLalleyWoodsWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DrmotaLalleyWoodsWindowSchemasBudgetCertificate.size
    (c : DrmotaLalleyWoodsWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem drmotaLalleyWoodsWindowSchemas_budgetCertificate_le_size
    (c : DrmotaLalleyWoodsWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDrmotaLalleyWoodsWindowSchemasBudgetCertificate :
    DrmotaLalleyWoodsWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleDrmotaLalleyWoodsWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DrmotaLalleyWoodsWindowSchemasBudgetCertificate.controlled,
      sampleDrmotaLalleyWoodsWindowSchemasBudgetCertificate]
  · norm_num [DrmotaLalleyWoodsWindowSchemasBudgetCertificate.budgetControlled,
      sampleDrmotaLalleyWoodsWindowSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDrmotaLalleyWoodsWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDrmotaLalleyWoodsWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleDrmotaLalleyWoodsWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DrmotaLalleyWoodsWindowSchemasBudgetCertificate.controlled,
      sampleDrmotaLalleyWoodsWindowSchemasBudgetCertificate]
  · norm_num [DrmotaLalleyWoodsWindowSchemasBudgetCertificate.budgetControlled,
      sampleDrmotaLalleyWoodsWindowSchemasBudgetCertificate]

example :
    sampleDrmotaLalleyWoodsWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDrmotaLalleyWoodsWindowSchemasBudgetCertificate.size := by
  apply drmotaLalleyWoodsWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [DrmotaLalleyWoodsWindowSchemasBudgetCertificate.controlled,
      sampleDrmotaLalleyWoodsWindowSchemasBudgetCertificate]
  · norm_num [DrmotaLalleyWoodsWindowSchemasBudgetCertificate.budgetControlled,
      sampleDrmotaLalleyWoodsWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List DrmotaLalleyWoodsWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDrmotaLalleyWoodsWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleDrmotaLalleyWoodsWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.DrmotaLalleyWoodsWindowSchemas
