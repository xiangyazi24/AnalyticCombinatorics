import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Rouche window schemas.

This module records finite bookkeeping for Rouche comparison windows.
-/

namespace AnalyticCombinatorics.PartB.Ch4.RoucheWindowSchemas

structure RoucheWindowData where
  contourCount : ℕ
  comparisonDepth : ℕ
  roucheSlack : ℕ
deriving DecidableEq, Repr

def hasContourCount (d : RoucheWindowData) : Prop :=
  0 < d.contourCount

def comparisonDepthControlled (d : RoucheWindowData) : Prop :=
  d.comparisonDepth ≤ d.contourCount + d.roucheSlack

def roucheWindowReady (d : RoucheWindowData) : Prop :=
  hasContourCount d ∧ comparisonDepthControlled d

def roucheWindowBudget (d : RoucheWindowData) : ℕ :=
  d.contourCount + d.comparisonDepth + d.roucheSlack

theorem roucheWindowReady.hasContourCount {d : RoucheWindowData}
    (h : roucheWindowReady d) :
    hasContourCount d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem comparisonDepth_le_budget (d : RoucheWindowData) :
    d.comparisonDepth ≤ roucheWindowBudget d := by
  unfold roucheWindowBudget
  omega

def sampleRoucheWindowData : RoucheWindowData :=
  { contourCount := 6, comparisonDepth := 8, roucheSlack := 3 }

example : roucheWindowReady sampleRoucheWindowData := by
  norm_num [roucheWindowReady, hasContourCount]
  norm_num [comparisonDepthControlled, sampleRoucheWindowData]

example : roucheWindowBudget sampleRoucheWindowData = 17 := by
  native_decide

structure RoucheCertificateWindow where
  contourCount : ℕ
  comparisonDepth : ℕ
  roucheSlack : ℕ
  zeroTransferBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RoucheCertificateWindow.comparisonControlled (w : RoucheCertificateWindow) : Prop :=
  w.comparisonDepth ≤ w.contourCount + w.roucheSlack + w.slack

def RoucheCertificateWindow.transferControlled (w : RoucheCertificateWindow) : Prop :=
  w.zeroTransferBudget ≤ w.contourCount + w.comparisonDepth + w.roucheSlack + w.slack

def roucheCertificateReady (w : RoucheCertificateWindow) : Prop :=
  0 < w.contourCount ∧
    w.comparisonControlled ∧
    w.transferControlled

def RoucheCertificateWindow.certificate (w : RoucheCertificateWindow) : ℕ :=
  w.contourCount + w.comparisonDepth + w.roucheSlack + w.slack

theorem rouche_zeroTransferBudget_le_certificate {w : RoucheCertificateWindow}
    (h : roucheCertificateReady w) :
    w.zeroTransferBudget ≤ w.certificate := by
  rcases h with ⟨_, _, htransfer⟩
  exact htransfer

def sampleRoucheCertificateWindow : RoucheCertificateWindow :=
  { contourCount := 6, comparisonDepth := 8, roucheSlack := 3, zeroTransferBudget := 16,
    slack := 0 }

example : roucheCertificateReady sampleRoucheCertificateWindow := by
  norm_num [roucheCertificateReady, RoucheCertificateWindow.comparisonControlled,
    RoucheCertificateWindow.transferControlled, sampleRoucheCertificateWindow]

example : sampleRoucheCertificateWindow.certificate = 17 := by
  native_decide


structure RoucheWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RoucheWindowSchemasBudgetCertificate.controlled
    (c : RoucheWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RoucheWindowSchemasBudgetCertificate.budgetControlled
    (c : RoucheWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RoucheWindowSchemasBudgetCertificate.Ready
    (c : RoucheWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RoucheWindowSchemasBudgetCertificate.size
    (c : RoucheWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem roucheWindowSchemas_budgetCertificate_le_size
    (c : RoucheWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRoucheWindowSchemasBudgetCertificate :
    RoucheWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRoucheWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RoucheWindowSchemasBudgetCertificate.controlled,
      sampleRoucheWindowSchemasBudgetCertificate]
  · norm_num [RoucheWindowSchemasBudgetCertificate.budgetControlled,
      sampleRoucheWindowSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRoucheWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRoucheWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRoucheWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RoucheWindowSchemasBudgetCertificate.controlled,
      sampleRoucheWindowSchemasBudgetCertificate]
  · norm_num [RoucheWindowSchemasBudgetCertificate.budgetControlled,
      sampleRoucheWindowSchemasBudgetCertificate]

example :
    sampleRoucheWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRoucheWindowSchemasBudgetCertificate.size := by
  apply roucheWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RoucheWindowSchemasBudgetCertificate.controlled,
      sampleRoucheWindowSchemasBudgetCertificate]
  · norm_num [RoucheWindowSchemasBudgetCertificate.budgetControlled,
      sampleRoucheWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List RoucheWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRoucheWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleRoucheWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.RoucheWindowSchemas
