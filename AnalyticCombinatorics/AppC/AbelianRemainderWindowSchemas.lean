import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Abelian remainder window schemas.

This module records finite bookkeeping for Abelian remainder windows.
-/

namespace AnalyticCombinatorics.AppC.AbelianRemainderWindowSchemas

structure AbelianRemainderWindowData where
  abelianScale : ℕ
  remainderWindow : ℕ
  abelianSlack : ℕ
deriving DecidableEq, Repr

def hasAbelianScale (d : AbelianRemainderWindowData) : Prop :=
  0 < d.abelianScale

def remainderWindowControlled (d : AbelianRemainderWindowData) : Prop :=
  d.remainderWindow ≤ d.abelianScale + d.abelianSlack

def abelianRemainderReady (d : AbelianRemainderWindowData) : Prop :=
  hasAbelianScale d ∧ remainderWindowControlled d

def abelianRemainderBudget (d : AbelianRemainderWindowData) : ℕ :=
  d.abelianScale + d.remainderWindow + d.abelianSlack

theorem abelianRemainderReady.hasAbelianScale
    {d : AbelianRemainderWindowData}
    (h : abelianRemainderReady d) :
    hasAbelianScale d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem remainderWindow_le_budget (d : AbelianRemainderWindowData) :
    d.remainderWindow ≤ abelianRemainderBudget d := by
  unfold abelianRemainderBudget
  omega

def sampleAbelianRemainderWindowData : AbelianRemainderWindowData :=
  { abelianScale := 6, remainderWindow := 8, abelianSlack := 3 }

example : abelianRemainderReady sampleAbelianRemainderWindowData := by
  norm_num [abelianRemainderReady, hasAbelianScale]
  norm_num [remainderWindowControlled, sampleAbelianRemainderWindowData]

example : abelianRemainderBudget sampleAbelianRemainderWindowData = 17 := by
  native_decide

structure AbelianRemainderCertificateWindow where
  scaleWindow : ℕ
  remainderWindow : ℕ
  abelianSlack : ℕ
  transferBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AbelianRemainderCertificateWindow.remainderControlled
    (w : AbelianRemainderCertificateWindow) : Prop :=
  w.remainderWindow ≤ w.scaleWindow + w.abelianSlack + w.slack

def abelianRemainderCertificateReady (w : AbelianRemainderCertificateWindow) : Prop :=
  0 < w.scaleWindow ∧ w.remainderControlled ∧
    w.transferBudget ≤ w.scaleWindow + w.remainderWindow + w.slack

def AbelianRemainderCertificateWindow.certificate
    (w : AbelianRemainderCertificateWindow) : ℕ :=
  w.scaleWindow + w.remainderWindow + w.abelianSlack + w.transferBudget + w.slack

theorem abelianRemainder_transferBudget_le_certificate
    (w : AbelianRemainderCertificateWindow) :
    w.transferBudget ≤ w.certificate := by
  unfold AbelianRemainderCertificateWindow.certificate
  omega

def sampleAbelianRemainderCertificateWindow : AbelianRemainderCertificateWindow :=
  { scaleWindow := 5, remainderWindow := 7, abelianSlack := 2,
    transferBudget := 14, slack := 2 }

example : abelianRemainderCertificateReady sampleAbelianRemainderCertificateWindow := by
  norm_num [abelianRemainderCertificateReady,
    AbelianRemainderCertificateWindow.remainderControlled,
    sampleAbelianRemainderCertificateWindow]


structure AbelianRemainderWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AbelianRemainderWindowSchemasBudgetCertificate.controlled
    (c : AbelianRemainderWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AbelianRemainderWindowSchemasBudgetCertificate.budgetControlled
    (c : AbelianRemainderWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AbelianRemainderWindowSchemasBudgetCertificate.Ready
    (c : AbelianRemainderWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AbelianRemainderWindowSchemasBudgetCertificate.size
    (c : AbelianRemainderWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem abelianRemainderWindowSchemas_budgetCertificate_le_size
    (c : AbelianRemainderWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAbelianRemainderWindowSchemasBudgetCertificate :
    AbelianRemainderWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAbelianRemainderWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [AbelianRemainderWindowSchemasBudgetCertificate.controlled,
      sampleAbelianRemainderWindowSchemasBudgetCertificate]
  · norm_num [AbelianRemainderWindowSchemasBudgetCertificate.budgetControlled,
      sampleAbelianRemainderWindowSchemasBudgetCertificate]

example : sampleAbelianRemainderWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [AbelianRemainderWindowSchemasBudgetCertificate.controlled,
      sampleAbelianRemainderWindowSchemasBudgetCertificate]
  · norm_num [AbelianRemainderWindowSchemasBudgetCertificate.budgetControlled,
      sampleAbelianRemainderWindowSchemasBudgetCertificate]

example :
    sampleAbelianRemainderWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleAbelianRemainderWindowSchemasBudgetCertificate.size := by
  apply abelianRemainderWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [AbelianRemainderWindowSchemasBudgetCertificate.controlled,
      sampleAbelianRemainderWindowSchemasBudgetCertificate]
  · norm_num [AbelianRemainderWindowSchemasBudgetCertificate.budgetControlled,
      sampleAbelianRemainderWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleAbelianRemainderWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleAbelianRemainderWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List AbelianRemainderWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAbelianRemainderWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAbelianRemainderWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.AbelianRemainderWindowSchemas
