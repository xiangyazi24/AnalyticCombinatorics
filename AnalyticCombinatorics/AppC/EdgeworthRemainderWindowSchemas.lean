import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Edgeworth remainder window schemas.

This module records finite bookkeeping for Edgeworth remainder windows.
-/

namespace AnalyticCombinatorics.AppC.EdgeworthRemainderWindowSchemas

structure EdgeworthRemainderWindowData where
  expansionOrder : ℕ
  remainderWindow : ℕ
  edgeworthSlack : ℕ
deriving DecidableEq, Repr

def hasExpansionOrder (d : EdgeworthRemainderWindowData) : Prop :=
  0 < d.expansionOrder

def remainderWindowControlled
    (d : EdgeworthRemainderWindowData) : Prop :=
  d.remainderWindow ≤ d.expansionOrder + d.edgeworthSlack

def edgeworthRemainderReady
    (d : EdgeworthRemainderWindowData) : Prop :=
  hasExpansionOrder d ∧ remainderWindowControlled d

def edgeworthRemainderBudget
    (d : EdgeworthRemainderWindowData) : ℕ :=
  d.expansionOrder + d.remainderWindow + d.edgeworthSlack

theorem edgeworthRemainderReady.hasExpansionOrder
    {d : EdgeworthRemainderWindowData}
    (h : edgeworthRemainderReady d) :
    hasExpansionOrder d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem remainderWindow_le_budget (d : EdgeworthRemainderWindowData) :
    d.remainderWindow ≤ edgeworthRemainderBudget d := by
  unfold edgeworthRemainderBudget
  omega

def sampleEdgeworthRemainderWindowData : EdgeworthRemainderWindowData :=
  { expansionOrder := 6, remainderWindow := 8, edgeworthSlack := 3 }

example : edgeworthRemainderReady sampleEdgeworthRemainderWindowData := by
  norm_num [edgeworthRemainderReady, hasExpansionOrder]
  norm_num [remainderWindowControlled, sampleEdgeworthRemainderWindowData]

example : edgeworthRemainderBudget sampleEdgeworthRemainderWindowData = 17 := by
  native_decide

structure EdgeworthRemainderCertificateWindow where
  orderWindow : ℕ
  remainderWindow : ℕ
  edgeworthSlack : ℕ
  remainderBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EdgeworthRemainderCertificateWindow.remainderControlled
    (w : EdgeworthRemainderCertificateWindow) : Prop :=
  w.remainderWindow ≤ w.orderWindow + w.edgeworthSlack + w.slack

def edgeworthRemainderCertificateReady
    (w : EdgeworthRemainderCertificateWindow) : Prop :=
  0 < w.orderWindow ∧ w.remainderControlled ∧
    w.remainderBudget ≤ w.orderWindow + w.remainderWindow + w.slack

def EdgeworthRemainderCertificateWindow.certificate
    (w : EdgeworthRemainderCertificateWindow) : ℕ :=
  w.orderWindow + w.remainderWindow + w.edgeworthSlack + w.remainderBudget + w.slack

theorem edgeworthRemainder_remainderBudget_le_certificate
    (w : EdgeworthRemainderCertificateWindow) :
    w.remainderBudget ≤ w.certificate := by
  unfold EdgeworthRemainderCertificateWindow.certificate
  omega

def sampleEdgeworthRemainderCertificateWindow :
    EdgeworthRemainderCertificateWindow :=
  { orderWindow := 5, remainderWindow := 7, edgeworthSlack := 2,
    remainderBudget := 14, slack := 2 }

example : edgeworthRemainderCertificateReady
    sampleEdgeworthRemainderCertificateWindow := by
  norm_num [edgeworthRemainderCertificateReady,
    EdgeworthRemainderCertificateWindow.remainderControlled,
    sampleEdgeworthRemainderCertificateWindow]


structure EdgeworthRemainderWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EdgeworthRemainderWindowSchemasBudgetCertificate.controlled
    (c : EdgeworthRemainderWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def EdgeworthRemainderWindowSchemasBudgetCertificate.budgetControlled
    (c : EdgeworthRemainderWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def EdgeworthRemainderWindowSchemasBudgetCertificate.Ready
    (c : EdgeworthRemainderWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def EdgeworthRemainderWindowSchemasBudgetCertificate.size
    (c : EdgeworthRemainderWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem edgeworthRemainderWindowSchemas_budgetCertificate_le_size
    (c : EdgeworthRemainderWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleEdgeworthRemainderWindowSchemasBudgetCertificate :
    EdgeworthRemainderWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleEdgeworthRemainderWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [EdgeworthRemainderWindowSchemasBudgetCertificate.controlled,
      sampleEdgeworthRemainderWindowSchemasBudgetCertificate]
  · norm_num [EdgeworthRemainderWindowSchemasBudgetCertificate.budgetControlled,
      sampleEdgeworthRemainderWindowSchemasBudgetCertificate]

example : sampleEdgeworthRemainderWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [EdgeworthRemainderWindowSchemasBudgetCertificate.controlled,
      sampleEdgeworthRemainderWindowSchemasBudgetCertificate]
  · norm_num [EdgeworthRemainderWindowSchemasBudgetCertificate.budgetControlled,
      sampleEdgeworthRemainderWindowSchemasBudgetCertificate]

example :
    sampleEdgeworthRemainderWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleEdgeworthRemainderWindowSchemasBudgetCertificate.size := by
  apply edgeworthRemainderWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [EdgeworthRemainderWindowSchemasBudgetCertificate.controlled,
      sampleEdgeworthRemainderWindowSchemasBudgetCertificate]
  · norm_num [EdgeworthRemainderWindowSchemasBudgetCertificate.budgetControlled,
      sampleEdgeworthRemainderWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleEdgeworthRemainderWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleEdgeworthRemainderWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List EdgeworthRemainderWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleEdgeworthRemainderWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleEdgeworthRemainderWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.EdgeworthRemainderWindowSchemas
