import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Tauberian remainder window schemas.

This module records finite bookkeeping for Tauberian remainders.
-/

namespace AnalyticCombinatorics.AppC.TauberianRemainderWindowSchemas

structure TauberianRemainderData where
  tauberianScale : ℕ
  remainderWindow : ℕ
  remainderSlack : ℕ
deriving DecidableEq, Repr

def hasTauberianScale (d : TauberianRemainderData) : Prop :=
  0 < d.tauberianScale

def remainderWindowControlled (d : TauberianRemainderData) : Prop :=
  d.remainderWindow ≤ d.tauberianScale + d.remainderSlack

def tauberianRemainderReady (d : TauberianRemainderData) : Prop :=
  hasTauberianScale d ∧ remainderWindowControlled d

def tauberianRemainderBudget (d : TauberianRemainderData) : ℕ :=
  d.tauberianScale + d.remainderWindow + d.remainderSlack

theorem tauberianRemainderReady.hasTauberianScale
    {d : TauberianRemainderData}
    (h : tauberianRemainderReady d) :
    hasTauberianScale d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem remainderWindow_le_budget (d : TauberianRemainderData) :
    d.remainderWindow ≤ tauberianRemainderBudget d := by
  unfold tauberianRemainderBudget
  omega

def sampleTauberianRemainderData : TauberianRemainderData :=
  { tauberianScale := 6, remainderWindow := 8, remainderSlack := 3 }

example : tauberianRemainderReady sampleTauberianRemainderData := by
  norm_num [tauberianRemainderReady, hasTauberianScale]
  norm_num [remainderWindowControlled, sampleTauberianRemainderData]

example : tauberianRemainderBudget sampleTauberianRemainderData = 17 := by
  native_decide

structure TauberianRemainderCertificateWindow where
  tauberianWindow : ℕ
  remainderWindow : ℕ
  remainderSlack : ℕ
  tauberianBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TauberianRemainderCertificateWindow.remainderControlled
    (w : TauberianRemainderCertificateWindow) : Prop :=
  w.remainderWindow ≤ w.tauberianWindow + w.remainderSlack + w.slack

def tauberianRemainderCertificateReady
    (w : TauberianRemainderCertificateWindow) : Prop :=
  0 < w.tauberianWindow ∧ w.remainderControlled ∧
    w.tauberianBudget ≤ w.tauberianWindow + w.remainderWindow + w.slack

def TauberianRemainderCertificateWindow.certificate
    (w : TauberianRemainderCertificateWindow) : ℕ :=
  w.tauberianWindow + w.remainderWindow + w.remainderSlack + w.tauberianBudget + w.slack

theorem tauberianRemainder_tauberianBudget_le_certificate
    (w : TauberianRemainderCertificateWindow) :
    w.tauberianBudget ≤ w.certificate := by
  unfold TauberianRemainderCertificateWindow.certificate
  omega

def sampleTauberianRemainderCertificateWindow :
    TauberianRemainderCertificateWindow :=
  { tauberianWindow := 5, remainderWindow := 7, remainderSlack := 2,
    tauberianBudget := 14, slack := 2 }

example : tauberianRemainderCertificateReady
    sampleTauberianRemainderCertificateWindow := by
  norm_num [tauberianRemainderCertificateReady,
    TauberianRemainderCertificateWindow.remainderControlled,
    sampleTauberianRemainderCertificateWindow]


structure TauberianRemainderWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TauberianRemainderWindowSchemasBudgetCertificate.controlled
    (c : TauberianRemainderWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def TauberianRemainderWindowSchemasBudgetCertificate.budgetControlled
    (c : TauberianRemainderWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def TauberianRemainderWindowSchemasBudgetCertificate.Ready
    (c : TauberianRemainderWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TauberianRemainderWindowSchemasBudgetCertificate.size
    (c : TauberianRemainderWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem tauberianRemainderWindowSchemas_budgetCertificate_le_size
    (c : TauberianRemainderWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleTauberianRemainderWindowSchemasBudgetCertificate :
    TauberianRemainderWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleTauberianRemainderWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [TauberianRemainderWindowSchemasBudgetCertificate.controlled,
      sampleTauberianRemainderWindowSchemasBudgetCertificate]
  · norm_num [TauberianRemainderWindowSchemasBudgetCertificate.budgetControlled,
      sampleTauberianRemainderWindowSchemasBudgetCertificate]

example : sampleTauberianRemainderWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [TauberianRemainderWindowSchemasBudgetCertificate.controlled,
      sampleTauberianRemainderWindowSchemasBudgetCertificate]
  · norm_num [TauberianRemainderWindowSchemasBudgetCertificate.budgetControlled,
      sampleTauberianRemainderWindowSchemasBudgetCertificate]

example :
    sampleTauberianRemainderWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleTauberianRemainderWindowSchemasBudgetCertificate.size := by
  apply tauberianRemainderWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [TauberianRemainderWindowSchemasBudgetCertificate.controlled,
      sampleTauberianRemainderWindowSchemasBudgetCertificate]
  · norm_num [TauberianRemainderWindowSchemasBudgetCertificate.budgetControlled,
      sampleTauberianRemainderWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleTauberianRemainderWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleTauberianRemainderWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List TauberianRemainderWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleTauberianRemainderWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleTauberianRemainderWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.TauberianRemainderWindowSchemas
