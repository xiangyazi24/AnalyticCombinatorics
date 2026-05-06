import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Jensen window schemas.

This module records finite bookkeeping for Jensen formula windows.
-/

namespace AnalyticCombinatorics.PartB.Ch4.JensenWindowSchemas

structure JensenWindowData where
  zeroBudget : ℕ
  radiusWindow : ℕ
  jensenSlack : ℕ
deriving DecidableEq, Repr

def hasZeroBudget (d : JensenWindowData) : Prop :=
  0 < d.zeroBudget

def radiusWindowControlled (d : JensenWindowData) : Prop :=
  d.radiusWindow ≤ d.zeroBudget + d.jensenSlack

def jensenWindowReady (d : JensenWindowData) : Prop :=
  hasZeroBudget d ∧ radiusWindowControlled d

def jensenWindowBudget (d : JensenWindowData) : ℕ :=
  d.zeroBudget + d.radiusWindow + d.jensenSlack

theorem jensenWindowReady.hasZeroBudget {d : JensenWindowData}
    (h : jensenWindowReady d) :
    hasZeroBudget d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem radiusWindow_le_budget (d : JensenWindowData) :
    d.radiusWindow ≤ jensenWindowBudget d := by
  unfold jensenWindowBudget
  omega

def sampleJensenWindowData : JensenWindowData :=
  { zeroBudget := 6, radiusWindow := 8, jensenSlack := 3 }

example : jensenWindowReady sampleJensenWindowData := by
  norm_num [jensenWindowReady, hasZeroBudget]
  norm_num [radiusWindowControlled, sampleJensenWindowData]

example : jensenWindowBudget sampleJensenWindowData = 17 := by
  native_decide

structure JensenCertificateWindow where
  zeroBudget : ℕ
  radiusWindow : ℕ
  jensenSlack : ℕ
  boundaryBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def JensenCertificateWindow.radiusControlled (w : JensenCertificateWindow) : Prop :=
  w.radiusWindow ≤ w.zeroBudget + w.jensenSlack + w.slack

def JensenCertificateWindow.boundaryControlled (w : JensenCertificateWindow) : Prop :=
  w.boundaryBudget ≤ w.zeroBudget + w.radiusWindow + w.jensenSlack + w.slack

def jensenCertificateReady (w : JensenCertificateWindow) : Prop :=
  0 < w.zeroBudget ∧
    w.radiusControlled ∧
    w.boundaryControlled

def JensenCertificateWindow.certificate (w : JensenCertificateWindow) : ℕ :=
  w.zeroBudget + w.radiusWindow + w.jensenSlack + w.slack

theorem jensen_boundaryBudget_le_certificate {w : JensenCertificateWindow}
    (h : jensenCertificateReady w) :
    w.boundaryBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hboundary⟩
  exact hboundary

def sampleJensenCertificateWindow : JensenCertificateWindow :=
  { zeroBudget := 6, radiusWindow := 8, jensenSlack := 3, boundaryBudget := 16, slack := 0 }

example : jensenCertificateReady sampleJensenCertificateWindow := by
  norm_num [jensenCertificateReady, JensenCertificateWindow.radiusControlled,
    JensenCertificateWindow.boundaryControlled, sampleJensenCertificateWindow]

example : sampleJensenCertificateWindow.certificate = 17 := by
  native_decide


structure JensenWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def JensenWindowSchemasBudgetCertificate.controlled
    (c : JensenWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def JensenWindowSchemasBudgetCertificate.budgetControlled
    (c : JensenWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def JensenWindowSchemasBudgetCertificate.Ready
    (c : JensenWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def JensenWindowSchemasBudgetCertificate.size
    (c : JensenWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem jensenWindowSchemas_budgetCertificate_le_size
    (c : JensenWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleJensenWindowSchemasBudgetCertificate :
    JensenWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleJensenWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [JensenWindowSchemasBudgetCertificate.controlled,
      sampleJensenWindowSchemasBudgetCertificate]
  · norm_num [JensenWindowSchemasBudgetCertificate.budgetControlled,
      sampleJensenWindowSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleJensenWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleJensenWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleJensenWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [JensenWindowSchemasBudgetCertificate.controlled,
      sampleJensenWindowSchemasBudgetCertificate]
  · norm_num [JensenWindowSchemasBudgetCertificate.budgetControlled,
      sampleJensenWindowSchemasBudgetCertificate]

example :
    sampleJensenWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleJensenWindowSchemasBudgetCertificate.size := by
  apply jensenWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [JensenWindowSchemasBudgetCertificate.controlled,
      sampleJensenWindowSchemasBudgetCertificate]
  · norm_num [JensenWindowSchemasBudgetCertificate.budgetControlled,
      sampleJensenWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List JensenWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleJensenWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleJensenWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.JensenWindowSchemas
