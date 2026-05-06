import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Prokhorov remainder window schemas.

This module records finite bookkeeping for Prokhorov remainder windows.
-/

namespace AnalyticCombinatorics.AppC.ProkhorovRemainderWindowSchemas

structure ProkhorovRemainderWindowData where
  tightnessScale : ℕ
  remainderWindow : ℕ
  prokhorovSlack : ℕ
deriving DecidableEq, Repr

def hasTightnessScale (d : ProkhorovRemainderWindowData) : Prop :=
  0 < d.tightnessScale

def remainderWindowControlled
    (d : ProkhorovRemainderWindowData) : Prop :=
  d.remainderWindow ≤ d.tightnessScale + d.prokhorovSlack

def prokhorovRemainderReady
    (d : ProkhorovRemainderWindowData) : Prop :=
  hasTightnessScale d ∧ remainderWindowControlled d

def prokhorovRemainderBudget
    (d : ProkhorovRemainderWindowData) : ℕ :=
  d.tightnessScale + d.remainderWindow + d.prokhorovSlack

theorem prokhorovRemainderReady.hasTightnessScale
    {d : ProkhorovRemainderWindowData}
    (h : prokhorovRemainderReady d) :
    hasTightnessScale d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem remainderWindow_le_budget (d : ProkhorovRemainderWindowData) :
    d.remainderWindow ≤ prokhorovRemainderBudget d := by
  unfold prokhorovRemainderBudget
  omega

def sampleProkhorovRemainderWindowData :
    ProkhorovRemainderWindowData :=
  { tightnessScale := 7, remainderWindow := 9, prokhorovSlack := 3 }

example : prokhorovRemainderReady
    sampleProkhorovRemainderWindowData := by
  norm_num [prokhorovRemainderReady, hasTightnessScale]
  norm_num [remainderWindowControlled, sampleProkhorovRemainderWindowData]

example :
    prokhorovRemainderBudget sampleProkhorovRemainderWindowData = 19 := by
  native_decide

structure ProkhorovRemainderCertificateWindow where
  tightnessWindow : ℕ
  remainderWindow : ℕ
  prokhorovSlack : ℕ
  remainderBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ProkhorovRemainderCertificateWindow.remainderControlled
    (w : ProkhorovRemainderCertificateWindow) : Prop :=
  w.remainderWindow ≤ w.tightnessWindow + w.prokhorovSlack + w.slack

def prokhorovRemainderCertificateReady
    (w : ProkhorovRemainderCertificateWindow) : Prop :=
  0 < w.tightnessWindow ∧ w.remainderControlled ∧
    w.remainderBudget ≤ w.tightnessWindow + w.remainderWindow + w.slack

def ProkhorovRemainderCertificateWindow.certificate
    (w : ProkhorovRemainderCertificateWindow) : ℕ :=
  w.tightnessWindow + w.remainderWindow + w.prokhorovSlack + w.remainderBudget + w.slack

theorem prokhorovRemainder_budget_le_certificate
    (w : ProkhorovRemainderCertificateWindow) :
    w.remainderBudget ≤ w.certificate := by
  unfold ProkhorovRemainderCertificateWindow.certificate
  omega

def sampleProkhorovRemainderCertificateWindow :
    ProkhorovRemainderCertificateWindow :=
  { tightnessWindow := 6, remainderWindow := 8, prokhorovSlack := 2,
    remainderBudget := 15, slack := 1 }

example : prokhorovRemainderCertificateReady
    sampleProkhorovRemainderCertificateWindow := by
  norm_num [prokhorovRemainderCertificateReady,
    ProkhorovRemainderCertificateWindow.remainderControlled,
    sampleProkhorovRemainderCertificateWindow]


structure ProkhorovRemainderWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ProkhorovRemainderWindowSchemasBudgetCertificate.controlled
    (c : ProkhorovRemainderWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ProkhorovRemainderWindowSchemasBudgetCertificate.budgetControlled
    (c : ProkhorovRemainderWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ProkhorovRemainderWindowSchemasBudgetCertificate.Ready
    (c : ProkhorovRemainderWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ProkhorovRemainderWindowSchemasBudgetCertificate.size
    (c : ProkhorovRemainderWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem prokhorovRemainderWindowSchemas_budgetCertificate_le_size
    (c : ProkhorovRemainderWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleProkhorovRemainderWindowSchemasBudgetCertificate :
    ProkhorovRemainderWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleProkhorovRemainderWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ProkhorovRemainderWindowSchemasBudgetCertificate.controlled,
      sampleProkhorovRemainderWindowSchemasBudgetCertificate]
  · norm_num [ProkhorovRemainderWindowSchemasBudgetCertificate.budgetControlled,
      sampleProkhorovRemainderWindowSchemasBudgetCertificate]

example : sampleProkhorovRemainderWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ProkhorovRemainderWindowSchemasBudgetCertificate.controlled,
      sampleProkhorovRemainderWindowSchemasBudgetCertificate]
  · norm_num [ProkhorovRemainderWindowSchemasBudgetCertificate.budgetControlled,
      sampleProkhorovRemainderWindowSchemasBudgetCertificate]

example :
    sampleProkhorovRemainderWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleProkhorovRemainderWindowSchemasBudgetCertificate.size := by
  apply prokhorovRemainderWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [ProkhorovRemainderWindowSchemasBudgetCertificate.controlled,
      sampleProkhorovRemainderWindowSchemasBudgetCertificate]
  · norm_num [ProkhorovRemainderWindowSchemasBudgetCertificate.budgetControlled,
      sampleProkhorovRemainderWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleProkhorovRemainderWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleProkhorovRemainderWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List ProkhorovRemainderWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleProkhorovRemainderWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleProkhorovRemainderWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.ProkhorovRemainderWindowSchemas
