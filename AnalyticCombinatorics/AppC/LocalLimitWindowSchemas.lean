import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Local limit window schemas.

The finite schema records window width, lattice span, and approximation
budget for local limit statements.
-/

namespace AnalyticCombinatorics.AppC.LocalLimitWindowSchemas

structure LocalLimitWindowData where
  windowWidth : ℕ
  latticeSpan : ℕ
  approximationBudget : ℕ
deriving DecidableEq, Repr

def positiveLatticeSpan (d : LocalLimitWindowData) : Prop :=
  0 < d.latticeSpan

def windowControlled (d : LocalLimitWindowData) : Prop :=
  d.windowWidth ≤ d.latticeSpan + d.approximationBudget

def localLimitWindowReady (d : LocalLimitWindowData) : Prop :=
  positiveLatticeSpan d ∧ windowControlled d

def localLimitWindowBudget (d : LocalLimitWindowData) : ℕ :=
  d.windowWidth + d.latticeSpan + d.approximationBudget

theorem localLimitWindowReady.span {d : LocalLimitWindowData}
    (h : localLimitWindowReady d) :
    positiveLatticeSpan d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem windowWidth_le_localLimitBudget (d : LocalLimitWindowData) :
    d.windowWidth ≤ localLimitWindowBudget d := by
  unfold localLimitWindowBudget
  omega

def sampleLocalLimitWindowData : LocalLimitWindowData :=
  { windowWidth := 6, latticeSpan := 4, approximationBudget := 5 }

example : localLimitWindowReady sampleLocalLimitWindowData := by
  norm_num [localLimitWindowReady, positiveLatticeSpan]
  norm_num [windowControlled, sampleLocalLimitWindowData]

example : localLimitWindowBudget sampleLocalLimitWindowData = 15 := by
  native_decide

structure LocalLimitCertificateWindow where
  windowWidth : ℕ
  latticeSpan : ℕ
  approximationBudget : ℕ
  massBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LocalLimitCertificateWindow.windowControlled (w : LocalLimitCertificateWindow) : Prop :=
  w.windowWidth ≤ w.latticeSpan + w.approximationBudget + w.slack

def LocalLimitCertificateWindow.massControlled (w : LocalLimitCertificateWindow) : Prop :=
  w.massBudget ≤ w.windowWidth + w.latticeSpan + w.approximationBudget + w.slack

def localLimitCertificateReady (w : LocalLimitCertificateWindow) : Prop :=
  0 < w.latticeSpan ∧
    w.windowControlled ∧
    w.massControlled

def LocalLimitCertificateWindow.certificate (w : LocalLimitCertificateWindow) : ℕ :=
  w.windowWidth + w.latticeSpan + w.approximationBudget + w.slack

theorem localLimit_massBudget_le_certificate {w : LocalLimitCertificateWindow}
    (h : localLimitCertificateReady w) :
    w.massBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hmass⟩
  exact hmass

def sampleLocalLimitCertificateWindow : LocalLimitCertificateWindow :=
  { windowWidth := 6, latticeSpan := 4, approximationBudget := 5, massBudget := 14, slack := 0 }

example : localLimitCertificateReady sampleLocalLimitCertificateWindow := by
  norm_num [localLimitCertificateReady, LocalLimitCertificateWindow.windowControlled,
    LocalLimitCertificateWindow.massControlled, sampleLocalLimitCertificateWindow]

example : sampleLocalLimitCertificateWindow.certificate = 15 := by
  native_decide


structure LocalLimitWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LocalLimitWindowSchemasBudgetCertificate.controlled
    (c : LocalLimitWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LocalLimitWindowSchemasBudgetCertificate.budgetControlled
    (c : LocalLimitWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LocalLimitWindowSchemasBudgetCertificate.Ready
    (c : LocalLimitWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LocalLimitWindowSchemasBudgetCertificate.size
    (c : LocalLimitWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem localLimitWindowSchemas_budgetCertificate_le_size
    (c : LocalLimitWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLocalLimitWindowSchemasBudgetCertificate :
    LocalLimitWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLocalLimitWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LocalLimitWindowSchemasBudgetCertificate.controlled,
      sampleLocalLimitWindowSchemasBudgetCertificate]
  · norm_num [LocalLimitWindowSchemasBudgetCertificate.budgetControlled,
      sampleLocalLimitWindowSchemasBudgetCertificate]

example : sampleLocalLimitWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LocalLimitWindowSchemasBudgetCertificate.controlled,
      sampleLocalLimitWindowSchemasBudgetCertificate]
  · norm_num [LocalLimitWindowSchemasBudgetCertificate.budgetControlled,
      sampleLocalLimitWindowSchemasBudgetCertificate]

example :
    sampleLocalLimitWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLocalLimitWindowSchemasBudgetCertificate.size := by
  apply localLimitWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [LocalLimitWindowSchemasBudgetCertificate.controlled,
      sampleLocalLimitWindowSchemasBudgetCertificate]
  · norm_num [LocalLimitWindowSchemasBudgetCertificate.budgetControlled,
      sampleLocalLimitWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleLocalLimitWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLocalLimitWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List LocalLimitWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLocalLimitWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLocalLimitWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.LocalLimitWindowSchemas
