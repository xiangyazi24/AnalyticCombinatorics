import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Critical window schema bookkeeping.

The finite data records window center, width, and scaling error for phase
transition estimates.
-/

namespace AnalyticCombinatorics.Asymptotics.CriticalWindowSchemas

structure CriticalWindowData where
  center : ℕ
  width : ℕ
  scalingError : ℕ
deriving DecidableEq, Repr

def positiveWidth (d : CriticalWindowData) : Prop :=
  0 < d.width

def criticalWindowReady (d : CriticalWindowData) : Prop :=
  positiveWidth d

def leftEndpoint (d : CriticalWindowData) : ℕ :=
  d.center - d.width

def rightEndpoint (d : CriticalWindowData) : ℕ :=
  d.center + d.width

def criticalWindowBudget (d : CriticalWindowData) : ℕ :=
  d.width + d.scalingError

theorem leftEndpoint_le_center (d : CriticalWindowData) :
    leftEndpoint d ≤ d.center := by
  unfold leftEndpoint
  omega

theorem width_le_budget (d : CriticalWindowData) :
    d.width ≤ criticalWindowBudget d := by
  unfold criticalWindowBudget
  omega

def sampleCriticalWindow : CriticalWindowData :=
  { center := 10, width := 3, scalingError := 2 }

example : criticalWindowReady sampleCriticalWindow := by
  norm_num [criticalWindowReady, positiveWidth, sampleCriticalWindow]

example : leftEndpoint sampleCriticalWindow = 7 := by
  native_decide

example : rightEndpoint sampleCriticalWindow = 13 := by
  native_decide

/-- Finite executable readiness audit for critical window data. -/
def criticalWindowDataListReady
    (data : List CriticalWindowData) : Bool :=
  data.all fun d => 0 < d.width

theorem criticalWindowDataList_readyWindow :
    criticalWindowDataListReady
      [{ center := 8, width := 2, scalingError := 1 },
       { center := 10, width := 3, scalingError := 2 }] = true := by
  unfold criticalWindowDataListReady
  native_decide

/-- A certificate window for critical-window endpoint bookkeeping. -/
structure CriticalWindowCertificate where
  centerWindow : ℕ
  widthWindow : ℕ
  scalingError : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The critical window has positive width. -/
def criticalWindowCertificateControlled
    (w : CriticalWindowCertificate) : Prop :=
  0 < w.widthWindow

/-- Readiness for a critical-window certificate. -/
def criticalWindowCertificateReady
    (w : CriticalWindowCertificate) : Prop :=
  criticalWindowCertificateControlled w ∧
    w.certificateBudget ≤ w.widthWindow + w.scalingError + w.slack

/-- Total size of a critical-window certificate. -/
def criticalWindowCertificateBudget
    (w : CriticalWindowCertificate) : ℕ :=
  w.centerWindow + w.widthWindow + w.scalingError + w.certificateBudget + w.slack

theorem criticalWindowCertificate_budget_le_total
    (w : CriticalWindowCertificate)
    (h : criticalWindowCertificateReady w) :
    w.certificateBudget ≤ criticalWindowCertificateBudget w := by
  rcases h with ⟨_, hbudget⟩
  unfold criticalWindowCertificateBudget
  omega

def sampleCriticalWindowCertificate : CriticalWindowCertificate where
  centerWindow := 10
  widthWindow := 3
  scalingError := 2
  certificateBudget := 5
  slack := 1

example :
    criticalWindowCertificateReady sampleCriticalWindowCertificate := by
  norm_num [criticalWindowCertificateReady,
    criticalWindowCertificateControlled, sampleCriticalWindowCertificate]

example :
    sampleCriticalWindowCertificate.certificateBudget ≤
      criticalWindowCertificateBudget sampleCriticalWindowCertificate := by
  apply criticalWindowCertificate_budget_le_total
  norm_num [criticalWindowCertificateReady,
    criticalWindowCertificateControlled, sampleCriticalWindowCertificate]

structure CriticalWindowRefinementCertificate where
  centerWindow : ℕ
  widthWindow : ℕ
  scalingErrorWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CriticalWindowRefinementCertificate.widthControlled
    (c : CriticalWindowRefinementCertificate) : Prop :=
  0 < c.widthWindow

def CriticalWindowRefinementCertificate.certificateBudgetControlled
    (c : CriticalWindowRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.centerWindow + c.widthWindow + c.scalingErrorWindow + c.slack

def criticalWindowRefinementReady
    (c : CriticalWindowRefinementCertificate) : Prop :=
  c.widthControlled ∧ c.certificateBudgetControlled

def CriticalWindowRefinementCertificate.size
    (c : CriticalWindowRefinementCertificate) : ℕ :=
  c.centerWindow + c.widthWindow + c.scalingErrorWindow + c.slack

theorem criticalWindow_certificateBudgetWindow_le_size
    {c : CriticalWindowRefinementCertificate}
    (h : criticalWindowRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCriticalWindowRefinementCertificate :
    CriticalWindowRefinementCertificate :=
  { centerWindow := 10, widthWindow := 3, scalingErrorWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : criticalWindowRefinementReady
    sampleCriticalWindowRefinementCertificate := by
  norm_num [criticalWindowRefinementReady,
    CriticalWindowRefinementCertificate.widthControlled,
    CriticalWindowRefinementCertificate.certificateBudgetControlled,
    sampleCriticalWindowRefinementCertificate]

example :
    sampleCriticalWindowRefinementCertificate.certificateBudgetWindow ≤
      sampleCriticalWindowRefinementCertificate.size := by
  norm_num [CriticalWindowRefinementCertificate.size,
    sampleCriticalWindowRefinementCertificate]

/-- A second-stage critical-window certificate with a named external budget. -/
structure CriticalWindowBudgetCertificate where
  centerWindow : ℕ
  widthWindow : ℕ
  scalingErrorWindow : ℕ
  criticalBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CriticalWindowBudgetCertificate.windowControlled
    (cert : CriticalWindowBudgetCertificate) : Prop :=
  0 < cert.widthWindow ∧
    cert.criticalBudgetWindow ≤
      cert.centerWindow + cert.widthWindow + cert.scalingErrorWindow + cert.slack

def CriticalWindowBudgetCertificate.budgetControlled
    (cert : CriticalWindowBudgetCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.centerWindow + cert.widthWindow + cert.scalingErrorWindow +
      cert.criticalBudgetWindow + cert.slack

def criticalWindowBudgetReady (cert : CriticalWindowBudgetCertificate) : Prop :=
  cert.windowControlled ∧ cert.budgetControlled

def CriticalWindowBudgetCertificate.size
    (cert : CriticalWindowBudgetCertificate) : ℕ :=
  cert.centerWindow + cert.widthWindow + cert.scalingErrorWindow +
    cert.criticalBudgetWindow + cert.slack

theorem criticalWindow_budgetCertificate_le_size
    (cert : CriticalWindowBudgetCertificate)
    (h : criticalWindowBudgetReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCriticalWindowBudgetCertificate :
    CriticalWindowBudgetCertificate :=
  { centerWindow := 10, widthWindow := 3, scalingErrorWindow := 2,
    criticalBudgetWindow := 16, certificateBudgetWindow := 32, slack := 1 }

example : criticalWindowBudgetReady sampleCriticalWindowBudgetCertificate := by
  norm_num [criticalWindowBudgetReady,
    CriticalWindowBudgetCertificate.windowControlled,
    CriticalWindowBudgetCertificate.budgetControlled,
    sampleCriticalWindowBudgetCertificate]

example :
    sampleCriticalWindowBudgetCertificate.certificateBudgetWindow ≤
      sampleCriticalWindowBudgetCertificate.size := by
  apply criticalWindow_budgetCertificate_le_size
  norm_num [criticalWindowBudgetReady,
    CriticalWindowBudgetCertificate.windowControlled,
    CriticalWindowBudgetCertificate.budgetControlled,
    sampleCriticalWindowBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    criticalWindowBudgetReady sampleCriticalWindowBudgetCertificate := by
  constructor
  · norm_num [CriticalWindowBudgetCertificate.windowControlled,
      sampleCriticalWindowBudgetCertificate]
  · norm_num [CriticalWindowBudgetCertificate.budgetControlled,
      sampleCriticalWindowBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCriticalWindowBudgetCertificate.certificateBudgetWindow ≤
      sampleCriticalWindowBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List CriticalWindowBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCriticalWindowBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleCriticalWindowBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.CriticalWindowSchemas
