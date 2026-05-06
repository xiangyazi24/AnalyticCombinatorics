import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Critical scale windows.

The finite schema records critical scale, window width, and perturbation
slack.
-/

namespace AnalyticCombinatorics.Asymptotics.CriticalScaleWindows

structure CriticalScaleWindowData where
  criticalScale : ℕ
  windowWidth : ℕ
  perturbationSlack : ℕ
deriving DecidableEq, Repr

def criticalScalePositive (d : CriticalScaleWindowData) : Prop :=
  0 < d.criticalScale

def windowWidthControlled (d : CriticalScaleWindowData) : Prop :=
  d.windowWidth ≤ d.criticalScale + d.perturbationSlack

def criticalScaleWindowReady (d : CriticalScaleWindowData) : Prop :=
  criticalScalePositive d ∧ windowWidthControlled d

def criticalScaleWindowBudget (d : CriticalScaleWindowData) : ℕ :=
  d.criticalScale + d.windowWidth + d.perturbationSlack

theorem criticalScaleWindowReady.scale {d : CriticalScaleWindowData}
    (h : criticalScaleWindowReady d) :
    criticalScalePositive d ∧ windowWidthControlled d ∧
      d.windowWidth ≤ criticalScaleWindowBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold criticalScaleWindowBudget
  omega

theorem windowWidth_le_criticalScaleBudget (d : CriticalScaleWindowData) :
    d.windowWidth ≤ criticalScaleWindowBudget d := by
  unfold criticalScaleWindowBudget
  omega

def sampleCriticalScaleWindowData : CriticalScaleWindowData :=
  { criticalScale := 6, windowWidth := 8, perturbationSlack := 3 }

example : criticalScaleWindowReady sampleCriticalScaleWindowData := by
  norm_num [criticalScaleWindowReady, criticalScalePositive]
  norm_num [windowWidthControlled, sampleCriticalScaleWindowData]

example : criticalScaleWindowBudget sampleCriticalScaleWindowData = 17 := by
  native_decide

/-- Finite executable readiness audit for critical scale windows. -/
def criticalScaleWindowListReady
    (windows : List CriticalScaleWindowData) : Bool :=
  windows.all fun d =>
    0 < d.criticalScale && d.windowWidth ≤ d.criticalScale + d.perturbationSlack

theorem criticalScaleWindowList_readyWindow :
    criticalScaleWindowListReady
      [{ criticalScale := 4, windowWidth := 5, perturbationSlack := 1 },
       { criticalScale := 6, windowWidth := 8, perturbationSlack := 3 }] = true := by
  unfold criticalScaleWindowListReady
  native_decide

/-- A certificate window for critical scale control. -/
structure CriticalScaleCertificateWindow where
  criticalWindow : ℕ
  widthWindow : ℕ
  perturbationSlack : ℕ
  criticalBudget : ℕ
  slack : ℕ

/-- The width window is controlled by the critical scale. -/
def criticalScaleCertificateControlled
    (w : CriticalScaleCertificateWindow) : Prop :=
  w.widthWindow ≤ w.criticalWindow + w.perturbationSlack + w.slack

/-- Readiness for a critical scale certificate window. -/
def criticalScaleCertificateReady
    (w : CriticalScaleCertificateWindow) : Prop :=
  0 < w.criticalWindow ∧
    criticalScaleCertificateControlled w ∧
      w.criticalBudget ≤ w.criticalWindow + w.widthWindow + w.slack

/-- Total size of the critical scale certificate. -/
def criticalScaleCertificate (w : CriticalScaleCertificateWindow) : ℕ :=
  w.criticalWindow + w.widthWindow + w.perturbationSlack + w.criticalBudget + w.slack

theorem criticalScaleCertificate_budget_le_certificate
    (w : CriticalScaleCertificateWindow)
    (h : criticalScaleCertificateReady w) :
    w.criticalBudget ≤ criticalScaleCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold criticalScaleCertificate
  omega

def sampleCriticalScaleCertificateWindow : CriticalScaleCertificateWindow where
  criticalWindow := 6
  widthWindow := 7
  perturbationSlack := 2
  criticalBudget := 12
  slack := 1

example :
    criticalScaleCertificateReady sampleCriticalScaleCertificateWindow := by
  norm_num [criticalScaleCertificateReady,
    criticalScaleCertificateControlled, sampleCriticalScaleCertificateWindow]

example :
    sampleCriticalScaleCertificateWindow.criticalBudget ≤
      criticalScaleCertificate sampleCriticalScaleCertificateWindow := by
  apply criticalScaleCertificate_budget_le_certificate
  norm_num [criticalScaleCertificateReady,
    criticalScaleCertificateControlled, sampleCriticalScaleCertificateWindow]

structure CriticalScaleRefinementCertificate where
  criticalWindow : ℕ
  widthWindow : ℕ
  perturbationSlackWindow : ℕ
  criticalBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CriticalScaleRefinementCertificate.widthControlled
    (c : CriticalScaleRefinementCertificate) : Prop :=
  c.widthWindow ≤ c.criticalWindow + c.perturbationSlackWindow + c.slack

def CriticalScaleRefinementCertificate.criticalBudgetControlled
    (c : CriticalScaleRefinementCertificate) : Prop :=
  c.criticalBudgetWindow ≤
    c.criticalWindow + c.widthWindow + c.perturbationSlackWindow + c.slack

def criticalScaleRefinementReady
    (c : CriticalScaleRefinementCertificate) : Prop :=
  0 < c.criticalWindow ∧
    c.widthControlled ∧
    c.criticalBudgetControlled

def CriticalScaleRefinementCertificate.size
    (c : CriticalScaleRefinementCertificate) : ℕ :=
  c.criticalWindow + c.widthWindow + c.perturbationSlackWindow + c.slack

theorem criticalScale_criticalBudgetWindow_le_size
    {c : CriticalScaleRefinementCertificate}
    (h : criticalScaleRefinementReady c) :
    c.criticalBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleCriticalScaleRefinementCertificate :
    CriticalScaleRefinementCertificate :=
  { criticalWindow := 6, widthWindow := 7, perturbationSlackWindow := 2,
    criticalBudgetWindow := 16, slack := 1 }

example : criticalScaleRefinementReady
    sampleCriticalScaleRefinementCertificate := by
  norm_num [criticalScaleRefinementReady,
    CriticalScaleRefinementCertificate.widthControlled,
    CriticalScaleRefinementCertificate.criticalBudgetControlled,
    sampleCriticalScaleRefinementCertificate]

example :
    sampleCriticalScaleRefinementCertificate.criticalBudgetWindow ≤
      sampleCriticalScaleRefinementCertificate.size := by
  norm_num [CriticalScaleRefinementCertificate.size,
    sampleCriticalScaleRefinementCertificate]

/-- A second-stage critical-scale certificate with a named external budget. -/
structure CriticalScaleBudgetCertificate where
  criticalWindow : ℕ
  widthWindow : ℕ
  perturbationSlackWindow : ℕ
  criticalBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CriticalScaleBudgetCertificate.scaleControlled
    (cert : CriticalScaleBudgetCertificate) : Prop :=
  0 < cert.criticalWindow ∧
    cert.widthWindow ≤ cert.criticalWindow + cert.perturbationSlackWindow + cert.slack ∧
      cert.criticalBudgetWindow ≤
        cert.criticalWindow + cert.widthWindow + cert.perturbationSlackWindow + cert.slack

def CriticalScaleBudgetCertificate.budgetControlled
    (cert : CriticalScaleBudgetCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.criticalWindow + cert.widthWindow + cert.perturbationSlackWindow +
      cert.criticalBudgetWindow + cert.slack

def criticalScaleBudgetReady (cert : CriticalScaleBudgetCertificate) : Prop :=
  cert.scaleControlled ∧ cert.budgetControlled

def CriticalScaleBudgetCertificate.size
    (cert : CriticalScaleBudgetCertificate) : ℕ :=
  cert.criticalWindow + cert.widthWindow + cert.perturbationSlackWindow +
    cert.criticalBudgetWindow + cert.slack

theorem criticalScale_budgetCertificate_le_size
    (cert : CriticalScaleBudgetCertificate)
    (h : criticalScaleBudgetReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCriticalScaleBudgetCertificate :
    CriticalScaleBudgetCertificate :=
  { criticalWindow := 6, widthWindow := 7, perturbationSlackWindow := 2,
    criticalBudgetWindow := 16, certificateBudgetWindow := 32, slack := 1 }

example : criticalScaleBudgetReady sampleCriticalScaleBudgetCertificate := by
  norm_num [criticalScaleBudgetReady,
    CriticalScaleBudgetCertificate.scaleControlled,
    CriticalScaleBudgetCertificate.budgetControlled,
    sampleCriticalScaleBudgetCertificate]

example :
    sampleCriticalScaleBudgetCertificate.certificateBudgetWindow ≤
      sampleCriticalScaleBudgetCertificate.size := by
  apply criticalScale_budgetCertificate_le_size
  norm_num [criticalScaleBudgetReady,
    CriticalScaleBudgetCertificate.scaleControlled,
    CriticalScaleBudgetCertificate.budgetControlled,
    sampleCriticalScaleBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    criticalScaleBudgetReady sampleCriticalScaleBudgetCertificate := by
  constructor
  · norm_num [CriticalScaleBudgetCertificate.scaleControlled,
      sampleCriticalScaleBudgetCertificate]
  · norm_num [CriticalScaleBudgetCertificate.budgetControlled,
      sampleCriticalScaleBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCriticalScaleBudgetCertificate.certificateBudgetWindow ≤
      sampleCriticalScaleBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List CriticalScaleBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCriticalScaleBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleCriticalScaleBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.CriticalScaleWindows
