import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic scale windows.

The finite schema records analytic radius, scale window, and error slack.
-/

namespace AnalyticCombinatorics.Asymptotics.AnalyticScaleWindows

structure AnalyticScaleWindowData where
  analyticRadius : ℕ
  scaleWindow : ℕ
  errorSlack : ℕ
deriving DecidableEq, Repr

def analyticRadiusPositive (d : AnalyticScaleWindowData) : Prop :=
  0 < d.analyticRadius

def scaleWindowControlled (d : AnalyticScaleWindowData) : Prop :=
  d.scaleWindow ≤ d.analyticRadius + d.errorSlack

def analyticScaleWindowReady (d : AnalyticScaleWindowData) : Prop :=
  analyticRadiusPositive d ∧ scaleWindowControlled d

def analyticScaleWindowBudget (d : AnalyticScaleWindowData) : ℕ :=
  d.analyticRadius + d.scaleWindow + d.errorSlack

theorem analyticScaleWindowReady.radius {d : AnalyticScaleWindowData}
    (h : analyticScaleWindowReady d) :
    analyticRadiusPositive d ∧ scaleWindowControlled d ∧
      d.scaleWindow ≤ analyticScaleWindowBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold analyticScaleWindowBudget
  omega

theorem scaleWindow_le_analyticScaleBudget (d : AnalyticScaleWindowData) :
    d.scaleWindow ≤ analyticScaleWindowBudget d := by
  unfold analyticScaleWindowBudget
  omega

def sampleAnalyticScaleWindowData : AnalyticScaleWindowData :=
  { analyticRadius := 5, scaleWindow := 7, errorSlack := 3 }

example : analyticScaleWindowReady sampleAnalyticScaleWindowData := by
  norm_num [analyticScaleWindowReady, analyticRadiusPositive]
  norm_num [scaleWindowControlled, sampleAnalyticScaleWindowData]

example : analyticScaleWindowBudget sampleAnalyticScaleWindowData = 15 := by
  native_decide

/-- Finite executable readiness audit for analytic scale windows. -/
def analyticScaleWindowListReady
    (windows : List AnalyticScaleWindowData) : Bool :=
  windows.all fun d =>
    0 < d.analyticRadius && d.scaleWindow ≤ d.analyticRadius + d.errorSlack

theorem analyticScaleWindowList_readyWindow :
    analyticScaleWindowListReady
      [{ analyticRadius := 3, scaleWindow := 4, errorSlack := 1 },
       { analyticRadius := 5, scaleWindow := 7, errorSlack := 3 }] = true := by
  unfold analyticScaleWindowListReady
  native_decide

structure AnalyticScaleCertificateWindow where
  radiusWindow : ℕ
  scaleWindow : ℕ
  errorSlack : ℕ
  scaleBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticScaleCertificateWindow.scaleControlled
    (w : AnalyticScaleCertificateWindow) : Prop :=
  w.scaleWindow ≤ w.radiusWindow + w.errorSlack + w.slack

def analyticScaleCertificateReady (w : AnalyticScaleCertificateWindow) : Prop :=
  0 < w.radiusWindow ∧ w.scaleControlled ∧
    w.scaleBudget ≤ w.radiusWindow + w.scaleWindow + w.slack

def AnalyticScaleCertificateWindow.certificate
    (w : AnalyticScaleCertificateWindow) : ℕ :=
  w.radiusWindow + w.scaleWindow + w.errorSlack + w.scaleBudget + w.slack

theorem analyticScale_scaleBudget_le_certificate
    (w : AnalyticScaleCertificateWindow) :
    w.scaleBudget ≤ w.certificate := by
  unfold AnalyticScaleCertificateWindow.certificate
  omega

def sampleAnalyticScaleCertificateWindow :
    AnalyticScaleCertificateWindow :=
  { radiusWindow := 5, scaleWindow := 7, errorSlack := 2,
    scaleBudget := 14, slack := 2 }

example : analyticScaleCertificateReady sampleAnalyticScaleCertificateWindow := by
  norm_num [analyticScaleCertificateReady,
    AnalyticScaleCertificateWindow.scaleControlled, sampleAnalyticScaleCertificateWindow]

/-- A refinement certificate for analytic scale windows. -/
structure AnalyticScaleRefinementCertificate where
  radiusWindow : ℕ
  scaleWindow : ℕ
  errorSlackWindow : ℕ
  scaleBudgetWindow : ℕ
  slack : ℕ

/-- Scale and budget windows are controlled by analytic radius. -/
def analyticScaleRefinementCertificateControlled
    (w : AnalyticScaleRefinementCertificate) : Prop :=
  0 < w.radiusWindow ∧
    w.scaleWindow ≤ w.radiusWindow + w.errorSlackWindow + w.slack ∧
      w.scaleBudgetWindow ≤ w.radiusWindow + w.scaleWindow + w.slack

/-- Readiness for an analytic scale refinement certificate. -/
def analyticScaleRefinementCertificateReady
    (w : AnalyticScaleRefinementCertificate) : Prop :=
  analyticScaleRefinementCertificateControlled w ∧
    w.scaleBudgetWindow ≤
      w.radiusWindow + w.scaleWindow + w.errorSlackWindow +
        w.scaleBudgetWindow + w.slack

/-- Total size of an analytic scale refinement certificate. -/
def analyticScaleRefinementCertificateSize
    (w : AnalyticScaleRefinementCertificate) : ℕ :=
  w.radiusWindow + w.scaleWindow + w.errorSlackWindow +
    w.scaleBudgetWindow + w.slack

theorem analyticScaleRefinementCertificate_budget_le_size
    (w : AnalyticScaleRefinementCertificate)
    (h : analyticScaleRefinementCertificateReady w) :
    w.scaleBudgetWindow ≤ analyticScaleRefinementCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold analyticScaleRefinementCertificateSize
  omega

def sampleAnalyticScaleRefinementCertificate :
    AnalyticScaleRefinementCertificate where
  radiusWindow := 5
  scaleWindow := 7
  errorSlackWindow := 2
  scaleBudgetWindow := 14
  slack := 2

example :
    analyticScaleRefinementCertificateReady
      sampleAnalyticScaleRefinementCertificate := by
  norm_num [analyticScaleRefinementCertificateReady,
    analyticScaleRefinementCertificateControlled,
    sampleAnalyticScaleRefinementCertificate]

example :
    sampleAnalyticScaleRefinementCertificate.scaleBudgetWindow ≤
      analyticScaleRefinementCertificateSize
        sampleAnalyticScaleRefinementCertificate := by
  apply analyticScaleRefinementCertificate_budget_le_size
  norm_num [analyticScaleRefinementCertificateReady,
    analyticScaleRefinementCertificateControlled,
    sampleAnalyticScaleRefinementCertificate]

/-- A second-stage certificate with the analytic-scale budget separated from size. -/
structure AnalyticScaleBudgetCertificate where
  radiusWindow : ℕ
  scaleWindow : ℕ
  errorSlackWindow : ℕ
  scaleBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticScaleBudgetCertificate.scaleControlled
    (cert : AnalyticScaleBudgetCertificate) : Prop :=
  0 < cert.radiusWindow ∧
    cert.scaleWindow ≤ cert.radiusWindow + cert.errorSlackWindow + cert.slack ∧
      cert.scaleBudgetWindow ≤ cert.radiusWindow + cert.scaleWindow + cert.slack

def AnalyticScaleBudgetCertificate.budgetControlled
    (cert : AnalyticScaleBudgetCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.radiusWindow + cert.scaleWindow + cert.errorSlackWindow +
      cert.scaleBudgetWindow + cert.slack

def analyticScaleBudgetReady (cert : AnalyticScaleBudgetCertificate) : Prop :=
  cert.scaleControlled ∧ cert.budgetControlled

def AnalyticScaleBudgetCertificate.size
    (cert : AnalyticScaleBudgetCertificate) : ℕ :=
  cert.radiusWindow + cert.scaleWindow + cert.errorSlackWindow +
    cert.scaleBudgetWindow + cert.slack

theorem analyticScale_certificateBudgetWindow_le_size
    (cert : AnalyticScaleBudgetCertificate)
    (h : analyticScaleBudgetReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticScaleBudgetCertificate :
    AnalyticScaleBudgetCertificate :=
  { radiusWindow := 5, scaleWindow := 7, errorSlackWindow := 2,
    scaleBudgetWindow := 14, certificateBudgetWindow := 30, slack := 2 }

example : analyticScaleBudgetReady sampleAnalyticScaleBudgetCertificate := by
  norm_num [analyticScaleBudgetReady,
    AnalyticScaleBudgetCertificate.scaleControlled,
    AnalyticScaleBudgetCertificate.budgetControlled,
    sampleAnalyticScaleBudgetCertificate]

example :
    sampleAnalyticScaleBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticScaleBudgetCertificate.size := by
  apply analyticScale_certificateBudgetWindow_le_size
  norm_num [analyticScaleBudgetReady,
    AnalyticScaleBudgetCertificate.scaleControlled,
    AnalyticScaleBudgetCertificate.budgetControlled,
    sampleAnalyticScaleBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    analyticScaleBudgetReady sampleAnalyticScaleBudgetCertificate := by
  constructor
  · norm_num [AnalyticScaleBudgetCertificate.scaleControlled,
      sampleAnalyticScaleBudgetCertificate]
  · norm_num [AnalyticScaleBudgetCertificate.budgetControlled,
      sampleAnalyticScaleBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticScaleBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticScaleBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List AnalyticScaleBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticScaleBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleAnalyticScaleBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.AnalyticScaleWindows
