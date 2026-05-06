import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform threshold schema bookkeeping.

The finite data records threshold location, window width, and uniform error
for phase transition estimates.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformThresholdSchemas

structure ThresholdData where
  threshold : ℕ
  windowWidth : ℕ
  errorBudget : ℕ
deriving DecidableEq, Repr

def positiveWindowWidth (d : ThresholdData) : Prop :=
  0 < d.windowWidth

def thresholdReady (d : ThresholdData) : Prop :=
  positiveWindowWidth d

def lowerThreshold (d : ThresholdData) : ℕ :=
  d.threshold - d.windowWidth

def upperThreshold (d : ThresholdData) : ℕ :=
  d.threshold + d.windowWidth

def thresholdBudget (d : ThresholdData) : ℕ :=
  d.windowWidth + d.errorBudget

theorem lowerThreshold_le_threshold (d : ThresholdData) :
    lowerThreshold d ≤ d.threshold := by
  unfold lowerThreshold
  omega

theorem windowWidth_le_thresholdBudget (d : ThresholdData) :
    d.windowWidth ≤ thresholdBudget d := by
  unfold thresholdBudget
  omega

def sampleThreshold : ThresholdData :=
  { threshold := 12, windowWidth := 4, errorBudget := 3 }

example : thresholdReady sampleThreshold := by
  norm_num [thresholdReady, positiveWindowWidth, sampleThreshold]

example : lowerThreshold sampleThreshold = 8 := by
  native_decide

example : upperThreshold sampleThreshold = 16 := by
  native_decide

/-- Finite executable readiness audit for threshold data. -/
def thresholdDataListReady (data : List ThresholdData) : Bool :=
  data.all fun d => 0 < d.windowWidth

theorem thresholdDataList_readyWindow :
    thresholdDataListReady
      [{ threshold := 12, windowWidth := 4, errorBudget := 3 },
       { threshold := 20, windowWidth := 5, errorBudget := 2 }] = true := by
  unfold thresholdDataListReady
  native_decide

/-- A certificate window for uniform threshold bookkeeping. -/
structure ThresholdCertificateWindow where
  thresholdWindow : ℕ
  widthWindow : ℕ
  errorWindow : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- Threshold certificates require positive window width. -/
def thresholdCertificateControlled
    (w : ThresholdCertificateWindow) : Prop :=
  0 < w.widthWindow

/-- Readiness for a threshold certificate. -/
def thresholdCertificateReady
    (w : ThresholdCertificateWindow) : Prop :=
  thresholdCertificateControlled w ∧
    w.certificateBudget ≤ w.widthWindow + w.errorWindow + w.slack

/-- Total size of a threshold certificate. -/
def thresholdCertificate (w : ThresholdCertificateWindow) : ℕ :=
  w.thresholdWindow + w.widthWindow + w.errorWindow + w.certificateBudget + w.slack

theorem thresholdCertificate_budget_le_certificate
    (w : ThresholdCertificateWindow)
    (h : thresholdCertificateReady w) :
    w.certificateBudget ≤ thresholdCertificate w := by
  rcases h with ⟨_, hbudget⟩
  unfold thresholdCertificate
  omega

def sampleThresholdCertificateWindow : ThresholdCertificateWindow where
  thresholdWindow := 12
  widthWindow := 4
  errorWindow := 3
  certificateBudget := 7
  slack := 1

example :
    thresholdCertificateReady sampleThresholdCertificateWindow := by
  norm_num [thresholdCertificateReady,
    thresholdCertificateControlled, sampleThresholdCertificateWindow]

example :
    sampleThresholdCertificateWindow.certificateBudget ≤
      thresholdCertificate sampleThresholdCertificateWindow := by
  apply thresholdCertificate_budget_le_certificate
  norm_num [thresholdCertificateReady,
    thresholdCertificateControlled, sampleThresholdCertificateWindow]

structure ThresholdRefinementCertificate where
  thresholdWindow : ℕ
  widthWindow : ℕ
  errorWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ThresholdRefinementCertificate.widthControlled
    (c : ThresholdRefinementCertificate) : Prop :=
  0 < c.widthWindow

def ThresholdRefinementCertificate.certificateBudgetControlled
    (c : ThresholdRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.thresholdWindow + c.widthWindow + c.errorWindow + c.slack

def thresholdRefinementReady
    (c : ThresholdRefinementCertificate) : Prop :=
  c.widthControlled ∧ c.certificateBudgetControlled

def ThresholdRefinementCertificate.size
    (c : ThresholdRefinementCertificate) : ℕ :=
  c.thresholdWindow + c.widthWindow + c.errorWindow + c.slack

theorem threshold_certificateBudgetWindow_le_size
    {c : ThresholdRefinementCertificate}
    (h : thresholdRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleThresholdRefinementCertificate :
    ThresholdRefinementCertificate :=
  { thresholdWindow := 12, widthWindow := 4, errorWindow := 3,
    certificateBudgetWindow := 20, slack := 1 }

example : thresholdRefinementReady
    sampleThresholdRefinementCertificate := by
  norm_num [thresholdRefinementReady,
    ThresholdRefinementCertificate.widthControlled,
    ThresholdRefinementCertificate.certificateBudgetControlled,
    sampleThresholdRefinementCertificate]

example :
    sampleThresholdRefinementCertificate.certificateBudgetWindow ≤
      sampleThresholdRefinementCertificate.size := by
  norm_num [ThresholdRefinementCertificate.size,
    sampleThresholdRefinementCertificate]

/-- A second-stage uniform-threshold certificate with a named external budget. -/
structure ThresholdBudgetCertificate where
  thresholdWindow : ℕ
  widthWindow : ℕ
  errorWindow : ℕ
  thresholdBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ThresholdBudgetCertificate.thresholdControlled
    (cert : ThresholdBudgetCertificate) : Prop :=
  0 < cert.widthWindow ∧
    cert.thresholdBudgetWindow ≤
      cert.thresholdWindow + cert.widthWindow + cert.errorWindow + cert.slack

def ThresholdBudgetCertificate.budgetControlled
    (cert : ThresholdBudgetCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.thresholdWindow + cert.widthWindow + cert.errorWindow +
      cert.thresholdBudgetWindow + cert.slack

def thresholdBudgetReady (cert : ThresholdBudgetCertificate) : Prop :=
  cert.thresholdControlled ∧ cert.budgetControlled

def ThresholdBudgetCertificate.size
    (cert : ThresholdBudgetCertificate) : ℕ :=
  cert.thresholdWindow + cert.widthWindow + cert.errorWindow +
    cert.thresholdBudgetWindow + cert.slack

theorem threshold_budgetCertificate_le_size
    (cert : ThresholdBudgetCertificate)
    (h : thresholdBudgetReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleThresholdBudgetCertificate :
    ThresholdBudgetCertificate :=
  { thresholdWindow := 12, widthWindow := 4, errorWindow := 3,
    thresholdBudgetWindow := 20, certificateBudgetWindow := 40, slack := 1 }

example : thresholdBudgetReady sampleThresholdBudgetCertificate := by
  norm_num [thresholdBudgetReady,
    ThresholdBudgetCertificate.thresholdControlled,
    ThresholdBudgetCertificate.budgetControlled,
    sampleThresholdBudgetCertificate]

example :
    sampleThresholdBudgetCertificate.certificateBudgetWindow ≤
      sampleThresholdBudgetCertificate.size := by
  apply threshold_budgetCertificate_le_size
  norm_num [thresholdBudgetReady,
    ThresholdBudgetCertificate.thresholdControlled,
    ThresholdBudgetCertificate.budgetControlled,
    sampleThresholdBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    thresholdBudgetReady sampleThresholdBudgetCertificate := by
  constructor
  · norm_num [ThresholdBudgetCertificate.thresholdControlled,
      sampleThresholdBudgetCertificate]
  · norm_num [ThresholdBudgetCertificate.budgetControlled,
      sampleThresholdBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleThresholdBudgetCertificate.certificateBudgetWindow ≤
      sampleThresholdBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List ThresholdBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleThresholdBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleThresholdBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformThresholdSchemas
