import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform quantile windows.

The finite record stores quantile rank, scale budget, and tail slack.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformQuantileWindows

structure UniformQuantileWindowData where
  quantileRank : ℕ
  scaleBudget : ℕ
  tailSlack : ℕ
deriving DecidableEq, Repr

def scaleBudgetPositive (d : UniformQuantileWindowData) : Prop :=
  0 < d.scaleBudget

def quantileRankControlled (d : UniformQuantileWindowData) : Prop :=
  d.quantileRank ≤ d.scaleBudget + d.tailSlack

def uniformQuantileWindowReady (d : UniformQuantileWindowData) : Prop :=
  scaleBudgetPositive d ∧ quantileRankControlled d

def uniformQuantileWindowBudget (d : UniformQuantileWindowData) : ℕ :=
  d.quantileRank + d.scaleBudget + d.tailSlack

theorem uniformQuantileWindowReady.scale {d : UniformQuantileWindowData}
    (h : uniformQuantileWindowReady d) :
    scaleBudgetPositive d ∧ quantileRankControlled d ∧
      d.quantileRank ≤ uniformQuantileWindowBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold uniformQuantileWindowBudget
  omega

theorem quantileRank_le_quantileWindowBudget
    (d : UniformQuantileWindowData) :
    d.quantileRank ≤ uniformQuantileWindowBudget d := by
  unfold uniformQuantileWindowBudget
  omega

def sampleUniformQuantileWindowData : UniformQuantileWindowData :=
  { quantileRank := 7, scaleBudget := 5, tailSlack := 3 }

example : uniformQuantileWindowReady sampleUniformQuantileWindowData := by
  norm_num [uniformQuantileWindowReady, scaleBudgetPositive]
  norm_num [quantileRankControlled, sampleUniformQuantileWindowData]

example : uniformQuantileWindowBudget sampleUniformQuantileWindowData = 15 := by
  native_decide

/-- Finite executable readiness audit for uniform quantile windows. -/
def uniformQuantileWindowDataListReady
    (data : List UniformQuantileWindowData) : Bool :=
  data.all fun d =>
    0 < d.scaleBudget && d.quantileRank ≤ d.scaleBudget + d.tailSlack

theorem uniformQuantileWindowDataList_readyWindow :
    uniformQuantileWindowDataListReady
      [{ quantileRank := 4, scaleBudget := 5, tailSlack := 1 },
       { quantileRank := 7, scaleBudget := 5, tailSlack := 3 }] = true := by
  unfold uniformQuantileWindowDataListReady
  native_decide

/-- A certificate window for uniform quantile control. -/
structure UniformQuantileCertificateWindow where
  quantileWindow : ℕ
  scaleWindow : ℕ
  tailSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- Quantile rank is controlled by scale and tail slack. -/
def uniformQuantileCertificateControlled
    (w : UniformQuantileCertificateWindow) : Prop :=
  w.quantileWindow ≤ w.scaleWindow + w.tailSlack + w.slack

/-- Readiness for a uniform quantile certificate. -/
def uniformQuantileCertificateReady
    (w : UniformQuantileCertificateWindow) : Prop :=
  0 < w.scaleWindow ∧
    uniformQuantileCertificateControlled w ∧
      w.certificateBudget ≤ w.quantileWindow + w.scaleWindow + w.slack

/-- Total size of a uniform quantile certificate. -/
def uniformQuantileCertificate
    (w : UniformQuantileCertificateWindow) : ℕ :=
  w.quantileWindow + w.scaleWindow + w.tailSlack + w.certificateBudget + w.slack

theorem uniformQuantileCertificate_budget_le_certificate
    (w : UniformQuantileCertificateWindow)
    (h : uniformQuantileCertificateReady w) :
    w.certificateBudget ≤ uniformQuantileCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold uniformQuantileCertificate
  omega

def sampleUniformQuantileCertificateWindow :
    UniformQuantileCertificateWindow where
  quantileWindow := 6
  scaleWindow := 7
  tailSlack := 2
  certificateBudget := 12
  slack := 1

example :
    uniformQuantileCertificateReady sampleUniformQuantileCertificateWindow := by
  norm_num [uniformQuantileCertificateReady,
    uniformQuantileCertificateControlled, sampleUniformQuantileCertificateWindow]

example :
    sampleUniformQuantileCertificateWindow.certificateBudget ≤
      uniformQuantileCertificate sampleUniformQuantileCertificateWindow := by
  apply uniformQuantileCertificate_budget_le_certificate
  norm_num [uniformQuantileCertificateReady,
    uniformQuantileCertificateControlled, sampleUniformQuantileCertificateWindow]

structure UniformQuantileRefinementCertificate where
  quantileWindow : ℕ
  scaleWindow : ℕ
  tailSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformQuantileRefinementCertificate.quantileControlled
    (c : UniformQuantileRefinementCertificate) : Prop :=
  c.quantileWindow ≤ c.scaleWindow + c.tailSlackWindow + c.slack

def UniformQuantileRefinementCertificate.certificateBudgetControlled
    (c : UniformQuantileRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.quantileWindow + c.scaleWindow + c.tailSlackWindow + c.slack

def uniformQuantileRefinementReady
    (c : UniformQuantileRefinementCertificate) : Prop :=
  0 < c.scaleWindow ∧ c.quantileControlled ∧ c.certificateBudgetControlled

def UniformQuantileRefinementCertificate.size
    (c : UniformQuantileRefinementCertificate) : ℕ :=
  c.quantileWindow + c.scaleWindow + c.tailSlackWindow + c.slack

theorem uniformQuantile_certificateBudgetWindow_le_size
    {c : UniformQuantileRefinementCertificate}
    (h : uniformQuantileRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleUniformQuantileRefinementCertificate :
    UniformQuantileRefinementCertificate :=
  { quantileWindow := 6, scaleWindow := 7, tailSlackWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : uniformQuantileRefinementReady
    sampleUniformQuantileRefinementCertificate := by
  norm_num [uniformQuantileRefinementReady,
    UniformQuantileRefinementCertificate.quantileControlled,
    UniformQuantileRefinementCertificate.certificateBudgetControlled,
    sampleUniformQuantileRefinementCertificate]

example :
    sampleUniformQuantileRefinementCertificate.certificateBudgetWindow ≤
      sampleUniformQuantileRefinementCertificate.size := by
  norm_num [UniformQuantileRefinementCertificate.size,
    sampleUniformQuantileRefinementCertificate]

/-- A second-stage uniform-quantile certificate with a named external budget. -/
structure UniformQuantileBudgetCertificate where
  quantileWindow : ℕ
  scaleWindow : ℕ
  tailSlackWindow : ℕ
  quantileBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformQuantileBudgetCertificate.quantileControlled
    (cert : UniformQuantileBudgetCertificate) : Prop :=
  0 < cert.scaleWindow ∧
    cert.quantileWindow ≤ cert.scaleWindow + cert.tailSlackWindow + cert.slack ∧
      cert.quantileBudgetWindow ≤
        cert.quantileWindow + cert.scaleWindow + cert.tailSlackWindow + cert.slack

def UniformQuantileBudgetCertificate.budgetControlled
    (cert : UniformQuantileBudgetCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.quantileWindow + cert.scaleWindow + cert.tailSlackWindow +
      cert.quantileBudgetWindow + cert.slack

def uniformQuantileBudgetReady
    (cert : UniformQuantileBudgetCertificate) : Prop :=
  cert.quantileControlled ∧ cert.budgetControlled

def UniformQuantileBudgetCertificate.size
    (cert : UniformQuantileBudgetCertificate) : ℕ :=
  cert.quantileWindow + cert.scaleWindow + cert.tailSlackWindow +
    cert.quantileBudgetWindow + cert.slack

theorem uniformQuantile_budgetCertificate_le_size
    (cert : UniformQuantileBudgetCertificate)
    (h : uniformQuantileBudgetReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformQuantileBudgetCertificate :
    UniformQuantileBudgetCertificate :=
  { quantileWindow := 6, scaleWindow := 7, tailSlackWindow := 2,
    quantileBudgetWindow := 16, certificateBudgetWindow := 32, slack := 1 }

example : uniformQuantileBudgetReady sampleUniformQuantileBudgetCertificate := by
  norm_num [uniformQuantileBudgetReady,
    UniformQuantileBudgetCertificate.quantileControlled,
    UniformQuantileBudgetCertificate.budgetControlled,
    sampleUniformQuantileBudgetCertificate]

example :
    sampleUniformQuantileBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformQuantileBudgetCertificate.size := by
  apply uniformQuantile_budgetCertificate_le_size
  norm_num [uniformQuantileBudgetReady,
    UniformQuantileBudgetCertificate.quantileControlled,
    UniformQuantileBudgetCertificate.budgetControlled,
    sampleUniformQuantileBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    uniformQuantileBudgetReady sampleUniformQuantileBudgetCertificate := by
  constructor
  · norm_num [UniformQuantileBudgetCertificate.quantileControlled,
      sampleUniformQuantileBudgetCertificate]
  · norm_num [UniformQuantileBudgetCertificate.budgetControlled,
      sampleUniformQuantileBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformQuantileBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformQuantileBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List UniformQuantileBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformQuantileBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformQuantileBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformQuantileWindows
