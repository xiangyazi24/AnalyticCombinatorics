import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform ratio asymptotics.

The finite schema records numerator scale, denominator scale, and
uniform slack.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformRatioAsymptotics

structure UniformRatioData where
  numeratorScale : ℕ
  denominatorScale : ℕ
  uniformSlack : ℕ
deriving DecidableEq, Repr

def denominatorScalePositive (d : UniformRatioData) : Prop :=
  0 < d.denominatorScale

def numeratorScaleControlled (d : UniformRatioData) : Prop :=
  d.numeratorScale ≤ d.denominatorScale + d.uniformSlack

def uniformRatioReady (d : UniformRatioData) : Prop :=
  denominatorScalePositive d ∧ numeratorScaleControlled d

def uniformRatioBudget (d : UniformRatioData) : ℕ :=
  d.numeratorScale + d.denominatorScale + d.uniformSlack

theorem uniformRatioReady.denominator {d : UniformRatioData}
    (h : uniformRatioReady d) :
    denominatorScalePositive d ∧ numeratorScaleControlled d ∧
      d.numeratorScale ≤ uniformRatioBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold uniformRatioBudget
  omega

theorem numeratorScale_le_uniformRatioBudget (d : UniformRatioData) :
    d.numeratorScale ≤ uniformRatioBudget d := by
  unfold uniformRatioBudget
  omega

def sampleUniformRatioData : UniformRatioData :=
  { numeratorScale := 7, denominatorScale := 5, uniformSlack := 3 }

example : uniformRatioReady sampleUniformRatioData := by
  norm_num [uniformRatioReady, denominatorScalePositive]
  norm_num [numeratorScaleControlled, sampleUniformRatioData]

example : uniformRatioBudget sampleUniformRatioData = 15 := by
  native_decide

/-- Finite executable readiness audit for uniform ratio data. -/
def uniformRatioDataListReady (data : List UniformRatioData) : Bool :=
  data.all fun d =>
    0 < d.denominatorScale && d.numeratorScale ≤ d.denominatorScale + d.uniformSlack

theorem uniformRatioDataList_readyWindow :
    uniformRatioDataListReady
      [{ numeratorScale := 4, denominatorScale := 5, uniformSlack := 1 },
       { numeratorScale := 7, denominatorScale := 5, uniformSlack := 3 }] = true := by
  unfold uniformRatioDataListReady
  native_decide

/-- A certificate window for uniform ratio asymptotics. -/
structure UniformRatioCertificateWindow where
  numeratorWindow : ℕ
  denominatorWindow : ℕ
  uniformSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The numerator window is controlled by the denominator window. -/
def uniformRatioCertificateControlled
    (w : UniformRatioCertificateWindow) : Prop :=
  w.numeratorWindow ≤ w.denominatorWindow + w.uniformSlack + w.slack

/-- Readiness for a uniform ratio certificate. -/
def uniformRatioCertificateReady
    (w : UniformRatioCertificateWindow) : Prop :=
  0 < w.denominatorWindow ∧
    uniformRatioCertificateControlled w ∧
      w.certificateBudget ≤ w.numeratorWindow + w.denominatorWindow + w.slack

/-- Total size of a uniform ratio certificate. -/
def uniformRatioCertificate (w : UniformRatioCertificateWindow) : ℕ :=
  w.numeratorWindow + w.denominatorWindow + w.uniformSlack + w.certificateBudget + w.slack

theorem uniformRatioCertificate_budget_le_certificate
    (w : UniformRatioCertificateWindow)
    (h : uniformRatioCertificateReady w) :
    w.certificateBudget ≤ uniformRatioCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold uniformRatioCertificate
  omega

def sampleUniformRatioCertificateWindow :
    UniformRatioCertificateWindow where
  numeratorWindow := 7
  denominatorWindow := 6
  uniformSlack := 2
  certificateBudget := 12
  slack := 1

example :
    uniformRatioCertificateReady sampleUniformRatioCertificateWindow := by
  norm_num [uniformRatioCertificateReady,
    uniformRatioCertificateControlled, sampleUniformRatioCertificateWindow]

example :
    sampleUniformRatioCertificateWindow.certificateBudget ≤
      uniformRatioCertificate sampleUniformRatioCertificateWindow := by
  apply uniformRatioCertificate_budget_le_certificate
  norm_num [uniformRatioCertificateReady,
    uniformRatioCertificateControlled, sampleUniformRatioCertificateWindow]

structure UniformRatioRefinementCertificate where
  numeratorWindow : ℕ
  denominatorWindow : ℕ
  uniformSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformRatioRefinementCertificate.numeratorControlled
    (c : UniformRatioRefinementCertificate) : Prop :=
  c.numeratorWindow ≤ c.denominatorWindow + c.uniformSlackWindow + c.slack

def UniformRatioRefinementCertificate.certificateBudgetControlled
    (c : UniformRatioRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.numeratorWindow + c.denominatorWindow + c.uniformSlackWindow + c.slack

def uniformRatioRefinementReady
    (c : UniformRatioRefinementCertificate) : Prop :=
  0 < c.denominatorWindow ∧ c.numeratorControlled ∧ c.certificateBudgetControlled

def UniformRatioRefinementCertificate.size
    (c : UniformRatioRefinementCertificate) : ℕ :=
  c.numeratorWindow + c.denominatorWindow + c.uniformSlackWindow + c.slack

theorem uniformRatio_certificateBudgetWindow_le_size
    {c : UniformRatioRefinementCertificate}
    (h : uniformRatioRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleUniformRatioRefinementCertificate :
    UniformRatioRefinementCertificate :=
  { numeratorWindow := 7, denominatorWindow := 6, uniformSlackWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : uniformRatioRefinementReady
    sampleUniformRatioRefinementCertificate := by
  norm_num [uniformRatioRefinementReady,
    UniformRatioRefinementCertificate.numeratorControlled,
    UniformRatioRefinementCertificate.certificateBudgetControlled,
    sampleUniformRatioRefinementCertificate]

example :
    sampleUniformRatioRefinementCertificate.certificateBudgetWindow ≤
      sampleUniformRatioRefinementCertificate.size := by
  norm_num [UniformRatioRefinementCertificate.size,
    sampleUniformRatioRefinementCertificate]

/-- A second-stage uniform-ratio certificate with a named external budget. -/
structure UniformRatioBudgetCertificate where
  numeratorWindow : ℕ
  denominatorWindow : ℕ
  uniformSlackWindow : ℕ
  ratioBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformRatioBudgetCertificate.ratioControlled
    (cert : UniformRatioBudgetCertificate) : Prop :=
  0 < cert.denominatorWindow ∧
    cert.numeratorWindow ≤ cert.denominatorWindow + cert.uniformSlackWindow + cert.slack ∧
      cert.ratioBudgetWindow ≤
        cert.numeratorWindow + cert.denominatorWindow + cert.uniformSlackWindow + cert.slack

def UniformRatioBudgetCertificate.budgetControlled
    (cert : UniformRatioBudgetCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.numeratorWindow + cert.denominatorWindow + cert.uniformSlackWindow +
      cert.ratioBudgetWindow + cert.slack

def uniformRatioBudgetReady (cert : UniformRatioBudgetCertificate) : Prop :=
  cert.ratioControlled ∧ cert.budgetControlled

def UniformRatioBudgetCertificate.size
    (cert : UniformRatioBudgetCertificate) : ℕ :=
  cert.numeratorWindow + cert.denominatorWindow + cert.uniformSlackWindow +
    cert.ratioBudgetWindow + cert.slack

theorem uniformRatio_budgetCertificate_le_size
    (cert : UniformRatioBudgetCertificate)
    (h : uniformRatioBudgetReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformRatioBudgetCertificate :
    UniformRatioBudgetCertificate :=
  { numeratorWindow := 7, denominatorWindow := 6, uniformSlackWindow := 2,
    ratioBudgetWindow := 16, certificateBudgetWindow := 32, slack := 1 }

example : uniformRatioBudgetReady sampleUniformRatioBudgetCertificate := by
  norm_num [uniformRatioBudgetReady,
    UniformRatioBudgetCertificate.ratioControlled,
    UniformRatioBudgetCertificate.budgetControlled,
    sampleUniformRatioBudgetCertificate]

example :
    sampleUniformRatioBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformRatioBudgetCertificate.size := by
  apply uniformRatio_budgetCertificate_le_size
  norm_num [uniformRatioBudgetReady,
    UniformRatioBudgetCertificate.ratioControlled,
    UniformRatioBudgetCertificate.budgetControlled,
    sampleUniformRatioBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    uniformRatioBudgetReady sampleUniformRatioBudgetCertificate := by
  constructor
  · norm_num [UniformRatioBudgetCertificate.ratioControlled,
      sampleUniformRatioBudgetCertificate]
  · norm_num [UniformRatioBudgetCertificate.budgetControlled,
      sampleUniformRatioBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformRatioBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformRatioBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List UniformRatioBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformRatioBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformRatioBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformRatioAsymptotics
