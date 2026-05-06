import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform cumulant bounds.

The finite record stores cumulant order, bound scale, and uniform slack.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformCumulantBounds

structure UniformCumulantBoundData where
  cumulantOrder : ℕ
  boundScale : ℕ
  uniformSlack : ℕ
deriving DecidableEq, Repr

def boundScalePositive (d : UniformCumulantBoundData) : Prop :=
  0 < d.boundScale

def cumulantOrderControlled (d : UniformCumulantBoundData) : Prop :=
  d.cumulantOrder ≤ d.boundScale + d.uniformSlack

def uniformCumulantBoundReady (d : UniformCumulantBoundData) : Prop :=
  boundScalePositive d ∧ cumulantOrderControlled d

def uniformCumulantBoundBudget (d : UniformCumulantBoundData) : ℕ :=
  d.cumulantOrder + d.boundScale + d.uniformSlack

theorem uniformCumulantBoundReady.bound
    {d : UniformCumulantBoundData}
    (h : uniformCumulantBoundReady d) :
    boundScalePositive d ∧ cumulantOrderControlled d ∧
      d.cumulantOrder ≤ uniformCumulantBoundBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold uniformCumulantBoundBudget
  omega

theorem cumulantOrder_le_cumulantBoundBudget
    (d : UniformCumulantBoundData) :
    d.cumulantOrder ≤ uniformCumulantBoundBudget d := by
  unfold uniformCumulantBoundBudget
  omega

def sampleUniformCumulantBoundData : UniformCumulantBoundData :=
  { cumulantOrder := 6, boundScale := 4, uniformSlack := 3 }

example : uniformCumulantBoundReady sampleUniformCumulantBoundData := by
  norm_num [uniformCumulantBoundReady, boundScalePositive]
  norm_num [cumulantOrderControlled, sampleUniformCumulantBoundData]

example : uniformCumulantBoundBudget sampleUniformCumulantBoundData = 13 := by
  native_decide

/-- Finite executable readiness audit for uniform cumulant bound data. -/
def uniformCumulantDataListReady
    (data : List UniformCumulantBoundData) : Bool :=
  data.all fun d => 0 < d.boundScale && d.cumulantOrder ≤ d.boundScale + d.uniformSlack

theorem uniformCumulantDataList_readyWindow :
    uniformCumulantDataListReady
      [{ cumulantOrder := 3, boundScale := 4, uniformSlack := 1 },
       { cumulantOrder := 6, boundScale := 4, uniformSlack := 3 }] = true := by
  unfold uniformCumulantDataListReady
  native_decide

/-- A certificate window for uniform cumulant bounds. -/
structure UniformCumulantCertificateWindow where
  cumulantWindow : ℕ
  boundWindow : ℕ
  uniformSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The cumulant window is controlled by the bound window. -/
def uniformCumulantCertificateControlled
    (w : UniformCumulantCertificateWindow) : Prop :=
  w.cumulantWindow ≤ w.boundWindow + w.uniformSlack + w.slack

/-- Readiness for a uniform cumulant certificate. -/
def uniformCumulantCertificateReady
    (w : UniformCumulantCertificateWindow) : Prop :=
  0 < w.boundWindow ∧
    uniformCumulantCertificateControlled w ∧
      w.certificateBudget ≤ w.cumulantWindow + w.boundWindow + w.slack

/-- Total size of a uniform cumulant certificate. -/
def uniformCumulantCertificate
    (w : UniformCumulantCertificateWindow) : ℕ :=
  w.cumulantWindow + w.boundWindow + w.uniformSlack + w.certificateBudget + w.slack

theorem uniformCumulantCertificate_budget_le_certificate
    (w : UniformCumulantCertificateWindow)
    (h : uniformCumulantCertificateReady w) :
    w.certificateBudget ≤ uniformCumulantCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold uniformCumulantCertificate
  omega

def sampleUniformCumulantCertificateWindow :
    UniformCumulantCertificateWindow where
  cumulantWindow := 5
  boundWindow := 6
  uniformSlack := 2
  certificateBudget := 10
  slack := 1

example :
    uniformCumulantCertificateReady sampleUniformCumulantCertificateWindow := by
  norm_num [uniformCumulantCertificateReady,
    uniformCumulantCertificateControlled, sampleUniformCumulantCertificateWindow]

example :
    sampleUniformCumulantCertificateWindow.certificateBudget ≤
      uniformCumulantCertificate sampleUniformCumulantCertificateWindow := by
  apply uniformCumulantCertificate_budget_le_certificate
  norm_num [uniformCumulantCertificateReady,
    uniformCumulantCertificateControlled, sampleUniformCumulantCertificateWindow]

structure UniformCumulantRefinementCertificate where
  cumulantWindow : ℕ
  boundWindow : ℕ
  uniformSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformCumulantRefinementCertificate.cumulantControlled
    (c : UniformCumulantRefinementCertificate) : Prop :=
  c.cumulantWindow ≤ c.boundWindow + c.uniformSlackWindow + c.slack

def UniformCumulantRefinementCertificate.certificateBudgetControlled
    (c : UniformCumulantRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.cumulantWindow + c.boundWindow + c.uniformSlackWindow + c.slack

def uniformCumulantRefinementReady
    (c : UniformCumulantRefinementCertificate) : Prop :=
  0 < c.boundWindow ∧ c.cumulantControlled ∧ c.certificateBudgetControlled

def UniformCumulantRefinementCertificate.size
    (c : UniformCumulantRefinementCertificate) : ℕ :=
  c.cumulantWindow + c.boundWindow + c.uniformSlackWindow + c.slack

theorem uniformCumulant_certificateBudgetWindow_le_size
    {c : UniformCumulantRefinementCertificate}
    (h : uniformCumulantRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleUniformCumulantRefinementCertificate :
    UniformCumulantRefinementCertificate :=
  { cumulantWindow := 5, boundWindow := 6, uniformSlackWindow := 2,
    certificateBudgetWindow := 14, slack := 1 }

example : uniformCumulantRefinementReady
    sampleUniformCumulantRefinementCertificate := by
  norm_num [uniformCumulantRefinementReady,
    UniformCumulantRefinementCertificate.cumulantControlled,
    UniformCumulantRefinementCertificate.certificateBudgetControlled,
    sampleUniformCumulantRefinementCertificate]

example :
    sampleUniformCumulantRefinementCertificate.certificateBudgetWindow ≤
      sampleUniformCumulantRefinementCertificate.size := by
  norm_num [UniformCumulantRefinementCertificate.size,
    sampleUniformCumulantRefinementCertificate]

/-- A second-stage uniform-cumulant certificate with a named external budget. -/
structure UniformCumulantBudgetCertificate where
  cumulantWindow : ℕ
  boundWindow : ℕ
  uniformSlackWindow : ℕ
  cumulantBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformCumulantBudgetCertificate.cumulantControlled
    (cert : UniformCumulantBudgetCertificate) : Prop :=
  0 < cert.boundWindow ∧
    cert.cumulantWindow ≤ cert.boundWindow + cert.uniformSlackWindow + cert.slack ∧
      cert.cumulantBudgetWindow ≤
        cert.cumulantWindow + cert.boundWindow + cert.uniformSlackWindow + cert.slack

def UniformCumulantBudgetCertificate.budgetControlled
    (cert : UniformCumulantBudgetCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.cumulantWindow + cert.boundWindow + cert.uniformSlackWindow +
      cert.cumulantBudgetWindow + cert.slack

def uniformCumulantBudgetReady
    (cert : UniformCumulantBudgetCertificate) : Prop :=
  cert.cumulantControlled ∧ cert.budgetControlled

def UniformCumulantBudgetCertificate.size
    (cert : UniformCumulantBudgetCertificate) : ℕ :=
  cert.cumulantWindow + cert.boundWindow + cert.uniformSlackWindow +
    cert.cumulantBudgetWindow + cert.slack

theorem uniformCumulant_budgetCertificate_le_size
    (cert : UniformCumulantBudgetCertificate)
    (h : uniformCumulantBudgetReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformCumulantBudgetCertificate :
    UniformCumulantBudgetCertificate :=
  { cumulantWindow := 5, boundWindow := 6, uniformSlackWindow := 2,
    cumulantBudgetWindow := 14, certificateBudgetWindow := 28, slack := 1 }

example : uniformCumulantBudgetReady sampleUniformCumulantBudgetCertificate := by
  norm_num [uniformCumulantBudgetReady,
    UniformCumulantBudgetCertificate.cumulantControlled,
    UniformCumulantBudgetCertificate.budgetControlled,
    sampleUniformCumulantBudgetCertificate]

example :
    sampleUniformCumulantBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformCumulantBudgetCertificate.size := by
  apply uniformCumulant_budgetCertificate_le_size
  norm_num [uniformCumulantBudgetReady,
    UniformCumulantBudgetCertificate.cumulantControlled,
    UniformCumulantBudgetCertificate.budgetControlled,
    sampleUniformCumulantBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    uniformCumulantBudgetReady sampleUniformCumulantBudgetCertificate := by
  constructor
  · norm_num [UniformCumulantBudgetCertificate.cumulantControlled,
      sampleUniformCumulantBudgetCertificate]
  · norm_num [UniformCumulantBudgetCertificate.budgetControlled,
      sampleUniformCumulantBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformCumulantBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformCumulantBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List UniformCumulantBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformCumulantBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformCumulantBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformCumulantBounds
