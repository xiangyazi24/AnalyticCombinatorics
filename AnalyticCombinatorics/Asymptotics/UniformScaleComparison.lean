import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform scale comparison.

The schema gives a finite certificate for comparing two scales with a slack
term.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformScaleComparison

structure UniformScaleComparisonData where
  baseScale : ℕ
  comparisonScale : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def positiveBaseScale (d : UniformScaleComparisonData) : Prop :=
  0 < d.baseScale

def comparisonControlled (d : UniformScaleComparisonData) : Prop :=
  d.comparisonScale ≤ d.baseScale + d.slack

def uniformScaleComparisonReady (d : UniformScaleComparisonData) : Prop :=
  positiveBaseScale d ∧ comparisonControlled d

def uniformScaleComparisonBudget (d : UniformScaleComparisonData) : ℕ :=
  d.baseScale + d.comparisonScale + d.slack

theorem uniformScaleComparisonReady.base {d : UniformScaleComparisonData}
    (h : uniformScaleComparisonReady d) :
    positiveBaseScale d ∧ comparisonControlled d ∧
      d.comparisonScale ≤ uniformScaleComparisonBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold uniformScaleComparisonBudget
  omega

theorem baseScale_le_comparisonBudget (d : UniformScaleComparisonData) :
    d.baseScale ≤ uniformScaleComparisonBudget d := by
  unfold uniformScaleComparisonBudget
  omega

def sampleUniformScaleComparisonData : UniformScaleComparisonData :=
  { baseScale := 6, comparisonScale := 9, slack := 4 }

example : uniformScaleComparisonReady sampleUniformScaleComparisonData := by
  norm_num [uniformScaleComparisonReady, positiveBaseScale]
  norm_num [comparisonControlled, sampleUniformScaleComparisonData]

example : uniformScaleComparisonBudget sampleUniformScaleComparisonData = 19 := by
  native_decide

/-- Finite executable readiness audit for uniform scale comparisons. -/
def uniformScaleComparisonDataListReady
    (data : List UniformScaleComparisonData) : Bool :=
  data.all fun d => 0 < d.baseScale && d.comparisonScale ≤ d.baseScale + d.slack

theorem uniformScaleComparisonDataList_readyWindow :
    uniformScaleComparisonDataListReady
      [{ baseScale := 4, comparisonScale := 5, slack := 1 },
       { baseScale := 6, comparisonScale := 9, slack := 4 }] = true := by
  unfold uniformScaleComparisonDataListReady
  native_decide

/-- A certificate window for uniform scale comparison. -/
structure UniformScaleComparisonCertificateWindow where
  baseWindow : ℕ
  comparisonWindow : ℕ
  comparisonSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The comparison window is controlled by the base window. -/
def uniformScaleComparisonCertificateControlled
    (w : UniformScaleComparisonCertificateWindow) : Prop :=
  w.comparisonWindow ≤ w.baseWindow + w.comparisonSlack + w.slack

/-- Readiness for a scale comparison certificate. -/
def uniformScaleComparisonCertificateReady
    (w : UniformScaleComparisonCertificateWindow) : Prop :=
  0 < w.baseWindow ∧
    uniformScaleComparisonCertificateControlled w ∧
      w.certificateBudget ≤ w.baseWindow + w.comparisonWindow + w.slack

/-- Total size of a scale comparison certificate. -/
def uniformScaleComparisonCertificate
    (w : UniformScaleComparisonCertificateWindow) : ℕ :=
  w.baseWindow + w.comparisonWindow + w.comparisonSlack +
    w.certificateBudget + w.slack

theorem uniformScaleComparisonCertificate_budget_le_certificate
    (w : UniformScaleComparisonCertificateWindow)
    (h : uniformScaleComparisonCertificateReady w) :
    w.certificateBudget ≤ uniformScaleComparisonCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold uniformScaleComparisonCertificate
  omega

def sampleUniformScaleComparisonCertificateWindow :
    UniformScaleComparisonCertificateWindow where
  baseWindow := 7
  comparisonWindow := 8
  comparisonSlack := 2
  certificateBudget := 14
  slack := 1

example :
    uniformScaleComparisonCertificateReady
      sampleUniformScaleComparisonCertificateWindow := by
  norm_num [uniformScaleComparisonCertificateReady,
    uniformScaleComparisonCertificateControlled,
    sampleUniformScaleComparisonCertificateWindow]

example :
    sampleUniformScaleComparisonCertificateWindow.certificateBudget ≤
      uniformScaleComparisonCertificate
        sampleUniformScaleComparisonCertificateWindow := by
  apply uniformScaleComparisonCertificate_budget_le_certificate
  norm_num [uniformScaleComparisonCertificateReady,
    uniformScaleComparisonCertificateControlled,
    sampleUniformScaleComparisonCertificateWindow]

structure UniformScaleComparisonRefinementCertificate where
  baseWindow : ℕ
  comparisonWindow : ℕ
  comparisonSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformScaleComparisonRefinementCertificate.comparisonControlled
    (c : UniformScaleComparisonRefinementCertificate) : Prop :=
  c.comparisonWindow ≤ c.baseWindow + c.comparisonSlackWindow + c.slack

def UniformScaleComparisonRefinementCertificate.certificateBudgetControlled
    (c : UniformScaleComparisonRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.baseWindow + c.comparisonWindow + c.comparisonSlackWindow + c.slack

def uniformScaleComparisonRefinementReady
    (c : UniformScaleComparisonRefinementCertificate) : Prop :=
  0 < c.baseWindow ∧ c.comparisonControlled ∧ c.certificateBudgetControlled

def UniformScaleComparisonRefinementCertificate.size
    (c : UniformScaleComparisonRefinementCertificate) : ℕ :=
  c.baseWindow + c.comparisonWindow + c.comparisonSlackWindow + c.slack

theorem uniformScaleComparison_certificateBudgetWindow_le_size
    {c : UniformScaleComparisonRefinementCertificate}
    (h : uniformScaleComparisonRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleUniformScaleComparisonRefinementCertificate :
    UniformScaleComparisonRefinementCertificate :=
  { baseWindow := 7, comparisonWindow := 8, comparisonSlackWindow := 2,
    certificateBudgetWindow := 18, slack := 1 }

example : uniformScaleComparisonRefinementReady
    sampleUniformScaleComparisonRefinementCertificate := by
  norm_num [uniformScaleComparisonRefinementReady,
    UniformScaleComparisonRefinementCertificate.comparisonControlled,
    UniformScaleComparisonRefinementCertificate.certificateBudgetControlled,
    sampleUniformScaleComparisonRefinementCertificate]

example :
    sampleUniformScaleComparisonRefinementCertificate.certificateBudgetWindow ≤
      sampleUniformScaleComparisonRefinementCertificate.size := by
  norm_num [UniformScaleComparisonRefinementCertificate.size,
    sampleUniformScaleComparisonRefinementCertificate]

structure UniformScaleComparisonBudgetCertificate where
  baseWindow : ℕ
  comparisonWindow : ℕ
  comparisonSlackWindow : ℕ
  comparisonBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformScaleComparisonBudgetCertificate.controlled
    (c : UniformScaleComparisonBudgetCertificate) : Prop :=
  0 < c.baseWindow ∧
    c.comparisonWindow ≤ c.baseWindow + c.comparisonSlackWindow + c.slack ∧
      c.comparisonBudgetWindow ≤
        c.baseWindow + c.comparisonWindow + c.comparisonSlackWindow + c.slack

def UniformScaleComparisonBudgetCertificate.budgetControlled
    (c : UniformScaleComparisonBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.baseWindow + c.comparisonWindow + c.comparisonSlackWindow +
      c.comparisonBudgetWindow + c.slack

def UniformScaleComparisonBudgetCertificate.Ready
    (c : UniformScaleComparisonBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformScaleComparisonBudgetCertificate.size
    (c : UniformScaleComparisonBudgetCertificate) : ℕ :=
  c.baseWindow + c.comparisonWindow + c.comparisonSlackWindow +
    c.comparisonBudgetWindow + c.slack

theorem uniformScaleComparison_budgetCertificate_le_size
    (c : UniformScaleComparisonBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformScaleComparisonBudgetCertificate :
    UniformScaleComparisonBudgetCertificate :=
  { baseWindow := 7
    comparisonWindow := 8
    comparisonSlackWindow := 2
    comparisonBudgetWindow := 18
    certificateBudgetWindow := 36
    slack := 1 }

example : sampleUniformScaleComparisonBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformScaleComparisonBudgetCertificate.controlled,
      sampleUniformScaleComparisonBudgetCertificate]
  · norm_num [UniformScaleComparisonBudgetCertificate.budgetControlled,
      sampleUniformScaleComparisonBudgetCertificate]

example :
    sampleUniformScaleComparisonBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformScaleComparisonBudgetCertificate.size := by
  apply uniformScaleComparison_budgetCertificate_le_size
  constructor
  · norm_num [UniformScaleComparisonBudgetCertificate.controlled,
      sampleUniformScaleComparisonBudgetCertificate]
  · norm_num [UniformScaleComparisonBudgetCertificate.budgetControlled,
      sampleUniformScaleComparisonBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleUniformScaleComparisonBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformScaleComparisonBudgetCertificate.controlled,
      sampleUniformScaleComparisonBudgetCertificate]
  · norm_num [UniformScaleComparisonBudgetCertificate.budgetControlled,
      sampleUniformScaleComparisonBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformScaleComparisonBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformScaleComparisonBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List UniformScaleComparisonBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformScaleComparisonBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformScaleComparisonBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformScaleComparison
