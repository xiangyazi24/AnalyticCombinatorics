import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform singularity margins.

The finite schema records dominant radius, margin width, and perturbation
slack.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformSingularityMargins

structure UniformSingularityMarginData where
  dominantRadius : ℕ
  marginWidth : ℕ
  perturbationSlack : ℕ
deriving DecidableEq, Repr

def dominantRadiusPositive (d : UniformSingularityMarginData) : Prop :=
  0 < d.dominantRadius

def marginControlled (d : UniformSingularityMarginData) : Prop :=
  d.marginWidth ≤ d.dominantRadius + d.perturbationSlack

def uniformSingularityMarginReady
    (d : UniformSingularityMarginData) : Prop :=
  dominantRadiusPositive d ∧ marginControlled d

def uniformSingularityMarginBudget
    (d : UniformSingularityMarginData) : ℕ :=
  d.dominantRadius + d.marginWidth + d.perturbationSlack

theorem uniformSingularityMarginReady.radius
    {d : UniformSingularityMarginData}
    (h : uniformSingularityMarginReady d) :
    dominantRadiusPositive d ∧ marginControlled d ∧
      d.marginWidth ≤ uniformSingularityMarginBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold uniformSingularityMarginBudget
  omega

theorem marginWidth_le_singularityMarginBudget
    (d : UniformSingularityMarginData) :
    d.marginWidth ≤ uniformSingularityMarginBudget d := by
  unfold uniformSingularityMarginBudget
  omega

def sampleUniformSingularityMarginData :
    UniformSingularityMarginData :=
  { dominantRadius := 7, marginWidth := 9, perturbationSlack := 3 }

example :
    uniformSingularityMarginReady sampleUniformSingularityMarginData := by
  norm_num [uniformSingularityMarginReady, dominantRadiusPositive]
  norm_num [marginControlled, sampleUniformSingularityMarginData]

example :
    uniformSingularityMarginBudget sampleUniformSingularityMarginData = 19 := by
  native_decide

/-- Finite executable readiness audit for uniform singularity margins. -/
def uniformSingularityMarginDataListReady
    (data : List UniformSingularityMarginData) : Bool :=
  data.all fun d =>
    0 < d.dominantRadius && d.marginWidth ≤ d.dominantRadius + d.perturbationSlack

theorem uniformSingularityMarginDataList_readyWindow :
    uniformSingularityMarginDataListReady
      [{ dominantRadius := 4, marginWidth := 5, perturbationSlack := 1 },
       { dominantRadius := 7, marginWidth := 9, perturbationSlack := 3 }] = true := by
  unfold uniformSingularityMarginDataListReady
  native_decide

/-- A certificate window for uniform singularity margins. -/
structure UniformSingularityMarginCertificateWindow where
  radiusWindow : ℕ
  marginWindow : ℕ
  perturbationSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The margin window is controlled by dominant radius and slack. -/
def uniformSingularityMarginCertificateControlled
    (w : UniformSingularityMarginCertificateWindow) : Prop :=
  w.marginWindow ≤ w.radiusWindow + w.perturbationSlack + w.slack

/-- Readiness for a singularity margin certificate. -/
def uniformSingularityMarginCertificateReady
    (w : UniformSingularityMarginCertificateWindow) : Prop :=
  0 < w.radiusWindow ∧
    uniformSingularityMarginCertificateControlled w ∧
      w.certificateBudget ≤ w.radiusWindow + w.marginWindow + w.slack

/-- Total size of a singularity margin certificate. -/
def uniformSingularityMarginCertificate
    (w : UniformSingularityMarginCertificateWindow) : ℕ :=
  w.radiusWindow + w.marginWindow + w.perturbationSlack +
    w.certificateBudget + w.slack

theorem uniformSingularityMarginCertificate_budget_le_certificate
    (w : UniformSingularityMarginCertificateWindow)
    (h : uniformSingularityMarginCertificateReady w) :
    w.certificateBudget ≤ uniformSingularityMarginCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold uniformSingularityMarginCertificate
  omega

def sampleUniformSingularityMarginCertificateWindow :
    UniformSingularityMarginCertificateWindow where
  radiusWindow := 7
  marginWindow := 8
  perturbationSlack := 2
  certificateBudget := 14
  slack := 1

example :
    uniformSingularityMarginCertificateReady
      sampleUniformSingularityMarginCertificateWindow := by
  norm_num [uniformSingularityMarginCertificateReady,
    uniformSingularityMarginCertificateControlled,
    sampleUniformSingularityMarginCertificateWindow]

example :
    sampleUniformSingularityMarginCertificateWindow.certificateBudget ≤
      uniformSingularityMarginCertificate
        sampleUniformSingularityMarginCertificateWindow := by
  apply uniformSingularityMarginCertificate_budget_le_certificate
  norm_num [uniformSingularityMarginCertificateReady,
    uniformSingularityMarginCertificateControlled,
    sampleUniformSingularityMarginCertificateWindow]

structure UniformSingularityMarginRefinementCertificate where
  radiusWindow : ℕ
  marginWindow : ℕ
  perturbationSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformSingularityMarginRefinementCertificate.marginControlled
    (c : UniformSingularityMarginRefinementCertificate) : Prop :=
  c.marginWindow ≤ c.radiusWindow + c.perturbationSlackWindow + c.slack

def UniformSingularityMarginRefinementCertificate.certificateBudgetControlled
    (c : UniformSingularityMarginRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.radiusWindow + c.marginWindow + c.perturbationSlackWindow + c.slack

def uniformSingularityMarginRefinementReady
    (c : UniformSingularityMarginRefinementCertificate) : Prop :=
  0 < c.radiusWindow ∧ c.marginControlled ∧ c.certificateBudgetControlled

def UniformSingularityMarginRefinementCertificate.size
    (c : UniformSingularityMarginRefinementCertificate) : ℕ :=
  c.radiusWindow + c.marginWindow + c.perturbationSlackWindow + c.slack

theorem uniformSingularityMargin_certificateBudgetWindow_le_size
    {c : UniformSingularityMarginRefinementCertificate}
    (h : uniformSingularityMarginRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleUniformSingularityMarginRefinementCertificate :
    UniformSingularityMarginRefinementCertificate :=
  { radiusWindow := 7, marginWindow := 8, perturbationSlackWindow := 2,
    certificateBudgetWindow := 18, slack := 1 }

example : uniformSingularityMarginRefinementReady
    sampleUniformSingularityMarginRefinementCertificate := by
  norm_num [uniformSingularityMarginRefinementReady,
    UniformSingularityMarginRefinementCertificate.marginControlled,
    UniformSingularityMarginRefinementCertificate.certificateBudgetControlled,
    sampleUniformSingularityMarginRefinementCertificate]

example :
    sampleUniformSingularityMarginRefinementCertificate.certificateBudgetWindow ≤
      sampleUniformSingularityMarginRefinementCertificate.size := by
  norm_num [UniformSingularityMarginRefinementCertificate.size,
    sampleUniformSingularityMarginRefinementCertificate]

structure UniformSingularityMarginBudgetCertificate where
  radiusWindow : ℕ
  marginWindow : ℕ
  perturbationSlackWindow : ℕ
  marginBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformSingularityMarginBudgetCertificate.controlled
    (c : UniformSingularityMarginBudgetCertificate) : Prop :=
  0 < c.radiusWindow ∧
    c.marginWindow ≤ c.radiusWindow + c.perturbationSlackWindow + c.slack ∧
      c.marginBudgetWindow ≤
        c.radiusWindow + c.marginWindow + c.perturbationSlackWindow + c.slack

def UniformSingularityMarginBudgetCertificate.budgetControlled
    (c : UniformSingularityMarginBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.radiusWindow + c.marginWindow + c.perturbationSlackWindow +
      c.marginBudgetWindow + c.slack

def UniformSingularityMarginBudgetCertificate.Ready
    (c : UniformSingularityMarginBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformSingularityMarginBudgetCertificate.size
    (c : UniformSingularityMarginBudgetCertificate) : ℕ :=
  c.radiusWindow + c.marginWindow + c.perturbationSlackWindow +
    c.marginBudgetWindow + c.slack

theorem uniformSingularityMargin_budgetCertificate_le_size
    (c : UniformSingularityMarginBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformSingularityMarginBudgetCertificate :
    UniformSingularityMarginBudgetCertificate :=
  { radiusWindow := 7
    marginWindow := 8
    perturbationSlackWindow := 2
    marginBudgetWindow := 18
    certificateBudgetWindow := 36
    slack := 1 }

example : sampleUniformSingularityMarginBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformSingularityMarginBudgetCertificate.controlled,
      sampleUniformSingularityMarginBudgetCertificate]
  · norm_num [UniformSingularityMarginBudgetCertificate.budgetControlled,
      sampleUniformSingularityMarginBudgetCertificate]

example :
    sampleUniformSingularityMarginBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformSingularityMarginBudgetCertificate.size := by
  apply uniformSingularityMargin_budgetCertificate_le_size
  constructor
  · norm_num [UniformSingularityMarginBudgetCertificate.controlled,
      sampleUniformSingularityMarginBudgetCertificate]
  · norm_num [UniformSingularityMarginBudgetCertificate.budgetControlled,
      sampleUniformSingularityMarginBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleUniformSingularityMarginBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformSingularityMarginBudgetCertificate.controlled,
      sampleUniformSingularityMarginBudgetCertificate]
  · norm_num [UniformSingularityMarginBudgetCertificate.budgetControlled,
      sampleUniformSingularityMarginBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformSingularityMarginBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformSingularityMarginBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List UniformSingularityMarginBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformSingularityMarginBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformSingularityMarginBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformSingularityMargins
