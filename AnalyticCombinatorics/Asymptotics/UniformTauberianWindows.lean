import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform Tauberian windows.

The finite schema records summatory window, monotone scale, and boundary
slack.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformTauberianWindows

structure UniformTauberianWindowData where
  summatoryWindow : ℕ
  monotoneScale : ℕ
  boundarySlack : ℕ
deriving DecidableEq, Repr

def monotoneScalePositive (d : UniformTauberianWindowData) : Prop :=
  0 < d.monotoneScale

def summatoryWindowControlled (d : UniformTauberianWindowData) : Prop :=
  d.summatoryWindow ≤ d.monotoneScale + d.boundarySlack

def uniformTauberianWindowReady
    (d : UniformTauberianWindowData) : Prop :=
  monotoneScalePositive d ∧ summatoryWindowControlled d

def uniformTauberianWindowBudget
    (d : UniformTauberianWindowData) : ℕ :=
  d.summatoryWindow + d.monotoneScale + d.boundarySlack

theorem uniformTauberianWindowReady.monotone
    {d : UniformTauberianWindowData}
    (h : uniformTauberianWindowReady d) :
    monotoneScalePositive d ∧ summatoryWindowControlled d ∧
      d.summatoryWindow ≤ uniformTauberianWindowBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold uniformTauberianWindowBudget
  omega

theorem summatoryWindow_le_tauberianWindowBudget
    (d : UniformTauberianWindowData) :
    d.summatoryWindow ≤ uniformTauberianWindowBudget d := by
  unfold uniformTauberianWindowBudget
  omega

def sampleUniformTauberianWindowData :
    UniformTauberianWindowData :=
  { summatoryWindow := 7, monotoneScale := 5, boundarySlack := 3 }

example :
    uniformTauberianWindowReady sampleUniformTauberianWindowData := by
  norm_num [uniformTauberianWindowReady, monotoneScalePositive]
  norm_num [summatoryWindowControlled, sampleUniformTauberianWindowData]

example :
    uniformTauberianWindowBudget sampleUniformTauberianWindowData = 15 := by
  native_decide

/-- Finite executable readiness audit for uniform Tauberian windows. -/
def uniformTauberianWindowDataListReady
    (data : List UniformTauberianWindowData) : Bool :=
  data.all fun d =>
    0 < d.monotoneScale && d.summatoryWindow ≤ d.monotoneScale + d.boundarySlack

theorem uniformTauberianWindowDataList_readyWindow :
    uniformTauberianWindowDataListReady
      [{ summatoryWindow := 4, monotoneScale := 5, boundarySlack := 1 },
       { summatoryWindow := 7, monotoneScale := 5, boundarySlack := 3 }] = true := by
  unfold uniformTauberianWindowDataListReady
  native_decide

/-- A certificate window for uniform Tauberian estimates. -/
structure UniformTauberianCertificateWindow where
  summatoryWindow : ℕ
  monotoneWindow : ℕ
  boundarySlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The summatory window is controlled by monotone scale and slack. -/
def uniformTauberianCertificateControlled
    (w : UniformTauberianCertificateWindow) : Prop :=
  w.summatoryWindow ≤ w.monotoneWindow + w.boundarySlack + w.slack

/-- Readiness for a Tauberian certificate. -/
def uniformTauberianCertificateReady
    (w : UniformTauberianCertificateWindow) : Prop :=
  0 < w.monotoneWindow ∧
    uniformTauberianCertificateControlled w ∧
      w.certificateBudget ≤ w.summatoryWindow + w.monotoneWindow + w.slack

/-- Total size of a Tauberian certificate. -/
def uniformTauberianCertificate
    (w : UniformTauberianCertificateWindow) : ℕ :=
  w.summatoryWindow + w.monotoneWindow + w.boundarySlack + w.certificateBudget + w.slack

theorem uniformTauberianCertificate_budget_le_certificate
    (w : UniformTauberianCertificateWindow)
    (h : uniformTauberianCertificateReady w) :
    w.certificateBudget ≤ uniformTauberianCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold uniformTauberianCertificate
  omega

def sampleUniformTauberianCertificateWindow :
    UniformTauberianCertificateWindow where
  summatoryWindow := 6
  monotoneWindow := 7
  boundarySlack := 2
  certificateBudget := 12
  slack := 1

example :
    uniformTauberianCertificateReady
      sampleUniformTauberianCertificateWindow := by
  norm_num [uniformTauberianCertificateReady,
    uniformTauberianCertificateControlled, sampleUniformTauberianCertificateWindow]

example :
    sampleUniformTauberianCertificateWindow.certificateBudget ≤
      uniformTauberianCertificate sampleUniformTauberianCertificateWindow := by
  apply uniformTauberianCertificate_budget_le_certificate
  norm_num [uniformTauberianCertificateReady,
    uniformTauberianCertificateControlled, sampleUniformTauberianCertificateWindow]

structure UniformTauberianRefinementCertificate where
  summatoryWindow : ℕ
  monotoneWindow : ℕ
  boundarySlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformTauberianRefinementCertificate.summatoryControlled
    (c : UniformTauberianRefinementCertificate) : Prop :=
  c.summatoryWindow ≤ c.monotoneWindow + c.boundarySlackWindow + c.slack

def UniformTauberianRefinementCertificate.certificateBudgetControlled
    (c : UniformTauberianRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.summatoryWindow + c.monotoneWindow + c.boundarySlackWindow + c.slack

def uniformTauberianRefinementReady
    (c : UniformTauberianRefinementCertificate) : Prop :=
  0 < c.monotoneWindow ∧ c.summatoryControlled ∧ c.certificateBudgetControlled

def UniformTauberianRefinementCertificate.size
    (c : UniformTauberianRefinementCertificate) : ℕ :=
  c.summatoryWindow + c.monotoneWindow + c.boundarySlackWindow + c.slack

theorem uniformTauberian_certificateBudgetWindow_le_size
    {c : UniformTauberianRefinementCertificate}
    (h : uniformTauberianRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleUniformTauberianRefinementCertificate :
    UniformTauberianRefinementCertificate :=
  { summatoryWindow := 6, monotoneWindow := 7, boundarySlackWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : uniformTauberianRefinementReady
    sampleUniformTauberianRefinementCertificate := by
  norm_num [uniformTauberianRefinementReady,
    UniformTauberianRefinementCertificate.summatoryControlled,
    UniformTauberianRefinementCertificate.certificateBudgetControlled,
    sampleUniformTauberianRefinementCertificate]

example :
    sampleUniformTauberianRefinementCertificate.certificateBudgetWindow ≤
      sampleUniformTauberianRefinementCertificate.size := by
  norm_num [UniformTauberianRefinementCertificate.size,
    sampleUniformTauberianRefinementCertificate]

structure UniformTauberianBudgetCertificate where
  summatoryWindow : ℕ
  monotoneWindow : ℕ
  boundarySlackWindow : ℕ
  tauberianBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformTauberianBudgetCertificate.controlled
    (c : UniformTauberianBudgetCertificate) : Prop :=
  0 < c.monotoneWindow ∧
    c.summatoryWindow ≤ c.monotoneWindow + c.boundarySlackWindow + c.slack ∧
      c.tauberianBudgetWindow ≤
        c.summatoryWindow + c.monotoneWindow + c.boundarySlackWindow + c.slack

def UniformTauberianBudgetCertificate.budgetControlled
    (c : UniformTauberianBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.summatoryWindow + c.monotoneWindow + c.boundarySlackWindow +
      c.tauberianBudgetWindow + c.slack

def UniformTauberianBudgetCertificate.Ready
    (c : UniformTauberianBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformTauberianBudgetCertificate.size
    (c : UniformTauberianBudgetCertificate) : ℕ :=
  c.summatoryWindow + c.monotoneWindow + c.boundarySlackWindow +
    c.tauberianBudgetWindow + c.slack

theorem uniformTauberian_budgetCertificate_le_size
    (c : UniformTauberianBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformTauberianBudgetCertificate :
    UniformTauberianBudgetCertificate :=
  { summatoryWindow := 6
    monotoneWindow := 7
    boundarySlackWindow := 2
    tauberianBudgetWindow := 16
    certificateBudgetWindow := 32
    slack := 1 }

example : sampleUniformTauberianBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformTauberianBudgetCertificate.controlled,
      sampleUniformTauberianBudgetCertificate]
  · norm_num [UniformTauberianBudgetCertificate.budgetControlled,
      sampleUniformTauberianBudgetCertificate]

example :
    sampleUniformTauberianBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformTauberianBudgetCertificate.size := by
  apply uniformTauberian_budgetCertificate_le_size
  constructor
  · norm_num [UniformTauberianBudgetCertificate.controlled,
      sampleUniformTauberianBudgetCertificate]
  · norm_num [UniformTauberianBudgetCertificate.budgetControlled,
      sampleUniformTauberianBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleUniformTauberianBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformTauberianBudgetCertificate.controlled,
      sampleUniformTauberianBudgetCertificate]
  · norm_num [UniformTauberianBudgetCertificate.budgetControlled,
      sampleUniformTauberianBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformTauberianBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformTauberianBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List UniformTauberianBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformTauberianBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformTauberianBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformTauberianWindows
