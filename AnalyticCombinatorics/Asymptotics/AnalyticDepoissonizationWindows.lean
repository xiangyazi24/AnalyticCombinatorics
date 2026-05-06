import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic depoissonization windows.

The finite record stores analytic radius, Poisson window, and tail slack.
-/

namespace AnalyticCombinatorics.Asymptotics.AnalyticDepoissonizationWindows

structure AnalyticDepoissonizationWindowData where
  analyticRadius : ℕ
  poissonWindow : ℕ
  tailSlack : ℕ
deriving DecidableEq, Repr

def analyticRadiusPositive (d : AnalyticDepoissonizationWindowData) : Prop :=
  0 < d.analyticRadius

def poissonWindowControlled (d : AnalyticDepoissonizationWindowData) : Prop :=
  d.poissonWindow ≤ d.analyticRadius + d.tailSlack

def analyticDepoissonizationWindowReady
    (d : AnalyticDepoissonizationWindowData) : Prop :=
  analyticRadiusPositive d ∧ poissonWindowControlled d

def analyticDepoissonizationWindowBudget
    (d : AnalyticDepoissonizationWindowData) : ℕ :=
  d.analyticRadius + d.poissonWindow + d.tailSlack

theorem analyticDepoissonizationWindowReady.radius
    {d : AnalyticDepoissonizationWindowData}
    (h : analyticDepoissonizationWindowReady d) :
    analyticRadiusPositive d ∧ poissonWindowControlled d ∧
      d.poissonWindow ≤ analyticDepoissonizationWindowBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold analyticDepoissonizationWindowBudget
  omega

theorem poissonWindow_le_analyticDepoissonizationBudget
    (d : AnalyticDepoissonizationWindowData) :
    d.poissonWindow ≤ analyticDepoissonizationWindowBudget d := by
  unfold analyticDepoissonizationWindowBudget
  omega

def sampleAnalyticDepoissonizationWindowData :
    AnalyticDepoissonizationWindowData :=
  { analyticRadius := 6, poissonWindow := 8, tailSlack := 3 }

example :
    analyticDepoissonizationWindowReady
      sampleAnalyticDepoissonizationWindowData := by
  norm_num [analyticDepoissonizationWindowReady, analyticRadiusPositive]
  norm_num [poissonWindowControlled, sampleAnalyticDepoissonizationWindowData]

example :
    analyticDepoissonizationWindowBudget
      sampleAnalyticDepoissonizationWindowData = 17 := by
  native_decide

/-- Finite executable readiness audit for analytic depoissonization windows. -/
def analyticDepoissonizationListReady
    (windows : List AnalyticDepoissonizationWindowData) : Bool :=
  windows.all fun d =>
    0 < d.analyticRadius && d.poissonWindow ≤ d.analyticRadius + d.tailSlack

theorem analyticDepoissonizationList_readyWindow :
    analyticDepoissonizationListReady
      [{ analyticRadius := 4, poissonWindow := 5, tailSlack := 1 },
       { analyticRadius := 6, poissonWindow := 8, tailSlack := 3 }] = true := by
  unfold analyticDepoissonizationListReady
  native_decide

/-- A certificate window for analytic depoissonization. -/
structure AnalyticDepoissonizationCertificateWindow where
  radiusWindow : ℕ
  poissonWindow : ℕ
  tailSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The Poisson window is controlled by the analytic radius. -/
def analyticDepoissonizationCertificateControlled
    (w : AnalyticDepoissonizationCertificateWindow) : Prop :=
  w.poissonWindow ≤ w.radiusWindow + w.tailSlack + w.slack

/-- Readiness for an analytic depoissonization certificate. -/
def analyticDepoissonizationCertificateReady
    (w : AnalyticDepoissonizationCertificateWindow) : Prop :=
  0 < w.radiusWindow ∧
    analyticDepoissonizationCertificateControlled w ∧
      w.certificateBudget ≤ w.radiusWindow + w.poissonWindow + w.slack

/-- Total size of an analytic depoissonization certificate. -/
def analyticDepoissonizationCertificate
    (w : AnalyticDepoissonizationCertificateWindow) : ℕ :=
  w.radiusWindow + w.poissonWindow + w.tailSlack + w.certificateBudget + w.slack

theorem analyticDepoissonizationCertificate_budget_le_certificate
    (w : AnalyticDepoissonizationCertificateWindow)
    (h : analyticDepoissonizationCertificateReady w) :
    w.certificateBudget ≤ analyticDepoissonizationCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold analyticDepoissonizationCertificate
  omega

def sampleAnalyticDepoissonizationCertificateWindow :
    AnalyticDepoissonizationCertificateWindow where
  radiusWindow := 6
  poissonWindow := 7
  tailSlack := 2
  certificateBudget := 12
  slack := 1

example :
    analyticDepoissonizationCertificateReady
      sampleAnalyticDepoissonizationCertificateWindow := by
  norm_num [analyticDepoissonizationCertificateReady,
    analyticDepoissonizationCertificateControlled,
    sampleAnalyticDepoissonizationCertificateWindow]

example :
    sampleAnalyticDepoissonizationCertificateWindow.certificateBudget ≤
      analyticDepoissonizationCertificate
        sampleAnalyticDepoissonizationCertificateWindow := by
  apply analyticDepoissonizationCertificate_budget_le_certificate
  norm_num [analyticDepoissonizationCertificateReady,
    analyticDepoissonizationCertificateControlled,
    sampleAnalyticDepoissonizationCertificateWindow]

structure AnalyticDepoissonizationRefinementCertificate where
  radiusWindow : ℕ
  poissonWindow : ℕ
  tailSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticDepoissonizationRefinementCertificate.poissonControlled
    (c : AnalyticDepoissonizationRefinementCertificate) : Prop :=
  c.poissonWindow ≤ c.radiusWindow + c.tailSlackWindow + c.slack

def AnalyticDepoissonizationRefinementCertificate.certificateBudgetControlled
    (c : AnalyticDepoissonizationRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.radiusWindow + c.poissonWindow + c.tailSlackWindow + c.slack

def analyticDepoissonizationRefinementReady
    (c : AnalyticDepoissonizationRefinementCertificate) : Prop :=
  0 < c.radiusWindow ∧ c.poissonControlled ∧ c.certificateBudgetControlled

def AnalyticDepoissonizationRefinementCertificate.size
    (c : AnalyticDepoissonizationRefinementCertificate) : ℕ :=
  c.radiusWindow + c.poissonWindow + c.tailSlackWindow + c.slack

theorem analyticDepoissonization_certificateBudgetWindow_le_size
    {c : AnalyticDepoissonizationRefinementCertificate}
    (h : analyticDepoissonizationRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleAnalyticDepoissonizationRefinementCertificate :
    AnalyticDepoissonizationRefinementCertificate :=
  { radiusWindow := 6, poissonWindow := 7, tailSlackWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : analyticDepoissonizationRefinementReady
    sampleAnalyticDepoissonizationRefinementCertificate := by
  norm_num [analyticDepoissonizationRefinementReady,
    AnalyticDepoissonizationRefinementCertificate.poissonControlled,
    AnalyticDepoissonizationRefinementCertificate.certificateBudgetControlled,
    sampleAnalyticDepoissonizationRefinementCertificate]

example :
    sampleAnalyticDepoissonizationRefinementCertificate.certificateBudgetWindow ≤
      sampleAnalyticDepoissonizationRefinementCertificate.size := by
  norm_num [AnalyticDepoissonizationRefinementCertificate.size,
    sampleAnalyticDepoissonizationRefinementCertificate]

structure AnalyticDepoissonizationBudgetCertificate where
  radiusWindow : ℕ
  poissonWindow : ℕ
  tailSlackWindow : ℕ
  tailBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticDepoissonizationBudgetCertificate.controlled
    (c : AnalyticDepoissonizationBudgetCertificate) : Prop :=
  0 < c.radiusWindow ∧
    c.poissonWindow ≤ c.radiusWindow + c.tailSlackWindow + c.slack ∧
      c.tailBudgetWindow ≤
        c.radiusWindow + c.poissonWindow + c.tailSlackWindow + c.slack

def AnalyticDepoissonizationBudgetCertificate.budgetControlled
    (c : AnalyticDepoissonizationBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.radiusWindow + c.poissonWindow + c.tailSlackWindow +
      c.tailBudgetWindow + c.slack

def AnalyticDepoissonizationBudgetCertificate.Ready
    (c : AnalyticDepoissonizationBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticDepoissonizationBudgetCertificate.size
    (c : AnalyticDepoissonizationBudgetCertificate) : ℕ :=
  c.radiusWindow + c.poissonWindow + c.tailSlackWindow +
    c.tailBudgetWindow + c.slack

theorem analyticDepoissonization_budgetCertificate_le_size
    (c : AnalyticDepoissonizationBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticDepoissonizationBudgetCertificate :
    AnalyticDepoissonizationBudgetCertificate :=
  { radiusWindow := 6
    poissonWindow := 7
    tailSlackWindow := 2
    tailBudgetWindow := 16
    certificateBudgetWindow := 32
    slack := 1 }

example : sampleAnalyticDepoissonizationBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticDepoissonizationBudgetCertificate.controlled,
      sampleAnalyticDepoissonizationBudgetCertificate]
  · norm_num [AnalyticDepoissonizationBudgetCertificate.budgetControlled,
      sampleAnalyticDepoissonizationBudgetCertificate]

example :
    sampleAnalyticDepoissonizationBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticDepoissonizationBudgetCertificate.size := by
  apply analyticDepoissonization_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticDepoissonizationBudgetCertificate.controlled,
      sampleAnalyticDepoissonizationBudgetCertificate]
  · norm_num [AnalyticDepoissonizationBudgetCertificate.budgetControlled,
      sampleAnalyticDepoissonizationBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAnalyticDepoissonizationBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticDepoissonizationBudgetCertificate.controlled,
      sampleAnalyticDepoissonizationBudgetCertificate]
  · norm_num [AnalyticDepoissonizationBudgetCertificate.budgetControlled,
      sampleAnalyticDepoissonizationBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticDepoissonizationBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticDepoissonizationBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List AnalyticDepoissonizationBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticDepoissonizationBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleAnalyticDepoissonizationBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.AnalyticDepoissonizationWindows
