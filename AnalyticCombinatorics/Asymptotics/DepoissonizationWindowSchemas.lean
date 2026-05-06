import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Depoissonization window schemas.

The finite record stores poisson radius, coefficient window, and tail
slack.
-/

namespace AnalyticCombinatorics.Asymptotics.DepoissonizationWindowSchemas

structure DepoissonizationWindowData where
  poissonRadius : ℕ
  coefficientWindow : ℕ
  tailSlack : ℕ
deriving DecidableEq, Repr

def poissonRadiusPositive (d : DepoissonizationWindowData) : Prop :=
  0 < d.poissonRadius

def coefficientWindowControlled (d : DepoissonizationWindowData) : Prop :=
  d.coefficientWindow ≤ d.poissonRadius + d.tailSlack

def depoissonizationWindowReady (d : DepoissonizationWindowData) : Prop :=
  poissonRadiusPositive d ∧ coefficientWindowControlled d

def depoissonizationWindowBudget (d : DepoissonizationWindowData) : ℕ :=
  d.poissonRadius + d.coefficientWindow + d.tailSlack

theorem depoissonizationWindowReady.radius
    {d : DepoissonizationWindowData}
    (h : depoissonizationWindowReady d) :
    poissonRadiusPositive d ∧ coefficientWindowControlled d ∧
      d.coefficientWindow ≤ depoissonizationWindowBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold depoissonizationWindowBudget
  omega

theorem coefficientWindow_le_depoissonizationBudget
    (d : DepoissonizationWindowData) :
    d.coefficientWindow ≤ depoissonizationWindowBudget d := by
  unfold depoissonizationWindowBudget
  omega

def sampleDepoissonizationWindowData : DepoissonizationWindowData :=
  { poissonRadius := 6, coefficientWindow := 8, tailSlack := 3 }

example : depoissonizationWindowReady sampleDepoissonizationWindowData := by
  norm_num [depoissonizationWindowReady, poissonRadiusPositive]
  norm_num [coefficientWindowControlled, sampleDepoissonizationWindowData]

example : depoissonizationWindowBudget sampleDepoissonizationWindowData = 17 := by
  native_decide

/-- Finite executable readiness audit for depoissonization windows. -/
def depoissonizationWindowListReady
    (windows : List DepoissonizationWindowData) : Bool :=
  windows.all fun d =>
    0 < d.poissonRadius && d.coefficientWindow ≤ d.poissonRadius + d.tailSlack

theorem depoissonizationWindowList_readyWindow :
    depoissonizationWindowListReady
      [{ poissonRadius := 4, coefficientWindow := 5, tailSlack := 1 },
       { poissonRadius := 6, coefficientWindow := 8, tailSlack := 3 }] = true := by
  unfold depoissonizationWindowListReady
  native_decide

/-- A certificate window for depoissonization estimates. -/
structure DepoissonizationCertificateWindow where
  radiusWindow : ℕ
  coefficientWindow : ℕ
  tailSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The coefficient window is controlled by radius and tail slack. -/
def depoissonizationCertificateControlled
    (w : DepoissonizationCertificateWindow) : Prop :=
  w.coefficientWindow ≤ w.radiusWindow + w.tailSlack + w.slack

/-- Readiness for a depoissonization certificate. -/
def depoissonizationCertificateReady
    (w : DepoissonizationCertificateWindow) : Prop :=
  0 < w.radiusWindow ∧
    depoissonizationCertificateControlled w ∧
      w.certificateBudget ≤ w.radiusWindow + w.coefficientWindow + w.slack

/-- Total size of a depoissonization certificate. -/
def depoissonizationCertificate
    (w : DepoissonizationCertificateWindow) : ℕ :=
  w.radiusWindow + w.coefficientWindow + w.tailSlack + w.certificateBudget + w.slack

theorem depoissonizationCertificate_budget_le_certificate
    (w : DepoissonizationCertificateWindow)
    (h : depoissonizationCertificateReady w) :
    w.certificateBudget ≤ depoissonizationCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold depoissonizationCertificate
  omega

def sampleDepoissonizationCertificateWindow :
    DepoissonizationCertificateWindow where
  radiusWindow := 6
  coefficientWindow := 7
  tailSlack := 2
  certificateBudget := 12
  slack := 1

example :
    depoissonizationCertificateReady
      sampleDepoissonizationCertificateWindow := by
  norm_num [depoissonizationCertificateReady,
    depoissonizationCertificateControlled,
    sampleDepoissonizationCertificateWindow]

example :
    sampleDepoissonizationCertificateWindow.certificateBudget ≤
      depoissonizationCertificate sampleDepoissonizationCertificateWindow := by
  apply depoissonizationCertificate_budget_le_certificate
  norm_num [depoissonizationCertificateReady,
    depoissonizationCertificateControlled,
    sampleDepoissonizationCertificateWindow]

structure DepoissonizationRefinementCertificate where
  radiusWindow : ℕ
  coefficientWindow : ℕ
  tailSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DepoissonizationRefinementCertificate.coefficientControlled
    (c : DepoissonizationRefinementCertificate) : Prop :=
  c.coefficientWindow ≤ c.radiusWindow + c.tailSlackWindow + c.slack

def DepoissonizationRefinementCertificate.certificateBudgetControlled
    (c : DepoissonizationRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.radiusWindow + c.coefficientWindow + c.tailSlackWindow + c.slack

def depoissonizationRefinementReady
    (c : DepoissonizationRefinementCertificate) : Prop :=
  0 < c.radiusWindow ∧ c.coefficientControlled ∧ c.certificateBudgetControlled

def DepoissonizationRefinementCertificate.size
    (c : DepoissonizationRefinementCertificate) : ℕ :=
  c.radiusWindow + c.coefficientWindow + c.tailSlackWindow + c.slack

theorem depoissonization_certificateBudgetWindow_le_size
    {c : DepoissonizationRefinementCertificate}
    (h : depoissonizationRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleDepoissonizationRefinementCertificate :
    DepoissonizationRefinementCertificate :=
  { radiusWindow := 6, coefficientWindow := 7, tailSlackWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : depoissonizationRefinementReady
    sampleDepoissonizationRefinementCertificate := by
  norm_num [depoissonizationRefinementReady,
    DepoissonizationRefinementCertificate.coefficientControlled,
    DepoissonizationRefinementCertificate.certificateBudgetControlled,
    sampleDepoissonizationRefinementCertificate]

example :
    sampleDepoissonizationRefinementCertificate.certificateBudgetWindow ≤
      sampleDepoissonizationRefinementCertificate.size := by
  norm_num [DepoissonizationRefinementCertificate.size,
    sampleDepoissonizationRefinementCertificate]

structure DepoissonizationBudgetCertificate where
  radiusWindow : ℕ
  coefficientWindow : ℕ
  tailSlackWindow : ℕ
  tailBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DepoissonizationBudgetCertificate.controlled
    (c : DepoissonizationBudgetCertificate) : Prop :=
  0 < c.radiusWindow ∧
    c.coefficientWindow ≤ c.radiusWindow + c.tailSlackWindow + c.slack ∧
      c.tailBudgetWindow ≤
        c.radiusWindow + c.coefficientWindow + c.tailSlackWindow + c.slack

def DepoissonizationBudgetCertificate.budgetControlled
    (c : DepoissonizationBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.radiusWindow + c.coefficientWindow + c.tailSlackWindow +
      c.tailBudgetWindow + c.slack

def DepoissonizationBudgetCertificate.Ready
    (c : DepoissonizationBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DepoissonizationBudgetCertificate.size
    (c : DepoissonizationBudgetCertificate) : ℕ :=
  c.radiusWindow + c.coefficientWindow + c.tailSlackWindow +
    c.tailBudgetWindow + c.slack

theorem depoissonization_budgetCertificate_le_size
    (c : DepoissonizationBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDepoissonizationBudgetCertificate :
    DepoissonizationBudgetCertificate :=
  { radiusWindow := 6
    coefficientWindow := 7
    tailSlackWindow := 2
    tailBudgetWindow := 16
    certificateBudgetWindow := 32
    slack := 1 }

example : sampleDepoissonizationBudgetCertificate.Ready := by
  constructor
  · norm_num [DepoissonizationBudgetCertificate.controlled,
      sampleDepoissonizationBudgetCertificate]
  · norm_num [DepoissonizationBudgetCertificate.budgetControlled,
      sampleDepoissonizationBudgetCertificate]

example :
    sampleDepoissonizationBudgetCertificate.certificateBudgetWindow ≤
      sampleDepoissonizationBudgetCertificate.size := by
  apply depoissonization_budgetCertificate_le_size
  constructor
  · norm_num [DepoissonizationBudgetCertificate.controlled,
      sampleDepoissonizationBudgetCertificate]
  · norm_num [DepoissonizationBudgetCertificate.budgetControlled,
      sampleDepoissonizationBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleDepoissonizationBudgetCertificate.Ready := by
  constructor
  · norm_num [DepoissonizationBudgetCertificate.controlled,
      sampleDepoissonizationBudgetCertificate]
  · norm_num [DepoissonizationBudgetCertificate.budgetControlled,
      sampleDepoissonizationBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDepoissonizationBudgetCertificate.certificateBudgetWindow ≤
      sampleDepoissonizationBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List DepoissonizationBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDepoissonizationBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleDepoissonizationBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.DepoissonizationWindowSchemas
