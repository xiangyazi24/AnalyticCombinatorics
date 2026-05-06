import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform Laplace remainders.

The finite abstraction records main scale, truncation scale, and
remainder slack for Laplace estimates.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformLaplaceRemainders

structure UniformLaplaceRemainderData where
  mainScale : ℕ
  truncationScale : ℕ
  remainderSlack : ℕ
deriving DecidableEq, Repr

def mainScalePositive (d : UniformLaplaceRemainderData) : Prop :=
  0 < d.mainScale

def truncationControlled (d : UniformLaplaceRemainderData) : Prop :=
  d.truncationScale ≤ d.mainScale + d.remainderSlack

def uniformLaplaceRemainderReady
    (d : UniformLaplaceRemainderData) : Prop :=
  mainScalePositive d ∧ truncationControlled d

def uniformLaplaceRemainderBudget
    (d : UniformLaplaceRemainderData) : ℕ :=
  d.mainScale + d.truncationScale + d.remainderSlack

theorem uniformLaplaceRemainderReady.main
    {d : UniformLaplaceRemainderData}
    (h : uniformLaplaceRemainderReady d) :
    mainScalePositive d ∧ truncationControlled d ∧
      d.truncationScale ≤ uniformLaplaceRemainderBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold uniformLaplaceRemainderBudget
  omega

theorem truncationScale_le_laplaceRemainderBudget
    (d : UniformLaplaceRemainderData) :
    d.truncationScale ≤ uniformLaplaceRemainderBudget d := by
  unfold uniformLaplaceRemainderBudget
  omega

def sampleUniformLaplaceRemainderData : UniformLaplaceRemainderData :=
  { mainScale := 6, truncationScale := 8, remainderSlack := 3 }

example : uniformLaplaceRemainderReady sampleUniformLaplaceRemainderData := by
  norm_num [uniformLaplaceRemainderReady, mainScalePositive]
  norm_num [truncationControlled, sampleUniformLaplaceRemainderData]

example :
    uniformLaplaceRemainderBudget sampleUniformLaplaceRemainderData = 17 := by
  native_decide

/-- Finite executable readiness audit for uniform Laplace remainder data. -/
def uniformLaplaceRemainderDataListReady
    (data : List UniformLaplaceRemainderData) : Bool :=
  data.all fun d =>
    0 < d.mainScale && d.truncationScale ≤ d.mainScale + d.remainderSlack

theorem uniformLaplaceRemainderDataList_readyWindow :
    uniformLaplaceRemainderDataListReady
      [{ mainScale := 4, truncationScale := 5, remainderSlack := 1 },
       { mainScale := 6, truncationScale := 8, remainderSlack := 3 }] = true := by
  unfold uniformLaplaceRemainderDataListReady
  native_decide

/-- A certificate window for uniform Laplace remainders. -/
structure UniformLaplaceRemainderCertificateWindow where
  mainWindow : ℕ
  truncationWindow : ℕ
  remainderSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The truncation window is controlled by main scale and slack. -/
def uniformLaplaceRemainderCertificateControlled
    (w : UniformLaplaceRemainderCertificateWindow) : Prop :=
  w.truncationWindow ≤ w.mainWindow + w.remainderSlack + w.slack

/-- Readiness for a Laplace remainder certificate. -/
def uniformLaplaceRemainderCertificateReady
    (w : UniformLaplaceRemainderCertificateWindow) : Prop :=
  0 < w.mainWindow ∧
    uniformLaplaceRemainderCertificateControlled w ∧
      w.certificateBudget ≤ w.mainWindow + w.truncationWindow + w.slack

/-- Total size of a Laplace remainder certificate. -/
def uniformLaplaceRemainderCertificate
    (w : UniformLaplaceRemainderCertificateWindow) : ℕ :=
  w.mainWindow + w.truncationWindow + w.remainderSlack +
    w.certificateBudget + w.slack

theorem uniformLaplaceRemainderCertificate_budget_le_certificate
    (w : UniformLaplaceRemainderCertificateWindow)
    (h : uniformLaplaceRemainderCertificateReady w) :
    w.certificateBudget ≤ uniformLaplaceRemainderCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold uniformLaplaceRemainderCertificate
  omega

def sampleUniformLaplaceRemainderCertificateWindow :
    UniformLaplaceRemainderCertificateWindow where
  mainWindow := 6
  truncationWindow := 7
  remainderSlack := 2
  certificateBudget := 12
  slack := 1

example :
    uniformLaplaceRemainderCertificateReady
      sampleUniformLaplaceRemainderCertificateWindow := by
  norm_num [uniformLaplaceRemainderCertificateReady,
    uniformLaplaceRemainderCertificateControlled,
    sampleUniformLaplaceRemainderCertificateWindow]

example :
    sampleUniformLaplaceRemainderCertificateWindow.certificateBudget ≤
      uniformLaplaceRemainderCertificate
        sampleUniformLaplaceRemainderCertificateWindow := by
  apply uniformLaplaceRemainderCertificate_budget_le_certificate
  norm_num [uniformLaplaceRemainderCertificateReady,
    uniformLaplaceRemainderCertificateControlled,
    sampleUniformLaplaceRemainderCertificateWindow]

structure UniformLaplaceRemainderRefinementCertificate where
  mainWindow : ℕ
  truncationWindow : ℕ
  remainderSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformLaplaceRemainderRefinementCertificate.truncationControlled
    (c : UniformLaplaceRemainderRefinementCertificate) : Prop :=
  c.truncationWindow ≤ c.mainWindow + c.remainderSlackWindow + c.slack

def UniformLaplaceRemainderRefinementCertificate.certificateBudgetControlled
    (c : UniformLaplaceRemainderRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.mainWindow + c.truncationWindow + c.remainderSlackWindow + c.slack

def uniformLaplaceRemainderRefinementReady
    (c : UniformLaplaceRemainderRefinementCertificate) : Prop :=
  0 < c.mainWindow ∧ c.truncationControlled ∧ c.certificateBudgetControlled

def UniformLaplaceRemainderRefinementCertificate.size
    (c : UniformLaplaceRemainderRefinementCertificate) : ℕ :=
  c.mainWindow + c.truncationWindow + c.remainderSlackWindow + c.slack

theorem uniformLaplaceRemainder_certificateBudgetWindow_le_size
    {c : UniformLaplaceRemainderRefinementCertificate}
    (h : uniformLaplaceRemainderRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleUniformLaplaceRemainderRefinementCertificate :
    UniformLaplaceRemainderRefinementCertificate :=
  { mainWindow := 6, truncationWindow := 7, remainderSlackWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : uniformLaplaceRemainderRefinementReady
    sampleUniformLaplaceRemainderRefinementCertificate := by
  norm_num [uniformLaplaceRemainderRefinementReady,
    UniformLaplaceRemainderRefinementCertificate.truncationControlled,
    UniformLaplaceRemainderRefinementCertificate.certificateBudgetControlled,
    sampleUniformLaplaceRemainderRefinementCertificate]

example :
    sampleUniformLaplaceRemainderRefinementCertificate.certificateBudgetWindow ≤
      sampleUniformLaplaceRemainderRefinementCertificate.size := by
  norm_num [UniformLaplaceRemainderRefinementCertificate.size,
    sampleUniformLaplaceRemainderRefinementCertificate]

structure UniformLaplaceRemainderBudgetCertificate where
  mainWindow : ℕ
  truncationWindow : ℕ
  remainderSlackWindow : ℕ
  remainderBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformLaplaceRemainderBudgetCertificate.controlled
    (c : UniformLaplaceRemainderBudgetCertificate) : Prop :=
  0 < c.mainWindow ∧
    c.truncationWindow ≤ c.mainWindow + c.remainderSlackWindow + c.slack ∧
      c.remainderBudgetWindow ≤
        c.mainWindow + c.truncationWindow + c.remainderSlackWindow + c.slack

def UniformLaplaceRemainderBudgetCertificate.budgetControlled
    (c : UniformLaplaceRemainderBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.mainWindow + c.truncationWindow + c.remainderSlackWindow +
      c.remainderBudgetWindow + c.slack

def UniformLaplaceRemainderBudgetCertificate.Ready
    (c : UniformLaplaceRemainderBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformLaplaceRemainderBudgetCertificate.size
    (c : UniformLaplaceRemainderBudgetCertificate) : ℕ :=
  c.mainWindow + c.truncationWindow + c.remainderSlackWindow +
    c.remainderBudgetWindow + c.slack

theorem uniformLaplaceRemainder_budgetCertificate_le_size
    (c : UniformLaplaceRemainderBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformLaplaceRemainderBudgetCertificate :
    UniformLaplaceRemainderBudgetCertificate :=
  { mainWindow := 6
    truncationWindow := 7
    remainderSlackWindow := 2
    remainderBudgetWindow := 16
    certificateBudgetWindow := 32
    slack := 1 }

example : sampleUniformLaplaceRemainderBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformLaplaceRemainderBudgetCertificate.controlled,
      sampleUniformLaplaceRemainderBudgetCertificate]
  · norm_num [UniformLaplaceRemainderBudgetCertificate.budgetControlled,
      sampleUniformLaplaceRemainderBudgetCertificate]

example :
    sampleUniformLaplaceRemainderBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformLaplaceRemainderBudgetCertificate.size := by
  apply uniformLaplaceRemainder_budgetCertificate_le_size
  constructor
  · norm_num [UniformLaplaceRemainderBudgetCertificate.controlled,
      sampleUniformLaplaceRemainderBudgetCertificate]
  · norm_num [UniformLaplaceRemainderBudgetCertificate.budgetControlled,
      sampleUniformLaplaceRemainderBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleUniformLaplaceRemainderBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformLaplaceRemainderBudgetCertificate.controlled,
      sampleUniformLaplaceRemainderBudgetCertificate]
  · norm_num [UniformLaplaceRemainderBudgetCertificate.budgetControlled,
      sampleUniformLaplaceRemainderBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformLaplaceRemainderBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformLaplaceRemainderBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List UniformLaplaceRemainderBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformLaplaceRemainderBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformLaplaceRemainderBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformLaplaceRemainders
