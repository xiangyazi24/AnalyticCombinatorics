import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform Tauberian remainders.

The finite record packages main-term scale, remainder, and monotonicity
budgets.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformTauberianRemainders

structure UniformTauberianRemainderData where
  mainScale : ℕ
  remainderScale : ℕ
  monotonicityBudget : ℕ
deriving DecidableEq, Repr

def positiveMainScale (d : UniformTauberianRemainderData) : Prop :=
  0 < d.mainScale

def remainderControlled (d : UniformTauberianRemainderData) : Prop :=
  d.remainderScale ≤ d.mainScale + d.monotonicityBudget

def uniformTauberianRemainderReady
    (d : UniformTauberianRemainderData) : Prop :=
  positiveMainScale d ∧ remainderControlled d

def uniformTauberianRemainderBudget
    (d : UniformTauberianRemainderData) : ℕ :=
  d.mainScale + d.remainderScale + d.monotonicityBudget

theorem uniformTauberianRemainderReady.main
    {d : UniformTauberianRemainderData}
    (h : uniformTauberianRemainderReady d) :
    positiveMainScale d ∧ remainderControlled d ∧
      d.remainderScale ≤ uniformTauberianRemainderBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold uniformTauberianRemainderBudget
  omega

theorem remainderScale_le_tauberianRemainderBudget
    (d : UniformTauberianRemainderData) :
    d.remainderScale ≤ uniformTauberianRemainderBudget d := by
  unfold uniformTauberianRemainderBudget
  omega

def sampleUniformTauberianRemainderData :
    UniformTauberianRemainderData :=
  { mainScale := 8, remainderScale := 11, monotonicityBudget := 5 }

example :
    uniformTauberianRemainderReady
      sampleUniformTauberianRemainderData := by
  norm_num [uniformTauberianRemainderReady, positiveMainScale]
  norm_num [remainderControlled, sampleUniformTauberianRemainderData]

example :
    uniformTauberianRemainderBudget
      sampleUniformTauberianRemainderData = 24 := by
  native_decide

/-- Finite executable readiness audit for uniform Tauberian remainders. -/
def uniformTauberianRemainderDataListReady
    (data : List UniformTauberianRemainderData) : Bool :=
  data.all fun d =>
    0 < d.mainScale && d.remainderScale ≤ d.mainScale + d.monotonicityBudget

theorem uniformTauberianRemainderDataList_readyWindow :
    uniformTauberianRemainderDataListReady
      [{ mainScale := 4, remainderScale := 5, monotonicityBudget := 1 },
       { mainScale := 8, remainderScale := 11, monotonicityBudget := 5 }] = true := by
  unfold uniformTauberianRemainderDataListReady
  native_decide

/-- A certificate window for uniform Tauberian remainders. -/
structure UniformTauberianRemainderCertificateWindow where
  mainWindow : ℕ
  remainderWindow : ℕ
  monotonicityWindow : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The remainder window is controlled by main scale and monotonicity. -/
def uniformTauberianRemainderCertificateControlled
    (w : UniformTauberianRemainderCertificateWindow) : Prop :=
  w.remainderWindow ≤ w.mainWindow + w.monotonicityWindow + w.slack

/-- Readiness for a Tauberian remainder certificate. -/
def uniformTauberianRemainderCertificateReady
    (w : UniformTauberianRemainderCertificateWindow) : Prop :=
  0 < w.mainWindow ∧
    uniformTauberianRemainderCertificateControlled w ∧
      w.certificateBudget ≤ w.mainWindow + w.remainderWindow + w.slack

/-- Total size of a Tauberian remainder certificate. -/
def uniformTauberianRemainderCertificate
    (w : UniformTauberianRemainderCertificateWindow) : ℕ :=
  w.mainWindow + w.remainderWindow + w.monotonicityWindow +
    w.certificateBudget + w.slack

theorem uniformTauberianRemainderCertificate_budget_le_certificate
    (w : UniformTauberianRemainderCertificateWindow)
    (h : uniformTauberianRemainderCertificateReady w) :
    w.certificateBudget ≤ uniformTauberianRemainderCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold uniformTauberianRemainderCertificate
  omega

def sampleUniformTauberianRemainderCertificateWindow :
    UniformTauberianRemainderCertificateWindow where
  mainWindow := 8
  remainderWindow := 9
  monotonicityWindow := 4
  certificateBudget := 16
  slack := 1

example :
    uniformTauberianRemainderCertificateReady
      sampleUniformTauberianRemainderCertificateWindow := by
  norm_num [uniformTauberianRemainderCertificateReady,
    uniformTauberianRemainderCertificateControlled,
    sampleUniformTauberianRemainderCertificateWindow]

example :
    sampleUniformTauberianRemainderCertificateWindow.certificateBudget ≤
      uniformTauberianRemainderCertificate
        sampleUniformTauberianRemainderCertificateWindow := by
  apply uniformTauberianRemainderCertificate_budget_le_certificate
  norm_num [uniformTauberianRemainderCertificateReady,
    uniformTauberianRemainderCertificateControlled,
    sampleUniformTauberianRemainderCertificateWindow]

structure UniformTauberianRemainderRefinementCertificate where
  mainWindow : ℕ
  remainderWindow : ℕ
  monotonicityWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformTauberianRemainderRefinementCertificate.remainderControlled
    (c : UniformTauberianRemainderRefinementCertificate) : Prop :=
  c.remainderWindow ≤ c.mainWindow + c.monotonicityWindow + c.slack

def UniformTauberianRemainderRefinementCertificate.certificateBudgetControlled
    (c : UniformTauberianRemainderRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.mainWindow + c.remainderWindow + c.monotonicityWindow + c.slack

def uniformTauberianRemainderRefinementReady
    (c : UniformTauberianRemainderRefinementCertificate) : Prop :=
  0 < c.mainWindow ∧ c.remainderControlled ∧ c.certificateBudgetControlled

def UniformTauberianRemainderRefinementCertificate.size
    (c : UniformTauberianRemainderRefinementCertificate) : ℕ :=
  c.mainWindow + c.remainderWindow + c.monotonicityWindow + c.slack

theorem uniformTauberianRemainder_certificateBudgetWindow_le_size
    {c : UniformTauberianRemainderRefinementCertificate}
    (h : uniformTauberianRemainderRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleUniformTauberianRemainderRefinementCertificate :
    UniformTauberianRemainderRefinementCertificate :=
  { mainWindow := 8, remainderWindow := 9, monotonicityWindow := 4,
    certificateBudgetWindow := 22, slack := 1 }

example : uniformTauberianRemainderRefinementReady
    sampleUniformTauberianRemainderRefinementCertificate := by
  norm_num [uniformTauberianRemainderRefinementReady,
    UniformTauberianRemainderRefinementCertificate.remainderControlled,
    UniformTauberianRemainderRefinementCertificate.certificateBudgetControlled,
    sampleUniformTauberianRemainderRefinementCertificate]

example :
    sampleUniformTauberianRemainderRefinementCertificate.certificateBudgetWindow ≤
      sampleUniformTauberianRemainderRefinementCertificate.size := by
  norm_num [UniformTauberianRemainderRefinementCertificate.size,
    sampleUniformTauberianRemainderRefinementCertificate]

structure UniformTauberianRemainderBudgetCertificate where
  mainWindow : ℕ
  remainderWindow : ℕ
  monotonicityWindow : ℕ
  remainderBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformTauberianRemainderBudgetCertificate.controlled
    (c : UniformTauberianRemainderBudgetCertificate) : Prop :=
  0 < c.mainWindow ∧
    c.remainderWindow ≤ c.mainWindow + c.monotonicityWindow + c.slack ∧
      c.remainderBudgetWindow ≤
        c.mainWindow + c.remainderWindow + c.monotonicityWindow + c.slack

def UniformTauberianRemainderBudgetCertificate.budgetControlled
    (c : UniformTauberianRemainderBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.mainWindow + c.remainderWindow + c.monotonicityWindow +
      c.remainderBudgetWindow + c.slack

def UniformTauberianRemainderBudgetCertificate.Ready
    (c : UniformTauberianRemainderBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformTauberianRemainderBudgetCertificate.size
    (c : UniformTauberianRemainderBudgetCertificate) : ℕ :=
  c.mainWindow + c.remainderWindow + c.monotonicityWindow +
    c.remainderBudgetWindow + c.slack

theorem uniformTauberianRemainder_budgetCertificate_le_size
    (c : UniformTauberianRemainderBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformTauberianRemainderBudgetCertificate :
    UniformTauberianRemainderBudgetCertificate :=
  { mainWindow := 8
    remainderWindow := 9
    monotonicityWindow := 4
    remainderBudgetWindow := 22
    certificateBudgetWindow := 44
    slack := 1 }

example : sampleUniformTauberianRemainderBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformTauberianRemainderBudgetCertificate.controlled,
      sampleUniformTauberianRemainderBudgetCertificate]
  · norm_num [UniformTauberianRemainderBudgetCertificate.budgetControlled,
      sampleUniformTauberianRemainderBudgetCertificate]

example :
    sampleUniformTauberianRemainderBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformTauberianRemainderBudgetCertificate.size := by
  apply uniformTauberianRemainder_budgetCertificate_le_size
  constructor
  · norm_num [UniformTauberianRemainderBudgetCertificate.controlled,
      sampleUniformTauberianRemainderBudgetCertificate]
  · norm_num [UniformTauberianRemainderBudgetCertificate.budgetControlled,
      sampleUniformTauberianRemainderBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleUniformTauberianRemainderBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformTauberianRemainderBudgetCertificate.controlled,
      sampleUniformTauberianRemainderBudgetCertificate]
  · norm_num [UniformTauberianRemainderBudgetCertificate.budgetControlled,
      sampleUniformTauberianRemainderBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformTauberianRemainderBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformTauberianRemainderBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List UniformTauberianRemainderBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformTauberianRemainderBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformTauberianRemainderBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformTauberianRemainders
