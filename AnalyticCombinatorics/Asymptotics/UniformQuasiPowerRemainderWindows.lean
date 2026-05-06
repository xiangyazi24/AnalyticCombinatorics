import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform quasi-power remainder windows.

This module records finite bookkeeping for quasi-power remainder windows.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformQuasiPowerRemainderWindows

structure QuasiPowerRemainderWindowData where
  cumulantScale : ℕ
  remainderWindow : ℕ
  quasiPowerSlack : ℕ
deriving DecidableEq, Repr

def hasCumulantScale (d : QuasiPowerRemainderWindowData) : Prop :=
  0 < d.cumulantScale

def remainderWindowControlled
    (d : QuasiPowerRemainderWindowData) : Prop :=
  d.remainderWindow ≤ d.cumulantScale + d.quasiPowerSlack

def quasiPowerRemainderReady
    (d : QuasiPowerRemainderWindowData) : Prop :=
  hasCumulantScale d ∧ remainderWindowControlled d

def quasiPowerRemainderBudget
    (d : QuasiPowerRemainderWindowData) : ℕ :=
  d.cumulantScale + d.remainderWindow + d.quasiPowerSlack

theorem quasiPowerRemainderReady.hasCumulantScale
    {d : QuasiPowerRemainderWindowData}
    (h : quasiPowerRemainderReady d) :
    hasCumulantScale d ∧ remainderWindowControlled d ∧
      d.remainderWindow ≤ quasiPowerRemainderBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold quasiPowerRemainderBudget
  omega

theorem remainderWindow_le_budget
    (d : QuasiPowerRemainderWindowData) :
    d.remainderWindow ≤ quasiPowerRemainderBudget d := by
  unfold quasiPowerRemainderBudget
  omega

def sampleQuasiPowerRemainderWindowData :
    QuasiPowerRemainderWindowData :=
  { cumulantScale := 7, remainderWindow := 9, quasiPowerSlack := 3 }

example : quasiPowerRemainderReady
    sampleQuasiPowerRemainderWindowData := by
  norm_num [quasiPowerRemainderReady, hasCumulantScale]
  norm_num [remainderWindowControlled, sampleQuasiPowerRemainderWindowData]

example :
    quasiPowerRemainderBudget sampleQuasiPowerRemainderWindowData = 19 := by
  native_decide

/-- Finite executable readiness audit for quasi-power remainder windows. -/
def quasiPowerRemainderWindowDataListReady
    (data : List QuasiPowerRemainderWindowData) : Bool :=
  data.all fun d =>
    0 < d.cumulantScale && d.remainderWindow ≤ d.cumulantScale + d.quasiPowerSlack

theorem quasiPowerRemainderWindowDataList_readyWindow :
    quasiPowerRemainderWindowDataListReady
      [{ cumulantScale := 4, remainderWindow := 5, quasiPowerSlack := 1 },
       { cumulantScale := 7, remainderWindow := 9, quasiPowerSlack := 3 }] = true := by
  unfold quasiPowerRemainderWindowDataListReady
  native_decide

/-- A certificate window for uniform quasi-power remainders. -/
structure QuasiPowerRemainderCertificateWindow where
  cumulantWindow : ℕ
  remainderWindow : ℕ
  quasiPowerSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The remainder window is controlled by cumulant scale and slack. -/
def quasiPowerRemainderCertificateControlled
    (w : QuasiPowerRemainderCertificateWindow) : Prop :=
  w.remainderWindow ≤ w.cumulantWindow + w.quasiPowerSlack + w.slack

/-- Readiness for a quasi-power remainder certificate. -/
def quasiPowerRemainderCertificateReady
    (w : QuasiPowerRemainderCertificateWindow) : Prop :=
  0 < w.cumulantWindow ∧
    quasiPowerRemainderCertificateControlled w ∧
      w.certificateBudget ≤ w.cumulantWindow + w.remainderWindow + w.slack

/-- Total size of a quasi-power remainder certificate. -/
def quasiPowerRemainderCertificate
    (w : QuasiPowerRemainderCertificateWindow) : ℕ :=
  w.cumulantWindow + w.remainderWindow + w.quasiPowerSlack +
    w.certificateBudget + w.slack

theorem quasiPowerRemainderCertificate_budget_le_certificate
    (w : QuasiPowerRemainderCertificateWindow)
    (h : quasiPowerRemainderCertificateReady w) :
    w.certificateBudget ≤ quasiPowerRemainderCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold quasiPowerRemainderCertificate
  omega

def sampleQuasiPowerRemainderCertificateWindow :
    QuasiPowerRemainderCertificateWindow where
  cumulantWindow := 7
  remainderWindow := 8
  quasiPowerSlack := 2
  certificateBudget := 14
  slack := 1

example :
    quasiPowerRemainderCertificateReady
      sampleQuasiPowerRemainderCertificateWindow := by
  norm_num [quasiPowerRemainderCertificateReady,
    quasiPowerRemainderCertificateControlled,
    sampleQuasiPowerRemainderCertificateWindow]

example :
    sampleQuasiPowerRemainderCertificateWindow.certificateBudget ≤
      quasiPowerRemainderCertificate
        sampleQuasiPowerRemainderCertificateWindow := by
  apply quasiPowerRemainderCertificate_budget_le_certificate
  norm_num [quasiPowerRemainderCertificateReady,
    quasiPowerRemainderCertificateControlled,
    sampleQuasiPowerRemainderCertificateWindow]

structure QuasiPowerRemainderRefinementCertificate where
  cumulantWindow : ℕ
  remainderWindow : ℕ
  quasiPowerSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def QuasiPowerRemainderRefinementCertificate.remainderControlled
    (c : QuasiPowerRemainderRefinementCertificate) : Prop :=
  c.remainderWindow ≤ c.cumulantWindow + c.quasiPowerSlackWindow + c.slack

def QuasiPowerRemainderRefinementCertificate.certificateBudgetControlled
    (c : QuasiPowerRemainderRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.cumulantWindow + c.remainderWindow + c.quasiPowerSlackWindow + c.slack

def quasiPowerRemainderRefinementReady
    (c : QuasiPowerRemainderRefinementCertificate) : Prop :=
  0 < c.cumulantWindow ∧ c.remainderControlled ∧ c.certificateBudgetControlled

def QuasiPowerRemainderRefinementCertificate.size
    (c : QuasiPowerRemainderRefinementCertificate) : ℕ :=
  c.cumulantWindow + c.remainderWindow + c.quasiPowerSlackWindow + c.slack

theorem quasiPowerRemainder_certificateBudgetWindow_le_size
    {c : QuasiPowerRemainderRefinementCertificate}
    (h : quasiPowerRemainderRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleQuasiPowerRemainderRefinementCertificate :
    QuasiPowerRemainderRefinementCertificate :=
  { cumulantWindow := 7, remainderWindow := 8, quasiPowerSlackWindow := 2,
    certificateBudgetWindow := 18, slack := 1 }

example : quasiPowerRemainderRefinementReady
    sampleQuasiPowerRemainderRefinementCertificate := by
  norm_num [quasiPowerRemainderRefinementReady,
    QuasiPowerRemainderRefinementCertificate.remainderControlled,
    QuasiPowerRemainderRefinementCertificate.certificateBudgetControlled,
    sampleQuasiPowerRemainderRefinementCertificate]

example :
    sampleQuasiPowerRemainderRefinementCertificate.certificateBudgetWindow ≤
      sampleQuasiPowerRemainderRefinementCertificate.size := by
  norm_num [QuasiPowerRemainderRefinementCertificate.size,
    sampleQuasiPowerRemainderRefinementCertificate]

structure QuasiPowerRemainderBudgetCertificate where
  cumulantWindow : ℕ
  remainderWindow : ℕ
  quasiPowerSlackWindow : ℕ
  remainderBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def QuasiPowerRemainderBudgetCertificate.controlled
    (c : QuasiPowerRemainderBudgetCertificate) : Prop :=
  0 < c.cumulantWindow ∧
    c.remainderWindow ≤ c.cumulantWindow + c.quasiPowerSlackWindow + c.slack ∧
      c.remainderBudgetWindow ≤
        c.cumulantWindow + c.remainderWindow + c.quasiPowerSlackWindow + c.slack

def QuasiPowerRemainderBudgetCertificate.budgetControlled
    (c : QuasiPowerRemainderBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.cumulantWindow + c.remainderWindow + c.quasiPowerSlackWindow +
      c.remainderBudgetWindow + c.slack

def QuasiPowerRemainderBudgetCertificate.Ready
    (c : QuasiPowerRemainderBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def QuasiPowerRemainderBudgetCertificate.size
    (c : QuasiPowerRemainderBudgetCertificate) : ℕ :=
  c.cumulantWindow + c.remainderWindow + c.quasiPowerSlackWindow +
    c.remainderBudgetWindow + c.slack

theorem quasiPowerRemainder_budgetCertificate_le_size
    (c : QuasiPowerRemainderBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleQuasiPowerRemainderBudgetCertificate :
    QuasiPowerRemainderBudgetCertificate :=
  { cumulantWindow := 7
    remainderWindow := 8
    quasiPowerSlackWindow := 2
    remainderBudgetWindow := 18
    certificateBudgetWindow := 36
    slack := 1 }

example : sampleQuasiPowerRemainderBudgetCertificate.Ready := by
  constructor
  · norm_num [QuasiPowerRemainderBudgetCertificate.controlled,
      sampleQuasiPowerRemainderBudgetCertificate]
  · norm_num [QuasiPowerRemainderBudgetCertificate.budgetControlled,
      sampleQuasiPowerRemainderBudgetCertificate]

example :
    sampleQuasiPowerRemainderBudgetCertificate.certificateBudgetWindow ≤
      sampleQuasiPowerRemainderBudgetCertificate.size := by
  apply quasiPowerRemainder_budgetCertificate_le_size
  constructor
  · norm_num [QuasiPowerRemainderBudgetCertificate.controlled,
      sampleQuasiPowerRemainderBudgetCertificate]
  · norm_num [QuasiPowerRemainderBudgetCertificate.budgetControlled,
      sampleQuasiPowerRemainderBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleQuasiPowerRemainderBudgetCertificate.Ready := by
  constructor
  · norm_num [QuasiPowerRemainderBudgetCertificate.controlled,
      sampleQuasiPowerRemainderBudgetCertificate]
  · norm_num [QuasiPowerRemainderBudgetCertificate.budgetControlled,
      sampleQuasiPowerRemainderBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleQuasiPowerRemainderBudgetCertificate.certificateBudgetWindow ≤
      sampleQuasiPowerRemainderBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List QuasiPowerRemainderBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleQuasiPowerRemainderBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleQuasiPowerRemainderBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformQuasiPowerRemainderWindows
