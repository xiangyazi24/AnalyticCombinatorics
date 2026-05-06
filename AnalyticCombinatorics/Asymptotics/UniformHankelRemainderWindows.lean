import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform Hankel remainder windows.

This module records finite bookkeeping for Hankel remainder windows.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformHankelRemainderWindows

structure HankelRemainderWindowData where
  hankelOrder : ℕ
  remainderWindow : ℕ
  contourSlack : ℕ
deriving DecidableEq, Repr

def hasHankelOrder (d : HankelRemainderWindowData) : Prop :=
  0 < d.hankelOrder

def remainderWindowControlled (d : HankelRemainderWindowData) : Prop :=
  d.remainderWindow ≤ d.hankelOrder + d.contourSlack

def hankelRemainderWindowReady (d : HankelRemainderWindowData) : Prop :=
  hasHankelOrder d ∧ remainderWindowControlled d

def hankelRemainderWindowBudget (d : HankelRemainderWindowData) : ℕ :=
  d.hankelOrder + d.remainderWindow + d.contourSlack

theorem hankelRemainderWindowReady.hasHankelOrder
    {d : HankelRemainderWindowData}
    (h : hankelRemainderWindowReady d) :
    hasHankelOrder d ∧ remainderWindowControlled d ∧
      d.remainderWindow ≤ hankelRemainderWindowBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold hankelRemainderWindowBudget
  omega

theorem remainderWindow_le_budget (d : HankelRemainderWindowData) :
    d.remainderWindow ≤ hankelRemainderWindowBudget d := by
  unfold hankelRemainderWindowBudget
  omega

def sampleHankelRemainderWindowData : HankelRemainderWindowData :=
  { hankelOrder := 6, remainderWindow := 8, contourSlack := 3 }

example : hankelRemainderWindowReady sampleHankelRemainderWindowData := by
  norm_num [hankelRemainderWindowReady, hasHankelOrder]
  norm_num [remainderWindowControlled, sampleHankelRemainderWindowData]

example : hankelRemainderWindowBudget sampleHankelRemainderWindowData = 17 := by
  native_decide

/-- Finite executable readiness audit for Hankel remainder windows. -/
def hankelRemainderWindowDataListReady
    (data : List HankelRemainderWindowData) : Bool :=
  data.all fun d =>
    0 < d.hankelOrder && d.remainderWindow ≤ d.hankelOrder + d.contourSlack

theorem hankelRemainderWindowDataList_readyWindow :
    hankelRemainderWindowDataListReady
      [{ hankelOrder := 4, remainderWindow := 5, contourSlack := 1 },
       { hankelOrder := 6, remainderWindow := 8, contourSlack := 3 }] = true := by
  unfold hankelRemainderWindowDataListReady
  native_decide

/-- A certificate window for uniform Hankel remainders. -/
structure HankelRemainderCertificateWindow where
  hankelWindow : ℕ
  remainderWindow : ℕ
  contourSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The remainder window is controlled by the Hankel window. -/
def hankelRemainderCertificateControlled
    (w : HankelRemainderCertificateWindow) : Prop :=
  w.remainderWindow ≤ w.hankelWindow + w.contourSlack + w.slack

/-- Readiness for a Hankel remainder certificate. -/
def hankelRemainderCertificateReady
    (w : HankelRemainderCertificateWindow) : Prop :=
  0 < w.hankelWindow ∧
    hankelRemainderCertificateControlled w ∧
      w.certificateBudget ≤ w.hankelWindow + w.remainderWindow + w.slack

/-- Total size of a Hankel remainder certificate. -/
def hankelRemainderCertificate
    (w : HankelRemainderCertificateWindow) : ℕ :=
  w.hankelWindow + w.remainderWindow + w.contourSlack +
    w.certificateBudget + w.slack

theorem hankelRemainderCertificate_budget_le_certificate
    (w : HankelRemainderCertificateWindow)
    (h : hankelRemainderCertificateReady w) :
    w.certificateBudget ≤ hankelRemainderCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold hankelRemainderCertificate
  omega

def sampleHankelRemainderCertificateWindow :
    HankelRemainderCertificateWindow where
  hankelWindow := 6
  remainderWindow := 7
  contourSlack := 2
  certificateBudget := 12
  slack := 1

example :
    hankelRemainderCertificateReady
      sampleHankelRemainderCertificateWindow := by
  norm_num [hankelRemainderCertificateReady,
    hankelRemainderCertificateControlled,
    sampleHankelRemainderCertificateWindow]

example :
    sampleHankelRemainderCertificateWindow.certificateBudget ≤
      hankelRemainderCertificate sampleHankelRemainderCertificateWindow := by
  apply hankelRemainderCertificate_budget_le_certificate
  norm_num [hankelRemainderCertificateReady,
    hankelRemainderCertificateControlled,
    sampleHankelRemainderCertificateWindow]

structure HankelRemainderRefinementCertificate where
  hankelWindow : ℕ
  remainderWindow : ℕ
  contourSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HankelRemainderRefinementCertificate.remainderControlled
    (c : HankelRemainderRefinementCertificate) : Prop :=
  c.remainderWindow ≤ c.hankelWindow + c.contourSlackWindow + c.slack

def HankelRemainderRefinementCertificate.certificateBudgetControlled
    (c : HankelRemainderRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.hankelWindow + c.remainderWindow + c.contourSlackWindow + c.slack

def hankelRemainderRefinementReady
    (c : HankelRemainderRefinementCertificate) : Prop :=
  0 < c.hankelWindow ∧ c.remainderControlled ∧ c.certificateBudgetControlled

def HankelRemainderRefinementCertificate.size
    (c : HankelRemainderRefinementCertificate) : ℕ :=
  c.hankelWindow + c.remainderWindow + c.contourSlackWindow + c.slack

theorem hankelRemainder_certificateBudgetWindow_le_size
    {c : HankelRemainderRefinementCertificate}
    (h : hankelRemainderRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleHankelRemainderRefinementCertificate :
    HankelRemainderRefinementCertificate :=
  { hankelWindow := 6, remainderWindow := 7, contourSlackWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : hankelRemainderRefinementReady
    sampleHankelRemainderRefinementCertificate := by
  norm_num [hankelRemainderRefinementReady,
    HankelRemainderRefinementCertificate.remainderControlled,
    HankelRemainderRefinementCertificate.certificateBudgetControlled,
    sampleHankelRemainderRefinementCertificate]

example :
    sampleHankelRemainderRefinementCertificate.certificateBudgetWindow ≤
      sampleHankelRemainderRefinementCertificate.size := by
  norm_num [HankelRemainderRefinementCertificate.size,
    sampleHankelRemainderRefinementCertificate]

structure HankelRemainderBudgetCertificate where
  hankelWindow : ℕ
  remainderWindow : ℕ
  contourSlackWindow : ℕ
  remainderBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HankelRemainderBudgetCertificate.controlled
    (c : HankelRemainderBudgetCertificate) : Prop :=
  0 < c.hankelWindow ∧
    c.remainderWindow ≤ c.hankelWindow + c.contourSlackWindow + c.slack ∧
      c.remainderBudgetWindow ≤
        c.hankelWindow + c.remainderWindow + c.contourSlackWindow + c.slack

def HankelRemainderBudgetCertificate.budgetControlled
    (c : HankelRemainderBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.hankelWindow + c.remainderWindow + c.contourSlackWindow +
      c.remainderBudgetWindow + c.slack

def HankelRemainderBudgetCertificate.Ready
    (c : HankelRemainderBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def HankelRemainderBudgetCertificate.size
    (c : HankelRemainderBudgetCertificate) : ℕ :=
  c.hankelWindow + c.remainderWindow + c.contourSlackWindow +
    c.remainderBudgetWindow + c.slack

theorem hankelRemainder_budgetCertificate_le_size
    (c : HankelRemainderBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleHankelRemainderBudgetCertificate :
    HankelRemainderBudgetCertificate :=
  { hankelWindow := 6
    remainderWindow := 7
    contourSlackWindow := 2
    remainderBudgetWindow := 16
    certificateBudgetWindow := 32
    slack := 1 }

example : sampleHankelRemainderBudgetCertificate.Ready := by
  constructor
  · norm_num [HankelRemainderBudgetCertificate.controlled,
      sampleHankelRemainderBudgetCertificate]
  · norm_num [HankelRemainderBudgetCertificate.budgetControlled,
      sampleHankelRemainderBudgetCertificate]

example :
    sampleHankelRemainderBudgetCertificate.certificateBudgetWindow ≤
      sampleHankelRemainderBudgetCertificate.size := by
  apply hankelRemainder_budgetCertificate_le_size
  constructor
  · norm_num [HankelRemainderBudgetCertificate.controlled,
      sampleHankelRemainderBudgetCertificate]
  · norm_num [HankelRemainderBudgetCertificate.budgetControlled,
      sampleHankelRemainderBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleHankelRemainderBudgetCertificate.Ready := by
  constructor
  · norm_num [HankelRemainderBudgetCertificate.controlled,
      sampleHankelRemainderBudgetCertificate]
  · norm_num [HankelRemainderBudgetCertificate.budgetControlled,
      sampleHankelRemainderBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleHankelRemainderBudgetCertificate.certificateBudgetWindow ≤
      sampleHankelRemainderBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List HankelRemainderBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleHankelRemainderBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleHankelRemainderBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformHankelRemainderWindows
