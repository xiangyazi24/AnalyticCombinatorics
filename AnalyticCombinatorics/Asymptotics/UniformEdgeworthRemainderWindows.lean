import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform Edgeworth remainder windows.

This module records finite bookkeeping for uniform Edgeworth remainders.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformEdgeworthRemainderWindows

structure EdgeworthRemainderData where
  cumulantOrder : ℕ
  remainderWindow : ℕ
  uniformSlack : ℕ
deriving DecidableEq, Repr

def hasCumulantOrder (d : EdgeworthRemainderData) : Prop :=
  0 < d.cumulantOrder

def remainderWindowControlled (d : EdgeworthRemainderData) : Prop :=
  d.remainderWindow ≤ d.cumulantOrder + d.uniformSlack

def edgeworthRemainderReady (d : EdgeworthRemainderData) : Prop :=
  hasCumulantOrder d ∧ remainderWindowControlled d

def edgeworthRemainderBudget (d : EdgeworthRemainderData) : ℕ :=
  d.cumulantOrder + d.remainderWindow + d.uniformSlack

theorem edgeworthRemainderReady.hasCumulantOrder
    {d : EdgeworthRemainderData}
    (h : edgeworthRemainderReady d) :
    hasCumulantOrder d ∧ remainderWindowControlled d ∧
      d.remainderWindow ≤ edgeworthRemainderBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold edgeworthRemainderBudget
  omega

theorem remainderWindow_le_budget (d : EdgeworthRemainderData) :
    d.remainderWindow ≤ edgeworthRemainderBudget d := by
  unfold edgeworthRemainderBudget
  omega

def sampleEdgeworthRemainderData : EdgeworthRemainderData :=
  { cumulantOrder := 6, remainderWindow := 8, uniformSlack := 3 }

example : edgeworthRemainderReady sampleEdgeworthRemainderData := by
  norm_num [edgeworthRemainderReady, hasCumulantOrder]
  norm_num [remainderWindowControlled, sampleEdgeworthRemainderData]

example : edgeworthRemainderBudget sampleEdgeworthRemainderData = 17 := by
  native_decide

/-- Finite executable readiness audit for Edgeworth remainder data. -/
def edgeworthRemainderDataListReady
    (data : List EdgeworthRemainderData) : Bool :=
  data.all fun d =>
    0 < d.cumulantOrder && d.remainderWindow ≤ d.cumulantOrder + d.uniformSlack

theorem edgeworthRemainderDataList_readyWindow :
    edgeworthRemainderDataListReady
      [{ cumulantOrder := 4, remainderWindow := 5, uniformSlack := 1 },
       { cumulantOrder := 6, remainderWindow := 8, uniformSlack := 3 }] = true := by
  unfold edgeworthRemainderDataListReady
  native_decide

/-- A certificate window for uniform Edgeworth remainders. -/
structure EdgeworthRemainderCertificateWindow where
  cumulantWindow : ℕ
  remainderWindow : ℕ
  uniformSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The remainder window is controlled by cumulant order and slack. -/
def edgeworthRemainderCertificateControlled
    (w : EdgeworthRemainderCertificateWindow) : Prop :=
  w.remainderWindow ≤ w.cumulantWindow + w.uniformSlack + w.slack

/-- Readiness for an Edgeworth remainder certificate. -/
def edgeworthRemainderCertificateReady
    (w : EdgeworthRemainderCertificateWindow) : Prop :=
  0 < w.cumulantWindow ∧
    edgeworthRemainderCertificateControlled w ∧
      w.certificateBudget ≤ w.cumulantWindow + w.remainderWindow + w.slack

/-- Total size of an Edgeworth remainder certificate. -/
def edgeworthRemainderCertificate
    (w : EdgeworthRemainderCertificateWindow) : ℕ :=
  w.cumulantWindow + w.remainderWindow + w.uniformSlack +
    w.certificateBudget + w.slack

theorem edgeworthRemainderCertificate_budget_le_certificate
    (w : EdgeworthRemainderCertificateWindow)
    (h : edgeworthRemainderCertificateReady w) :
    w.certificateBudget ≤ edgeworthRemainderCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold edgeworthRemainderCertificate
  omega

def sampleEdgeworthRemainderCertificateWindow :
    EdgeworthRemainderCertificateWindow where
  cumulantWindow := 6
  remainderWindow := 7
  uniformSlack := 2
  certificateBudget := 12
  slack := 1

example :
    edgeworthRemainderCertificateReady
      sampleEdgeworthRemainderCertificateWindow := by
  norm_num [edgeworthRemainderCertificateReady,
    edgeworthRemainderCertificateControlled,
    sampleEdgeworthRemainderCertificateWindow]

example :
    sampleEdgeworthRemainderCertificateWindow.certificateBudget ≤
      edgeworthRemainderCertificate
        sampleEdgeworthRemainderCertificateWindow := by
  apply edgeworthRemainderCertificate_budget_le_certificate
  norm_num [edgeworthRemainderCertificateReady,
    edgeworthRemainderCertificateControlled,
    sampleEdgeworthRemainderCertificateWindow]

structure EdgeworthRemainderRefinementCertificate where
  cumulantWindow : ℕ
  remainderWindow : ℕ
  uniformSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EdgeworthRemainderRefinementCertificate.remainderControlled
    (c : EdgeworthRemainderRefinementCertificate) : Prop :=
  c.remainderWindow ≤ c.cumulantWindow + c.uniformSlackWindow + c.slack

def EdgeworthRemainderRefinementCertificate.certificateBudgetControlled
    (c : EdgeworthRemainderRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.cumulantWindow + c.remainderWindow + c.uniformSlackWindow + c.slack

def edgeworthRemainderRefinementReady
    (c : EdgeworthRemainderRefinementCertificate) : Prop :=
  0 < c.cumulantWindow ∧ c.remainderControlled ∧ c.certificateBudgetControlled

def EdgeworthRemainderRefinementCertificate.size
    (c : EdgeworthRemainderRefinementCertificate) : ℕ :=
  c.cumulantWindow + c.remainderWindow + c.uniformSlackWindow + c.slack

theorem edgeworthRemainder_certificateBudgetWindow_le_size
    {c : EdgeworthRemainderRefinementCertificate}
    (h : edgeworthRemainderRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleEdgeworthRemainderRefinementCertificate :
    EdgeworthRemainderRefinementCertificate :=
  { cumulantWindow := 6, remainderWindow := 7, uniformSlackWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : edgeworthRemainderRefinementReady
    sampleEdgeworthRemainderRefinementCertificate := by
  norm_num [edgeworthRemainderRefinementReady,
    EdgeworthRemainderRefinementCertificate.remainderControlled,
    EdgeworthRemainderRefinementCertificate.certificateBudgetControlled,
    sampleEdgeworthRemainderRefinementCertificate]

example :
    sampleEdgeworthRemainderRefinementCertificate.certificateBudgetWindow ≤
      sampleEdgeworthRemainderRefinementCertificate.size := by
  norm_num [EdgeworthRemainderRefinementCertificate.size,
    sampleEdgeworthRemainderRefinementCertificate]

structure EdgeworthRemainderBudgetCertificate where
  cumulantWindow : ℕ
  remainderWindow : ℕ
  uniformSlackWindow : ℕ
  remainderBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EdgeworthRemainderBudgetCertificate.controlled
    (c : EdgeworthRemainderBudgetCertificate) : Prop :=
  0 < c.cumulantWindow ∧
    c.remainderWindow ≤ c.cumulantWindow + c.uniformSlackWindow + c.slack ∧
      c.remainderBudgetWindow ≤
        c.cumulantWindow + c.remainderWindow + c.uniformSlackWindow + c.slack

def EdgeworthRemainderBudgetCertificate.budgetControlled
    (c : EdgeworthRemainderBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.cumulantWindow + c.remainderWindow + c.uniformSlackWindow +
      c.remainderBudgetWindow + c.slack

def EdgeworthRemainderBudgetCertificate.Ready
    (c : EdgeworthRemainderBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def EdgeworthRemainderBudgetCertificate.size
    (c : EdgeworthRemainderBudgetCertificate) : ℕ :=
  c.cumulantWindow + c.remainderWindow + c.uniformSlackWindow +
    c.remainderBudgetWindow + c.slack

theorem edgeworthRemainder_budgetCertificate_le_size
    (c : EdgeworthRemainderBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleEdgeworthRemainderBudgetCertificate :
    EdgeworthRemainderBudgetCertificate :=
  { cumulantWindow := 6
    remainderWindow := 7
    uniformSlackWindow := 2
    remainderBudgetWindow := 16
    certificateBudgetWindow := 32
    slack := 1 }

example : sampleEdgeworthRemainderBudgetCertificate.Ready := by
  constructor
  · norm_num [EdgeworthRemainderBudgetCertificate.controlled,
      sampleEdgeworthRemainderBudgetCertificate]
  · norm_num [EdgeworthRemainderBudgetCertificate.budgetControlled,
      sampleEdgeworthRemainderBudgetCertificate]

example :
    sampleEdgeworthRemainderBudgetCertificate.certificateBudgetWindow ≤
      sampleEdgeworthRemainderBudgetCertificate.size := by
  apply edgeworthRemainder_budgetCertificate_le_size
  constructor
  · norm_num [EdgeworthRemainderBudgetCertificate.controlled,
      sampleEdgeworthRemainderBudgetCertificate]
  · norm_num [EdgeworthRemainderBudgetCertificate.budgetControlled,
      sampleEdgeworthRemainderBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleEdgeworthRemainderBudgetCertificate.Ready := by
  constructor
  · norm_num [EdgeworthRemainderBudgetCertificate.controlled,
      sampleEdgeworthRemainderBudgetCertificate]
  · norm_num [EdgeworthRemainderBudgetCertificate.budgetControlled,
      sampleEdgeworthRemainderBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleEdgeworthRemainderBudgetCertificate.certificateBudgetWindow ≤
      sampleEdgeworthRemainderBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List EdgeworthRemainderBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleEdgeworthRemainderBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleEdgeworthRemainderBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformEdgeworthRemainderWindows
