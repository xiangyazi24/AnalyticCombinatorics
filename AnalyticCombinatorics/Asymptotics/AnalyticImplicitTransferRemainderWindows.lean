import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic implicit transfer remainder windows.

This module records finite bookkeeping for implicit transfer remainders.
-/

namespace AnalyticCombinatorics.Asymptotics.AnalyticImplicitTransferRemainderWindows

structure ImplicitTransferRemainderData where
  implicitScale : ℕ
  remainderWindow : ℕ
  transferSlack : ℕ
deriving DecidableEq, Repr

def hasImplicitScale (d : ImplicitTransferRemainderData) : Prop :=
  0 < d.implicitScale

def remainderWindowControlled
    (d : ImplicitTransferRemainderData) : Prop :=
  d.remainderWindow ≤ d.implicitScale + d.transferSlack

def implicitTransferRemainderReady
    (d : ImplicitTransferRemainderData) : Prop :=
  hasImplicitScale d ∧ remainderWindowControlled d

def implicitTransferRemainderBudget
    (d : ImplicitTransferRemainderData) : ℕ :=
  d.implicitScale + d.remainderWindow + d.transferSlack

theorem implicitTransferRemainderReady.hasImplicitScale
    {d : ImplicitTransferRemainderData}
    (h : implicitTransferRemainderReady d) :
    hasImplicitScale d ∧ remainderWindowControlled d ∧
      d.remainderWindow ≤ implicitTransferRemainderBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold implicitTransferRemainderBudget
  omega

theorem remainderWindow_le_budget
    (d : ImplicitTransferRemainderData) :
    d.remainderWindow ≤ implicitTransferRemainderBudget d := by
  unfold implicitTransferRemainderBudget
  omega

def sampleImplicitTransferRemainderData :
    ImplicitTransferRemainderData :=
  { implicitScale := 6, remainderWindow := 8, transferSlack := 3 }

example : implicitTransferRemainderReady
    sampleImplicitTransferRemainderData := by
  norm_num [implicitTransferRemainderReady, hasImplicitScale]
  norm_num [remainderWindowControlled, sampleImplicitTransferRemainderData]

example :
    implicitTransferRemainderBudget sampleImplicitTransferRemainderData = 17 := by
  native_decide

/-- Finite executable readiness audit for implicit transfer remainder windows. -/
def implicitTransferRemainderListReady
    (windows : List ImplicitTransferRemainderData) : Bool :=
  windows.all fun d =>
    0 < d.implicitScale && d.remainderWindow ≤ d.implicitScale + d.transferSlack

theorem implicitTransferRemainderList_readyWindow :
    implicitTransferRemainderListReady
      [{ implicitScale := 4, remainderWindow := 5, transferSlack := 1 },
       { implicitScale := 6, remainderWindow := 8, transferSlack := 3 }] = true := by
  unfold implicitTransferRemainderListReady
  native_decide

/-- A certificate window for analytic implicit transfer remainders. -/
structure ImplicitTransferRemainderCertificateWindow where
  implicitWindow : ℕ
  remainderWindow : ℕ
  transferSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The remainder window is controlled by the implicit scale. -/
def implicitTransferRemainderCertificateControlled
    (w : ImplicitTransferRemainderCertificateWindow) : Prop :=
  w.remainderWindow ≤ w.implicitWindow + w.transferSlack + w.slack

/-- Readiness for an implicit transfer remainder certificate. -/
def implicitTransferRemainderCertificateReady
    (w : ImplicitTransferRemainderCertificateWindow) : Prop :=
  0 < w.implicitWindow ∧
    implicitTransferRemainderCertificateControlled w ∧
      w.certificateBudget ≤ w.implicitWindow + w.remainderWindow + w.slack

/-- Total size of an implicit transfer remainder certificate. -/
def implicitTransferRemainderCertificate
    (w : ImplicitTransferRemainderCertificateWindow) : ℕ :=
  w.implicitWindow + w.remainderWindow + w.transferSlack +
    w.certificateBudget + w.slack

theorem implicitTransferRemainderCertificate_budget_le_certificate
    (w : ImplicitTransferRemainderCertificateWindow)
    (h : implicitTransferRemainderCertificateReady w) :
    w.certificateBudget ≤ implicitTransferRemainderCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold implicitTransferRemainderCertificate
  omega

def sampleImplicitTransferRemainderCertificateWindow :
    ImplicitTransferRemainderCertificateWindow where
  implicitWindow := 6
  remainderWindow := 7
  transferSlack := 2
  certificateBudget := 12
  slack := 1

example :
    implicitTransferRemainderCertificateReady
      sampleImplicitTransferRemainderCertificateWindow := by
  norm_num [implicitTransferRemainderCertificateReady,
    implicitTransferRemainderCertificateControlled,
    sampleImplicitTransferRemainderCertificateWindow]

example :
    sampleImplicitTransferRemainderCertificateWindow.certificateBudget ≤
      implicitTransferRemainderCertificate
        sampleImplicitTransferRemainderCertificateWindow := by
  apply implicitTransferRemainderCertificate_budget_le_certificate
  norm_num [implicitTransferRemainderCertificateReady,
    implicitTransferRemainderCertificateControlled,
    sampleImplicitTransferRemainderCertificateWindow]

structure ImplicitTransferRemainderRefinementCertificate where
  implicitWindow : ℕ
  remainderWindow : ℕ
  transferSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ImplicitTransferRemainderRefinementCertificate.remainderControlled
    (c : ImplicitTransferRemainderRefinementCertificate) : Prop :=
  c.remainderWindow ≤ c.implicitWindow + c.transferSlackWindow + c.slack

def ImplicitTransferRemainderRefinementCertificate.certificateBudgetControlled
    (c : ImplicitTransferRemainderRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.implicitWindow + c.remainderWindow + c.transferSlackWindow + c.slack

def implicitTransferRemainderRefinementReady
    (c : ImplicitTransferRemainderRefinementCertificate) : Prop :=
  0 < c.implicitWindow ∧ c.remainderControlled ∧ c.certificateBudgetControlled

def ImplicitTransferRemainderRefinementCertificate.size
    (c : ImplicitTransferRemainderRefinementCertificate) : ℕ :=
  c.implicitWindow + c.remainderWindow + c.transferSlackWindow + c.slack

theorem implicitTransferRemainder_certificateBudgetWindow_le_size
    {c : ImplicitTransferRemainderRefinementCertificate}
    (h : implicitTransferRemainderRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleImplicitTransferRemainderRefinementCertificate :
    ImplicitTransferRemainderRefinementCertificate :=
  { implicitWindow := 6, remainderWindow := 7, transferSlackWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : implicitTransferRemainderRefinementReady
    sampleImplicitTransferRemainderRefinementCertificate := by
  norm_num [implicitTransferRemainderRefinementReady,
    ImplicitTransferRemainderRefinementCertificate.remainderControlled,
    ImplicitTransferRemainderRefinementCertificate.certificateBudgetControlled,
    sampleImplicitTransferRemainderRefinementCertificate]

example :
    sampleImplicitTransferRemainderRefinementCertificate.certificateBudgetWindow ≤
      sampleImplicitTransferRemainderRefinementCertificate.size := by
  norm_num [ImplicitTransferRemainderRefinementCertificate.size,
    sampleImplicitTransferRemainderRefinementCertificate]

structure ImplicitTransferRemainderBudgetCertificate where
  implicitWindow : ℕ
  remainderWindow : ℕ
  transferSlackWindow : ℕ
  remainderBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ImplicitTransferRemainderBudgetCertificate.controlled
    (c : ImplicitTransferRemainderBudgetCertificate) : Prop :=
  0 < c.implicitWindow ∧
    c.remainderWindow ≤ c.implicitWindow + c.transferSlackWindow + c.slack ∧
      c.remainderBudgetWindow ≤
        c.implicitWindow + c.remainderWindow + c.transferSlackWindow + c.slack

def ImplicitTransferRemainderBudgetCertificate.budgetControlled
    (c : ImplicitTransferRemainderBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.implicitWindow + c.remainderWindow + c.transferSlackWindow +
      c.remainderBudgetWindow + c.slack

def ImplicitTransferRemainderBudgetCertificate.Ready
    (c : ImplicitTransferRemainderBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ImplicitTransferRemainderBudgetCertificate.size
    (c : ImplicitTransferRemainderBudgetCertificate) : ℕ :=
  c.implicitWindow + c.remainderWindow + c.transferSlackWindow +
    c.remainderBudgetWindow + c.slack

theorem implicitTransferRemainder_budgetCertificate_le_size
    (c : ImplicitTransferRemainderBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleImplicitTransferRemainderBudgetCertificate :
    ImplicitTransferRemainderBudgetCertificate :=
  { implicitWindow := 6
    remainderWindow := 7
    transferSlackWindow := 2
    remainderBudgetWindow := 16
    certificateBudgetWindow := 32
    slack := 1 }

example : sampleImplicitTransferRemainderBudgetCertificate.Ready := by
  constructor
  · norm_num [ImplicitTransferRemainderBudgetCertificate.controlled,
      sampleImplicitTransferRemainderBudgetCertificate]
  · norm_num [ImplicitTransferRemainderBudgetCertificate.budgetControlled,
      sampleImplicitTransferRemainderBudgetCertificate]

example :
    sampleImplicitTransferRemainderBudgetCertificate.certificateBudgetWindow ≤
      sampleImplicitTransferRemainderBudgetCertificate.size := by
  apply implicitTransferRemainder_budgetCertificate_le_size
  constructor
  · norm_num [ImplicitTransferRemainderBudgetCertificate.controlled,
      sampleImplicitTransferRemainderBudgetCertificate]
  · norm_num [ImplicitTransferRemainderBudgetCertificate.budgetControlled,
      sampleImplicitTransferRemainderBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleImplicitTransferRemainderBudgetCertificate.Ready := by
  constructor
  · norm_num [ImplicitTransferRemainderBudgetCertificate.controlled,
      sampleImplicitTransferRemainderBudgetCertificate]
  · norm_num [ImplicitTransferRemainderBudgetCertificate.budgetControlled,
      sampleImplicitTransferRemainderBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleImplicitTransferRemainderBudgetCertificate.certificateBudgetWindow ≤
      sampleImplicitTransferRemainderBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List ImplicitTransferRemainderBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleImplicitTransferRemainderBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleImplicitTransferRemainderBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.AnalyticImplicitTransferRemainderWindows
