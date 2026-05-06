import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Singular perturbation transfer windows.

This module records finite bookkeeping for singular perturbation transfer.
-/

namespace AnalyticCombinatorics.Asymptotics.SingularPerturbationTransferWindows

structure SingularPerturbationTransferData where
  perturbationOrder : ℕ
  transferWindow : ℕ
  singularSlack : ℕ
deriving DecidableEq, Repr

def hasPerturbationOrder (d : SingularPerturbationTransferData) : Prop :=
  0 < d.perturbationOrder

def transferWindowControlled
    (d : SingularPerturbationTransferData) : Prop :=
  d.transferWindow ≤ d.perturbationOrder + d.singularSlack

def singularPerturbationTransferReady
    (d : SingularPerturbationTransferData) : Prop :=
  hasPerturbationOrder d ∧ transferWindowControlled d

def singularPerturbationTransferBudget
    (d : SingularPerturbationTransferData) : ℕ :=
  d.perturbationOrder + d.transferWindow + d.singularSlack

theorem singularPerturbationTransferReady.hasPerturbationOrder
    {d : SingularPerturbationTransferData}
    (h : singularPerturbationTransferReady d) :
    hasPerturbationOrder d ∧ transferWindowControlled d ∧
      d.transferWindow ≤ singularPerturbationTransferBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold singularPerturbationTransferBudget
  omega

theorem transferWindow_le_budget
    (d : SingularPerturbationTransferData) :
    d.transferWindow ≤ singularPerturbationTransferBudget d := by
  unfold singularPerturbationTransferBudget
  omega

def sampleSingularPerturbationTransferData :
    SingularPerturbationTransferData :=
  { perturbationOrder := 6, transferWindow := 8, singularSlack := 3 }

example : singularPerturbationTransferReady
    sampleSingularPerturbationTransferData := by
  norm_num [singularPerturbationTransferReady, hasPerturbationOrder]
  norm_num [transferWindowControlled, sampleSingularPerturbationTransferData]

example :
    singularPerturbationTransferBudget
      sampleSingularPerturbationTransferData = 17 := by
  native_decide

/-- Finite executable readiness audit for singular perturbation transfer data. -/
def singularPerturbationTransferDataListReady
    (data : List SingularPerturbationTransferData) : Bool :=
  data.all fun d =>
    0 < d.perturbationOrder && d.transferWindow ≤ d.perturbationOrder + d.singularSlack

theorem singularPerturbationTransferDataList_readyWindow :
    singularPerturbationTransferDataListReady
      [{ perturbationOrder := 4, transferWindow := 5, singularSlack := 1 },
       { perturbationOrder := 6, transferWindow := 8, singularSlack := 3 }] =
      true := by
  unfold singularPerturbationTransferDataListReady
  native_decide

/-- A certificate window for singular perturbation transfer. -/
structure SingularPerturbationTransferCertificateWindow where
  perturbationWindow : ℕ
  transferWindow : ℕ
  singularSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The transfer window is controlled by perturbation order and slack. -/
def singularPerturbationTransferCertificateControlled
    (w : SingularPerturbationTransferCertificateWindow) : Prop :=
  w.transferWindow ≤ w.perturbationWindow + w.singularSlack + w.slack

/-- Readiness for a singular perturbation transfer certificate. -/
def singularPerturbationTransferCertificateReady
    (w : SingularPerturbationTransferCertificateWindow) : Prop :=
  0 < w.perturbationWindow ∧
    singularPerturbationTransferCertificateControlled w ∧
      w.certificateBudget ≤ w.perturbationWindow + w.transferWindow + w.slack

/-- Total size of a singular perturbation transfer certificate. -/
def singularPerturbationTransferCertificate
    (w : SingularPerturbationTransferCertificateWindow) : ℕ :=
  w.perturbationWindow + w.transferWindow + w.singularSlack +
    w.certificateBudget + w.slack

theorem singularPerturbationTransferCertificate_budget_le_certificate
    (w : SingularPerturbationTransferCertificateWindow)
    (h : singularPerturbationTransferCertificateReady w) :
    w.certificateBudget ≤ singularPerturbationTransferCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold singularPerturbationTransferCertificate
  omega

def sampleSingularPerturbationTransferCertificateWindow :
    SingularPerturbationTransferCertificateWindow where
  perturbationWindow := 6
  transferWindow := 7
  singularSlack := 2
  certificateBudget := 12
  slack := 1

example :
    singularPerturbationTransferCertificateReady
      sampleSingularPerturbationTransferCertificateWindow := by
  norm_num [singularPerturbationTransferCertificateReady,
    singularPerturbationTransferCertificateControlled,
    sampleSingularPerturbationTransferCertificateWindow]

example :
    sampleSingularPerturbationTransferCertificateWindow.certificateBudget ≤
      singularPerturbationTransferCertificate
        sampleSingularPerturbationTransferCertificateWindow := by
  apply singularPerturbationTransferCertificate_budget_le_certificate
  norm_num [singularPerturbationTransferCertificateReady,
    singularPerturbationTransferCertificateControlled,
    sampleSingularPerturbationTransferCertificateWindow]

structure SingularPerturbationTransferRefinementCertificate where
  perturbationWindow : ℕ
  transferWindow : ℕ
  singularSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SingularPerturbationTransferRefinementCertificate.transferControlled
    (c : SingularPerturbationTransferRefinementCertificate) : Prop :=
  c.transferWindow ≤ c.perturbationWindow + c.singularSlackWindow + c.slack

def SingularPerturbationTransferRefinementCertificate.certificateBudgetControlled
    (c : SingularPerturbationTransferRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.perturbationWindow + c.transferWindow + c.singularSlackWindow + c.slack

def singularPerturbationTransferRefinementReady
    (c : SingularPerturbationTransferRefinementCertificate) : Prop :=
  0 < c.perturbationWindow ∧ c.transferControlled ∧ c.certificateBudgetControlled

def SingularPerturbationTransferRefinementCertificate.size
    (c : SingularPerturbationTransferRefinementCertificate) : ℕ :=
  c.perturbationWindow + c.transferWindow + c.singularSlackWindow + c.slack

theorem singularPerturbationTransfer_certificateBudgetWindow_le_size
    {c : SingularPerturbationTransferRefinementCertificate}
    (h : singularPerturbationTransferRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleSingularPerturbationTransferRefinementCertificate :
    SingularPerturbationTransferRefinementCertificate :=
  { perturbationWindow := 6, transferWindow := 7, singularSlackWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : singularPerturbationTransferRefinementReady
    sampleSingularPerturbationTransferRefinementCertificate := by
  norm_num [singularPerturbationTransferRefinementReady,
    SingularPerturbationTransferRefinementCertificate.transferControlled,
    SingularPerturbationTransferRefinementCertificate.certificateBudgetControlled,
    sampleSingularPerturbationTransferRefinementCertificate]

example :
    sampleSingularPerturbationTransferRefinementCertificate.certificateBudgetWindow ≤
      sampleSingularPerturbationTransferRefinementCertificate.size := by
  norm_num [SingularPerturbationTransferRefinementCertificate.size,
    sampleSingularPerturbationTransferRefinementCertificate]

structure SingularPerturbationTransferBudgetCertificate where
  perturbationWindow : ℕ
  transferWindow : ℕ
  singularSlackWindow : ℕ
  transferBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SingularPerturbationTransferBudgetCertificate.controlled
    (c : SingularPerturbationTransferBudgetCertificate) : Prop :=
  0 < c.perturbationWindow ∧
    c.transferWindow ≤ c.perturbationWindow + c.singularSlackWindow + c.slack ∧
      c.transferBudgetWindow ≤
        c.perturbationWindow + c.transferWindow + c.singularSlackWindow + c.slack

def SingularPerturbationTransferBudgetCertificate.budgetControlled
    (c : SingularPerturbationTransferBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.perturbationWindow + c.transferWindow + c.singularSlackWindow +
      c.transferBudgetWindow + c.slack

def SingularPerturbationTransferBudgetCertificate.Ready
    (c : SingularPerturbationTransferBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SingularPerturbationTransferBudgetCertificate.size
    (c : SingularPerturbationTransferBudgetCertificate) : ℕ :=
  c.perturbationWindow + c.transferWindow + c.singularSlackWindow +
    c.transferBudgetWindow + c.slack

theorem singularPerturbationTransfer_budgetCertificate_le_size
    (c : SingularPerturbationTransferBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSingularPerturbationTransferBudgetCertificate :
    SingularPerturbationTransferBudgetCertificate :=
  { perturbationWindow := 6
    transferWindow := 7
    singularSlackWindow := 2
    transferBudgetWindow := 16
    certificateBudgetWindow := 32
    slack := 1 }

example : sampleSingularPerturbationTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularPerturbationTransferBudgetCertificate.controlled,
      sampleSingularPerturbationTransferBudgetCertificate]
  · norm_num [SingularPerturbationTransferBudgetCertificate.budgetControlled,
      sampleSingularPerturbationTransferBudgetCertificate]

example :
    sampleSingularPerturbationTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularPerturbationTransferBudgetCertificate.size := by
  apply singularPerturbationTransfer_budgetCertificate_le_size
  constructor
  · norm_num [SingularPerturbationTransferBudgetCertificate.controlled,
      sampleSingularPerturbationTransferBudgetCertificate]
  · norm_num [SingularPerturbationTransferBudgetCertificate.budgetControlled,
      sampleSingularPerturbationTransferBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSingularPerturbationTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularPerturbationTransferBudgetCertificate.controlled,
      sampleSingularPerturbationTransferBudgetCertificate]
  · norm_num [SingularPerturbationTransferBudgetCertificate.budgetControlled,
      sampleSingularPerturbationTransferBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSingularPerturbationTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularPerturbationTransferBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List SingularPerturbationTransferBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSingularPerturbationTransferBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleSingularPerturbationTransferBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.SingularPerturbationTransferWindows
