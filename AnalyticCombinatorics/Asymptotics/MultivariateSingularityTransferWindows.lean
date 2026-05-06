import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Multivariate singularity transfer windows.

This module records finite bookkeeping for multivariate singular transfer.
-/

namespace AnalyticCombinatorics.Asymptotics.MultivariateSingularityTransferWindows

structure MultivariateSingularityTransferData where
  singularFaces : ℕ
  transferWindow : ℕ
  multivariateSlack : ℕ
deriving DecidableEq, Repr

def hasSingularFaces (d : MultivariateSingularityTransferData) : Prop :=
  0 < d.singularFaces

def transferWindowControlled
    (d : MultivariateSingularityTransferData) : Prop :=
  d.transferWindow ≤ d.singularFaces + d.multivariateSlack

def multivariateSingularityTransferReady
    (d : MultivariateSingularityTransferData) : Prop :=
  hasSingularFaces d ∧ transferWindowControlled d

def multivariateSingularityTransferBudget
    (d : MultivariateSingularityTransferData) : ℕ :=
  d.singularFaces + d.transferWindow + d.multivariateSlack

theorem multivariateSingularityTransferReady.hasSingularFaces
    {d : MultivariateSingularityTransferData}
    (h : multivariateSingularityTransferReady d) :
    hasSingularFaces d ∧ transferWindowControlled d ∧
      d.transferWindow ≤ multivariateSingularityTransferBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold multivariateSingularityTransferBudget
  omega

theorem transferWindow_le_budget
    (d : MultivariateSingularityTransferData) :
    d.transferWindow ≤ multivariateSingularityTransferBudget d := by
  unfold multivariateSingularityTransferBudget
  omega

def sampleMultivariateSingularityTransferData :
    MultivariateSingularityTransferData :=
  { singularFaces := 7, transferWindow := 9, multivariateSlack := 3 }

example : multivariateSingularityTransferReady
    sampleMultivariateSingularityTransferData := by
  norm_num [multivariateSingularityTransferReady, hasSingularFaces]
  norm_num [transferWindowControlled, sampleMultivariateSingularityTransferData]

example :
    multivariateSingularityTransferBudget
      sampleMultivariateSingularityTransferData = 19 := by
  native_decide

/-- Finite executable readiness audit for multivariate singularity transfer data. -/
def multivariateSingularityTransferDataListReady
    (data : List MultivariateSingularityTransferData) : Bool :=
  data.all fun d =>
    0 < d.singularFaces && d.transferWindow ≤ d.singularFaces + d.multivariateSlack

theorem multivariateSingularityTransferDataList_readyWindow :
    multivariateSingularityTransferDataListReady
      [{ singularFaces := 4, transferWindow := 5, multivariateSlack := 1 },
       { singularFaces := 7, transferWindow := 9, multivariateSlack := 3 }] =
      true := by
  unfold multivariateSingularityTransferDataListReady
  native_decide

/-- A certificate window for multivariate singularity transfer. -/
structure MultivariateSingularityTransferCertificateWindow where
  faceWindow : ℕ
  transferWindow : ℕ
  multivariateSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The transfer window is controlled by the singular-face window. -/
def multivariateSingularityTransferCertificateControlled
    (w : MultivariateSingularityTransferCertificateWindow) : Prop :=
  w.transferWindow ≤ w.faceWindow + w.multivariateSlack + w.slack

/-- Readiness for a multivariate singularity transfer certificate. -/
def multivariateSingularityTransferCertificateReady
    (w : MultivariateSingularityTransferCertificateWindow) : Prop :=
  0 < w.faceWindow ∧
    multivariateSingularityTransferCertificateControlled w ∧
      w.certificateBudget ≤ w.faceWindow + w.transferWindow + w.slack

/-- Total size of a multivariate singularity transfer certificate. -/
def multivariateSingularityTransferCertificate
    (w : MultivariateSingularityTransferCertificateWindow) : ℕ :=
  w.faceWindow + w.transferWindow + w.multivariateSlack +
    w.certificateBudget + w.slack

theorem multivariateSingularityTransferCertificate_budget_le_certificate
    (w : MultivariateSingularityTransferCertificateWindow)
    (h : multivariateSingularityTransferCertificateReady w) :
    w.certificateBudget ≤ multivariateSingularityTransferCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold multivariateSingularityTransferCertificate
  omega

def sampleMultivariateSingularityTransferCertificateWindow :
    MultivariateSingularityTransferCertificateWindow where
  faceWindow := 7
  transferWindow := 8
  multivariateSlack := 2
  certificateBudget := 14
  slack := 1

example :
    multivariateSingularityTransferCertificateReady
      sampleMultivariateSingularityTransferCertificateWindow := by
  norm_num [multivariateSingularityTransferCertificateReady,
    multivariateSingularityTransferCertificateControlled,
    sampleMultivariateSingularityTransferCertificateWindow]

example :
    sampleMultivariateSingularityTransferCertificateWindow.certificateBudget ≤
      multivariateSingularityTransferCertificate
        sampleMultivariateSingularityTransferCertificateWindow := by
  apply multivariateSingularityTransferCertificate_budget_le_certificate
  norm_num [multivariateSingularityTransferCertificateReady,
    multivariateSingularityTransferCertificateControlled,
    sampleMultivariateSingularityTransferCertificateWindow]

structure MultivariateSingularityTransferRefinementCertificate where
  faceWindow : ℕ
  transferWindow : ℕ
  multivariateSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MultivariateSingularityTransferRefinementCertificate.transferControlled
    (c : MultivariateSingularityTransferRefinementCertificate) : Prop :=
  c.transferWindow ≤ c.faceWindow + c.multivariateSlackWindow + c.slack

def MultivariateSingularityTransferRefinementCertificate.certificateBudgetControlled
    (c : MultivariateSingularityTransferRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.faceWindow + c.transferWindow + c.multivariateSlackWindow + c.slack

def multivariateSingularityTransferRefinementReady
    (c : MultivariateSingularityTransferRefinementCertificate) : Prop :=
  0 < c.faceWindow ∧ c.transferControlled ∧ c.certificateBudgetControlled

def MultivariateSingularityTransferRefinementCertificate.size
    (c : MultivariateSingularityTransferRefinementCertificate) : ℕ :=
  c.faceWindow + c.transferWindow + c.multivariateSlackWindow + c.slack

theorem multivariateSingularityTransfer_certificateBudgetWindow_le_size
    {c : MultivariateSingularityTransferRefinementCertificate}
    (h : multivariateSingularityTransferRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleMultivariateSingularityTransferRefinementCertificate :
    MultivariateSingularityTransferRefinementCertificate :=
  { faceWindow := 7, transferWindow := 8, multivariateSlackWindow := 2,
    certificateBudgetWindow := 18, slack := 1 }

example : multivariateSingularityTransferRefinementReady
    sampleMultivariateSingularityTransferRefinementCertificate := by
  norm_num [multivariateSingularityTransferRefinementReady,
    MultivariateSingularityTransferRefinementCertificate.transferControlled,
    MultivariateSingularityTransferRefinementCertificate.certificateBudgetControlled,
    sampleMultivariateSingularityTransferRefinementCertificate]

example :
    sampleMultivariateSingularityTransferRefinementCertificate.certificateBudgetWindow ≤
      sampleMultivariateSingularityTransferRefinementCertificate.size := by
  norm_num [MultivariateSingularityTransferRefinementCertificate.size,
    sampleMultivariateSingularityTransferRefinementCertificate]

structure MultivariateSingularityTransferBudgetCertificate where
  faceWindow : ℕ
  transferWindow : ℕ
  multivariateSlackWindow : ℕ
  transferBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MultivariateSingularityTransferBudgetCertificate.controlled
    (c : MultivariateSingularityTransferBudgetCertificate) : Prop :=
  0 < c.faceWindow ∧
    c.transferWindow ≤ c.faceWindow + c.multivariateSlackWindow + c.slack ∧
      c.transferBudgetWindow ≤
        c.faceWindow + c.transferWindow + c.multivariateSlackWindow + c.slack

def MultivariateSingularityTransferBudgetCertificate.budgetControlled
    (c : MultivariateSingularityTransferBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.faceWindow + c.transferWindow + c.multivariateSlackWindow +
      c.transferBudgetWindow + c.slack

def MultivariateSingularityTransferBudgetCertificate.Ready
    (c : MultivariateSingularityTransferBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MultivariateSingularityTransferBudgetCertificate.size
    (c : MultivariateSingularityTransferBudgetCertificate) : ℕ :=
  c.faceWindow + c.transferWindow + c.multivariateSlackWindow +
    c.transferBudgetWindow + c.slack

theorem multivariateSingularityTransfer_budgetCertificate_le_size
    (c : MultivariateSingularityTransferBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMultivariateSingularityTransferBudgetCertificate :
    MultivariateSingularityTransferBudgetCertificate :=
  { faceWindow := 7
    transferWindow := 8
    multivariateSlackWindow := 2
    transferBudgetWindow := 18
    certificateBudgetWindow := 36
    slack := 1 }

example : sampleMultivariateSingularityTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [MultivariateSingularityTransferBudgetCertificate.controlled,
      sampleMultivariateSingularityTransferBudgetCertificate]
  · norm_num [MultivariateSingularityTransferBudgetCertificate.budgetControlled,
      sampleMultivariateSingularityTransferBudgetCertificate]

example :
    sampleMultivariateSingularityTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleMultivariateSingularityTransferBudgetCertificate.size := by
  apply multivariateSingularityTransfer_budgetCertificate_le_size
  constructor
  · norm_num [MultivariateSingularityTransferBudgetCertificate.controlled,
      sampleMultivariateSingularityTransferBudgetCertificate]
  · norm_num [MultivariateSingularityTransferBudgetCertificate.budgetControlled,
      sampleMultivariateSingularityTransferBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleMultivariateSingularityTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [MultivariateSingularityTransferBudgetCertificate.controlled,
      sampleMultivariateSingularityTransferBudgetCertificate]
  · norm_num [MultivariateSingularityTransferBudgetCertificate.budgetControlled,
      sampleMultivariateSingularityTransferBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMultivariateSingularityTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleMultivariateSingularityTransferBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List MultivariateSingularityTransferBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMultivariateSingularityTransferBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleMultivariateSingularityTransferBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.MultivariateSingularityTransferWindows
