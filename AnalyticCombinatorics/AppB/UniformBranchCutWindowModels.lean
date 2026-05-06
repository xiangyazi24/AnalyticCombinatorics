import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform branch cut window models.

This module records finite bookkeeping for branch cut windows.
-/

namespace AnalyticCombinatorics.AppB.UniformBranchCutWindowModels

structure BranchCutWindowData where
  branchCuts : ℕ
  continuationWindow : ℕ
  cutSlack : ℕ
deriving DecidableEq, Repr

def hasBranchCuts (d : BranchCutWindowData) : Prop :=
  0 < d.branchCuts

def continuationWindowControlled (d : BranchCutWindowData) : Prop :=
  d.continuationWindow ≤ d.branchCuts + d.cutSlack

def branchCutWindowReady (d : BranchCutWindowData) : Prop :=
  hasBranchCuts d ∧ continuationWindowControlled d

def branchCutWindowBudget (d : BranchCutWindowData) : ℕ :=
  d.branchCuts + d.continuationWindow + d.cutSlack

theorem branchCutWindowReady.hasBranchCuts {d : BranchCutWindowData}
    (h : branchCutWindowReady d) :
    hasBranchCuts d ∧ continuationWindowControlled d ∧
      d.continuationWindow ≤ branchCutWindowBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold branchCutWindowBudget
  omega

theorem continuationWindow_le_budget (d : BranchCutWindowData) :
    d.continuationWindow ≤ branchCutWindowBudget d := by
  unfold branchCutWindowBudget
  omega

def sampleBranchCutWindowData : BranchCutWindowData :=
  { branchCuts := 5, continuationWindow := 7, cutSlack := 3 }

example : branchCutWindowReady sampleBranchCutWindowData := by
  norm_num [branchCutWindowReady, hasBranchCuts]
  norm_num [continuationWindowControlled, sampleBranchCutWindowData]

example : branchCutWindowBudget sampleBranchCutWindowData = 15 := by
  native_decide

structure UniformBranchCutWindow where
  cutWindow : ℕ
  continuationWindow : ℕ
  branchSlack : ℕ
  branchBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformBranchCutWindow.continuationControlled (w : UniformBranchCutWindow) : Prop :=
  w.continuationWindow ≤ w.cutWindow + w.branchSlack + w.slack

def uniformBranchCutWindowReady (w : UniformBranchCutWindow) : Prop :=
  0 < w.cutWindow ∧ w.continuationControlled ∧
    w.branchBudget ≤ w.cutWindow + w.continuationWindow + w.slack

def UniformBranchCutWindow.certificate (w : UniformBranchCutWindow) : ℕ :=
  w.cutWindow + w.continuationWindow + w.branchSlack + w.branchBudget + w.slack

theorem uniformBranchCut_branchBudget_le_certificate (w : UniformBranchCutWindow) :
    w.branchBudget ≤ w.certificate := by
  unfold UniformBranchCutWindow.certificate
  omega

def sampleUniformBranchCutWindow : UniformBranchCutWindow :=
  { cutWindow := 4, continuationWindow := 6, branchSlack := 2, branchBudget := 11, slack := 2 }

example : uniformBranchCutWindowReady sampleUniformBranchCutWindow := by
  norm_num [uniformBranchCutWindowReady, UniformBranchCutWindow.continuationControlled,
    sampleUniformBranchCutWindow]


structure UniformBranchCutWindowModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformBranchCutWindowModelsBudgetCertificate.controlled
    (c : UniformBranchCutWindowModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformBranchCutWindowModelsBudgetCertificate.budgetControlled
    (c : UniformBranchCutWindowModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformBranchCutWindowModelsBudgetCertificate.Ready
    (c : UniformBranchCutWindowModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformBranchCutWindowModelsBudgetCertificate.size
    (c : UniformBranchCutWindowModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformBranchCutWindowModels_budgetCertificate_le_size
    (c : UniformBranchCutWindowModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformBranchCutWindowModelsBudgetCertificate :
    UniformBranchCutWindowModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformBranchCutWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformBranchCutWindowModelsBudgetCertificate.controlled,
      sampleUniformBranchCutWindowModelsBudgetCertificate]
  · norm_num [UniformBranchCutWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformBranchCutWindowModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformBranchCutWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformBranchCutWindowModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformBranchCutWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformBranchCutWindowModelsBudgetCertificate.controlled,
      sampleUniformBranchCutWindowModelsBudgetCertificate]
  · norm_num [UniformBranchCutWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformBranchCutWindowModelsBudgetCertificate]

example :
    sampleUniformBranchCutWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformBranchCutWindowModelsBudgetCertificate.size := by
  apply uniformBranchCutWindowModels_budgetCertificate_le_size
  constructor
  · norm_num [UniformBranchCutWindowModelsBudgetCertificate.controlled,
      sampleUniformBranchCutWindowModelsBudgetCertificate]
  · norm_num [UniformBranchCutWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformBranchCutWindowModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List UniformBranchCutWindowModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformBranchCutWindowModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleUniformBranchCutWindowModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.UniformBranchCutWindowModels
