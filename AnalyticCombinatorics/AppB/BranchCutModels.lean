import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Branch-cut bookkeeping for analytic continuations.

This file keeps finite information about sectors, cuts, and protected
neighborhoods separate from complex analytic proofs.
-/

namespace AnalyticCombinatorics.AppB.BranchCutModels

structure BranchCutDatum where
  cutCount : ℕ
  protectedRadius : ℕ
  overlapBudget : ℕ
deriving DecidableEq, Repr

def hasBranchCut (d : BranchCutDatum) : Prop :=
  0 < d.cutCount

def protectedNeighborhood (d : BranchCutDatum) : Prop :=
  0 < d.protectedRadius

def branchCutReady (d : BranchCutDatum) : Prop :=
  hasBranchCut d ∧ protectedNeighborhood d

def branchComplexity (d : BranchCutDatum) : ℕ :=
  d.cutCount * d.protectedRadius + d.overlapBudget

theorem branchCutReady.protected {d : BranchCutDatum}
    (h : branchCutReady d) :
    hasBranchCut d ∧ protectedNeighborhood d ∧
      d.overlapBudget ≤ branchComplexity d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold branchComplexity
  omega

theorem branchComplexity_ge_overlap (d : BranchCutDatum) :
    d.overlapBudget ≤ branchComplexity d := by
  unfold branchComplexity
  omega

def sampleBranchCut : BranchCutDatum :=
  { cutCount := 2, protectedRadius := 5, overlapBudget := 3 }

example : branchCutReady sampleBranchCut := by
  norm_num [branchCutReady, hasBranchCut, protectedNeighborhood, sampleBranchCut]

example : branchComplexity sampleBranchCut = 13 := by
  native_decide

structure BranchCutWindow where
  cutWindow : ℕ
  protectedWindow : ℕ
  overlapWindow : ℕ
  continuationBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BranchCutWindow.overlapControlled (w : BranchCutWindow) : Prop :=
  w.overlapWindow ≤ w.cutWindow * w.protectedWindow + w.slack

def branchCutWindowReady (w : BranchCutWindow) : Prop :=
  0 < w.cutWindow ∧ 0 < w.protectedWindow ∧ w.overlapControlled ∧
    w.continuationBudget ≤ w.cutWindow * w.protectedWindow + w.overlapWindow + w.slack

def BranchCutWindow.certificate (w : BranchCutWindow) : ℕ :=
  w.cutWindow * w.protectedWindow + w.overlapWindow + w.continuationBudget + w.slack

theorem branchCut_continuationBudget_le_certificate (w : BranchCutWindow) :
    w.continuationBudget ≤ w.certificate := by
  unfold BranchCutWindow.certificate
  omega

def sampleBranchCutWindow : BranchCutWindow :=
  { cutWindow := 3, protectedWindow := 4, overlapWindow := 5,
    continuationBudget := 18, slack := 2 }

example : branchCutWindowReady sampleBranchCutWindow := by
  norm_num [branchCutWindowReady, BranchCutWindow.overlapControlled, sampleBranchCutWindow]


structure BranchCutModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BranchCutModelsBudgetCertificate.controlled
    (c : BranchCutModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def BranchCutModelsBudgetCertificate.budgetControlled
    (c : BranchCutModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def BranchCutModelsBudgetCertificate.Ready
    (c : BranchCutModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BranchCutModelsBudgetCertificate.size
    (c : BranchCutModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem branchCutModels_budgetCertificate_le_size
    (c : BranchCutModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleBranchCutModelsBudgetCertificate :
    BranchCutModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBranchCutModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [BranchCutModelsBudgetCertificate.controlled,
      sampleBranchCutModelsBudgetCertificate]
  · norm_num [BranchCutModelsBudgetCertificate.budgetControlled,
      sampleBranchCutModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBranchCutModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleBranchCutModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleBranchCutModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [BranchCutModelsBudgetCertificate.controlled,
      sampleBranchCutModelsBudgetCertificate]
  · norm_num [BranchCutModelsBudgetCertificate.budgetControlled,
      sampleBranchCutModelsBudgetCertificate]

example :
    sampleBranchCutModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleBranchCutModelsBudgetCertificate.size := by
  apply branchCutModels_budgetCertificate_le_size
  constructor
  · norm_num [BranchCutModelsBudgetCertificate.controlled,
      sampleBranchCutModelsBudgetCertificate]
  · norm_num [BranchCutModelsBudgetCertificate.budgetControlled,
      sampleBranchCutModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List BranchCutModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBranchCutModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleBranchCutModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.BranchCutModels
