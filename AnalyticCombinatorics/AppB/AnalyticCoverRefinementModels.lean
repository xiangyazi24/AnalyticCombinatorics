import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic cover refinement models.

This module records finite bookkeeping for analytic cover refinements.
-/

namespace AnalyticCombinatorics.AppB.AnalyticCoverRefinementModels

structure CoverRefinementData where
  baseCover : ℕ
  refinedPatches : ℕ
  refinementSlack : ℕ
deriving DecidableEq, Repr

def hasBaseCover (d : CoverRefinementData) : Prop :=
  0 < d.baseCover

def refinedPatchesControlled (d : CoverRefinementData) : Prop :=
  d.refinedPatches ≤ d.baseCover + d.refinementSlack

def coverRefinementReady (d : CoverRefinementData) : Prop :=
  hasBaseCover d ∧ refinedPatchesControlled d

def coverRefinementBudget (d : CoverRefinementData) : ℕ :=
  d.baseCover + d.refinedPatches + d.refinementSlack

theorem coverRefinementReady.hasBaseCover {d : CoverRefinementData}
    (h : coverRefinementReady d) :
    hasBaseCover d ∧ refinedPatchesControlled d ∧
      d.refinedPatches ≤ coverRefinementBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold coverRefinementBudget
  omega

theorem refinedPatches_le_budget (d : CoverRefinementData) :
    d.refinedPatches ≤ coverRefinementBudget d := by
  unfold coverRefinementBudget
  omega

def sampleCoverRefinementData : CoverRefinementData :=
  { baseCover := 6, refinedPatches := 8, refinementSlack := 3 }

example : coverRefinementReady sampleCoverRefinementData := by
  norm_num [coverRefinementReady, hasBaseCover]
  norm_num [refinedPatchesControlled, sampleCoverRefinementData]

example : coverRefinementBudget sampleCoverRefinementData = 17 := by
  native_decide

structure CoverRefinementWindow where
  basePatches : ℕ
  refinementSteps : ℕ
  compatibilitySlack : ℕ
  refinementBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CoverRefinementWindow.refinementControlled (w : CoverRefinementWindow) : Prop :=
  w.refinementSteps ≤ w.basePatches + w.compatibilitySlack + w.slack

def coverRefinementWindowReady (w : CoverRefinementWindow) : Prop :=
  0 < w.basePatches ∧ w.refinementControlled ∧
    w.refinementBudget ≤ w.basePatches + w.refinementSteps + w.slack

def CoverRefinementWindow.certificate (w : CoverRefinementWindow) : ℕ :=
  w.basePatches + w.refinementSteps + w.compatibilitySlack + w.refinementBudget + w.slack

theorem coverRefinement_refinementBudget_le_certificate (w : CoverRefinementWindow) :
    w.refinementBudget ≤ w.certificate := by
  unfold CoverRefinementWindow.certificate
  omega

def sampleCoverRefinementWindow : CoverRefinementWindow :=
  { basePatches := 5, refinementSteps := 7, compatibilitySlack := 2,
    refinementBudget := 13, slack := 3 }

example : coverRefinementWindowReady sampleCoverRefinementWindow := by
  norm_num [coverRefinementWindowReady, CoverRefinementWindow.refinementControlled,
    sampleCoverRefinementWindow]


structure AnalyticCoverRefinementModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticCoverRefinementModelsBudgetCertificate.controlled
    (c : AnalyticCoverRefinementModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticCoverRefinementModelsBudgetCertificate.budgetControlled
    (c : AnalyticCoverRefinementModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticCoverRefinementModelsBudgetCertificate.Ready
    (c : AnalyticCoverRefinementModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticCoverRefinementModelsBudgetCertificate.size
    (c : AnalyticCoverRefinementModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticCoverRefinementModels_budgetCertificate_le_size
    (c : AnalyticCoverRefinementModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticCoverRefinementModelsBudgetCertificate :
    AnalyticCoverRefinementModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticCoverRefinementModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticCoverRefinementModelsBudgetCertificate.controlled,
      sampleAnalyticCoverRefinementModelsBudgetCertificate]
  · norm_num [AnalyticCoverRefinementModelsBudgetCertificate.budgetControlled,
      sampleAnalyticCoverRefinementModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticCoverRefinementModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticCoverRefinementModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticCoverRefinementModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticCoverRefinementModelsBudgetCertificate.controlled,
      sampleAnalyticCoverRefinementModelsBudgetCertificate]
  · norm_num [AnalyticCoverRefinementModelsBudgetCertificate.budgetControlled,
      sampleAnalyticCoverRefinementModelsBudgetCertificate]

example :
    sampleAnalyticCoverRefinementModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticCoverRefinementModelsBudgetCertificate.size := by
  apply analyticCoverRefinementModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticCoverRefinementModelsBudgetCertificate.controlled,
      sampleAnalyticCoverRefinementModelsBudgetCertificate]
  · norm_num [AnalyticCoverRefinementModelsBudgetCertificate.budgetControlled,
      sampleAnalyticCoverRefinementModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List AnalyticCoverRefinementModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticCoverRefinementModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticCoverRefinementModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.AnalyticCoverRefinementModels
