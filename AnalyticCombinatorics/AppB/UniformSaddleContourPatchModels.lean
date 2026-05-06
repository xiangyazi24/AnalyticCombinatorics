import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform saddle contour patch models.

This module records finite bookkeeping for saddle contour patches.
-/

namespace AnalyticCombinatorics.AppB.UniformSaddleContourPatchModels

structure SaddleContourPatchData where
  contourPatches : ℕ
  saddleOrder : ℕ
  contourSlack : ℕ
deriving DecidableEq, Repr

def hasContourPatches (d : SaddleContourPatchData) : Prop :=
  0 < d.contourPatches

def saddleOrderControlled (d : SaddleContourPatchData) : Prop :=
  d.saddleOrder ≤ d.contourPatches + d.contourSlack

def saddleContourPatchReady (d : SaddleContourPatchData) : Prop :=
  hasContourPatches d ∧ saddleOrderControlled d

def saddleContourPatchBudget (d : SaddleContourPatchData) : ℕ :=
  d.contourPatches + d.saddleOrder + d.contourSlack

theorem saddleContourPatchReady.hasContourPatches
    {d : SaddleContourPatchData}
    (h : saddleContourPatchReady d) :
    hasContourPatches d ∧ saddleOrderControlled d ∧
      d.saddleOrder ≤ saddleContourPatchBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold saddleContourPatchBudget
  omega

theorem saddleOrder_le_budget (d : SaddleContourPatchData) :
    d.saddleOrder ≤ saddleContourPatchBudget d := by
  unfold saddleContourPatchBudget
  omega

def sampleSaddleContourPatchData : SaddleContourPatchData :=
  { contourPatches := 6, saddleOrder := 8, contourSlack := 3 }

example : saddleContourPatchReady sampleSaddleContourPatchData := by
  norm_num [saddleContourPatchReady, hasContourPatches]
  norm_num [saddleOrderControlled, sampleSaddleContourPatchData]

example : saddleContourPatchBudget sampleSaddleContourPatchData = 17 := by
  native_decide

/-- Finite executable readiness audit for saddle-contour patches. -/
def saddleContourPatchListReady (windows : List SaddleContourPatchData) : Bool :=
  windows.all fun d =>
    0 < d.contourPatches && d.saddleOrder ≤ d.contourPatches + d.contourSlack

theorem saddleContourPatchList_readyWindow :
    saddleContourPatchListReady
      [{ contourPatches := 4, saddleOrder := 5, contourSlack := 1 },
       { contourPatches := 6, saddleOrder := 8, contourSlack := 3 }] = true := by
  unfold saddleContourPatchListReady
  native_decide


structure UniformSaddleContourPatchModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformSaddleContourPatchModelsBudgetCertificate.controlled
    (c : UniformSaddleContourPatchModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformSaddleContourPatchModelsBudgetCertificate.budgetControlled
    (c : UniformSaddleContourPatchModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformSaddleContourPatchModelsBudgetCertificate.Ready
    (c : UniformSaddleContourPatchModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformSaddleContourPatchModelsBudgetCertificate.size
    (c : UniformSaddleContourPatchModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformSaddleContourPatchModels_budgetCertificate_le_size
    (c : UniformSaddleContourPatchModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformSaddleContourPatchModelsBudgetCertificate :
    UniformSaddleContourPatchModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformSaddleContourPatchModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformSaddleContourPatchModelsBudgetCertificate.controlled,
      sampleUniformSaddleContourPatchModelsBudgetCertificate]
  · norm_num [UniformSaddleContourPatchModelsBudgetCertificate.budgetControlled,
      sampleUniformSaddleContourPatchModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformSaddleContourPatchModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformSaddleContourPatchModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformSaddleContourPatchModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformSaddleContourPatchModelsBudgetCertificate.controlled,
      sampleUniformSaddleContourPatchModelsBudgetCertificate]
  · norm_num [UniformSaddleContourPatchModelsBudgetCertificate.budgetControlled,
      sampleUniformSaddleContourPatchModelsBudgetCertificate]

example :
    sampleUniformSaddleContourPatchModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformSaddleContourPatchModelsBudgetCertificate.size := by
  apply uniformSaddleContourPatchModels_budgetCertificate_le_size
  constructor
  · norm_num [UniformSaddleContourPatchModelsBudgetCertificate.controlled,
      sampleUniformSaddleContourPatchModelsBudgetCertificate]
  · norm_num [UniformSaddleContourPatchModelsBudgetCertificate.budgetControlled,
      sampleUniformSaddleContourPatchModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List UniformSaddleContourPatchModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformSaddleContourPatchModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformSaddleContourPatchModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppB.UniformSaddleContourPatchModels
