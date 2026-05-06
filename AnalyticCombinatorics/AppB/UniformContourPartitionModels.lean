import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform contour partition models.

This module records finite bookkeeping for contour partition windows.
-/

namespace AnalyticCombinatorics.AppB.UniformContourPartitionModels

structure ContourPartitionData where
  contourPieces : ℕ
  partitionDepth : ℕ
  meshSlack : ℕ
deriving DecidableEq, Repr

def hasContourPieces (d : ContourPartitionData) : Prop :=
  0 < d.contourPieces

def partitionDepthControlled (d : ContourPartitionData) : Prop :=
  d.partitionDepth ≤ d.contourPieces + d.meshSlack

def contourPartitionReady (d : ContourPartitionData) : Prop :=
  hasContourPieces d ∧ partitionDepthControlled d

def contourPartitionBudget (d : ContourPartitionData) : ℕ :=
  d.contourPieces + d.partitionDepth + d.meshSlack

theorem contourPartitionReady.hasContourPieces {d : ContourPartitionData}
    (h : contourPartitionReady d) :
    hasContourPieces d ∧ partitionDepthControlled d ∧
      d.partitionDepth ≤ contourPartitionBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold contourPartitionBudget
  omega

theorem partitionDepth_le_budget (d : ContourPartitionData) :
    d.partitionDepth ≤ contourPartitionBudget d := by
  unfold contourPartitionBudget
  omega

def sampleContourPartitionData : ContourPartitionData :=
  { contourPieces := 6, partitionDepth := 8, meshSlack := 3 }

example : contourPartitionReady sampleContourPartitionData := by
  norm_num [contourPartitionReady, hasContourPieces]
  norm_num [partitionDepthControlled, sampleContourPartitionData]

example : contourPartitionBudget sampleContourPartitionData = 17 := by
  native_decide

structure UniformContourPartitionWindow where
  contourWindow : ℕ
  depthWindow : ℕ
  meshSlack : ℕ
  partitionBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformContourPartitionWindow.depthControlled
    (w : UniformContourPartitionWindow) : Prop :=
  w.depthWindow ≤ w.contourWindow + w.meshSlack + w.slack

def uniformContourPartitionWindowReady (w : UniformContourPartitionWindow) : Prop :=
  0 < w.contourWindow ∧ w.depthControlled ∧
    w.partitionBudget ≤ w.contourWindow + w.depthWindow + w.slack

def UniformContourPartitionWindow.certificate (w : UniformContourPartitionWindow) : ℕ :=
  w.contourWindow + w.depthWindow + w.meshSlack + w.partitionBudget + w.slack

theorem uniformContourPartition_partitionBudget_le_certificate
    (w : UniformContourPartitionWindow) :
    w.partitionBudget ≤ w.certificate := by
  unfold UniformContourPartitionWindow.certificate
  omega

def sampleUniformContourPartitionWindow : UniformContourPartitionWindow :=
  { contourWindow := 5, depthWindow := 7, meshSlack := 2, partitionBudget := 14, slack := 2 }

example : uniformContourPartitionWindowReady sampleUniformContourPartitionWindow := by
  norm_num [uniformContourPartitionWindowReady,
    UniformContourPartitionWindow.depthControlled, sampleUniformContourPartitionWindow]


structure UniformContourPartitionModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformContourPartitionModelsBudgetCertificate.controlled
    (c : UniformContourPartitionModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformContourPartitionModelsBudgetCertificate.budgetControlled
    (c : UniformContourPartitionModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformContourPartitionModelsBudgetCertificate.Ready
    (c : UniformContourPartitionModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformContourPartitionModelsBudgetCertificate.size
    (c : UniformContourPartitionModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformContourPartitionModels_budgetCertificate_le_size
    (c : UniformContourPartitionModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformContourPartitionModelsBudgetCertificate :
    UniformContourPartitionModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformContourPartitionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformContourPartitionModelsBudgetCertificate.controlled,
      sampleUniformContourPartitionModelsBudgetCertificate]
  · norm_num [UniformContourPartitionModelsBudgetCertificate.budgetControlled,
      sampleUniformContourPartitionModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformContourPartitionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformContourPartitionModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformContourPartitionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformContourPartitionModelsBudgetCertificate.controlled,
      sampleUniformContourPartitionModelsBudgetCertificate]
  · norm_num [UniformContourPartitionModelsBudgetCertificate.budgetControlled,
      sampleUniformContourPartitionModelsBudgetCertificate]

example :
    sampleUniformContourPartitionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformContourPartitionModelsBudgetCertificate.size := by
  apply uniformContourPartitionModels_budgetCertificate_le_size
  constructor
  · norm_num [UniformContourPartitionModelsBudgetCertificate.controlled,
      sampleUniformContourPartitionModelsBudgetCertificate]
  · norm_num [UniformContourPartitionModelsBudgetCertificate.budgetControlled,
      sampleUniformContourPartitionModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List UniformContourPartitionModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformContourPartitionModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleUniformContourPartitionModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.UniformContourPartitionModels
