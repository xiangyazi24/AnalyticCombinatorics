import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random spatial tree limit schemas.

The finite schema records vertices, embedding dimension, and displacement
slack.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomSpatialTreeLimitSchemas

structure RandomSpatialTreeData where
  vertexCount : ℕ
  embeddingDimension : ℕ
  displacementSlack : ℕ
deriving DecidableEq, Repr

def vertexCountPositive (d : RandomSpatialTreeData) : Prop :=
  0 < d.vertexCount

def dimensionControlled (d : RandomSpatialTreeData) : Prop :=
  d.embeddingDimension ≤ d.vertexCount + d.displacementSlack

def randomSpatialTreeReady (d : RandomSpatialTreeData) : Prop :=
  vertexCountPositive d ∧ dimensionControlled d

def randomSpatialTreeBudget (d : RandomSpatialTreeData) : ℕ :=
  d.vertexCount + d.embeddingDimension + d.displacementSlack

theorem randomSpatialTreeReady.vertices {d : RandomSpatialTreeData}
    (h : randomSpatialTreeReady d) :
    vertexCountPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem dimension_le_randomSpatialTreeBudget
    (d : RandomSpatialTreeData) :
    d.embeddingDimension ≤ randomSpatialTreeBudget d := by
  unfold randomSpatialTreeBudget
  omega

def sampleRandomSpatialTreeData : RandomSpatialTreeData :=
  { vertexCount := 9, embeddingDimension := 11, displacementSlack := 3 }

example : randomSpatialTreeReady sampleRandomSpatialTreeData := by
  norm_num [randomSpatialTreeReady, vertexCountPositive]
  norm_num [dimensionControlled, sampleRandomSpatialTreeData]

example : randomSpatialTreeBudget sampleRandomSpatialTreeData = 23 := by
  native_decide

/-- Finite executable readiness audit for random spatial-tree windows. -/
def randomSpatialTreeListReady
    (windows : List RandomSpatialTreeData) : Bool :=
  windows.all fun d =>
    0 < d.vertexCount &&
      d.embeddingDimension ≤ d.vertexCount + d.displacementSlack

theorem randomSpatialTreeList_readyWindow :
    randomSpatialTreeListReady
      [{ vertexCount := 5, embeddingDimension := 6, displacementSlack := 1 },
       { vertexCount := 9, embeddingDimension := 11, displacementSlack := 3 }] =
      true := by
  unfold randomSpatialTreeListReady
  native_decide

structure RandomSpatialTreeBudgetCertificate where
  vertexCountWindow : ℕ
  embeddingDimensionWindow : ℕ
  displacementSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomSpatialTreeBudgetCertificate.controlled
    (c : RandomSpatialTreeBudgetCertificate) : Prop :=
  0 < c.vertexCountWindow ∧
    c.embeddingDimensionWindow ≤
      c.vertexCountWindow + c.displacementSlackWindow + c.slack

def RandomSpatialTreeBudgetCertificate.budgetControlled
    (c : RandomSpatialTreeBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.vertexCountWindow + c.embeddingDimensionWindow + c.displacementSlackWindow +
      c.slack

def RandomSpatialTreeBudgetCertificate.Ready
    (c : RandomSpatialTreeBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomSpatialTreeBudgetCertificate.size
    (c : RandomSpatialTreeBudgetCertificate) : ℕ :=
  c.vertexCountWindow + c.embeddingDimensionWindow + c.displacementSlackWindow +
    c.slack

theorem randomSpatialTree_budgetCertificate_le_size
    (c : RandomSpatialTreeBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomSpatialTreeBudgetCertificate :
    RandomSpatialTreeBudgetCertificate :=
  { vertexCountWindow := 9
    embeddingDimensionWindow := 11
    displacementSlackWindow := 3
    certificateBudgetWindow := 24
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomSpatialTreeBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomSpatialTreeBudgetCertificate.controlled,
      sampleRandomSpatialTreeBudgetCertificate]
  · norm_num [RandomSpatialTreeBudgetCertificate.budgetControlled,
      sampleRandomSpatialTreeBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomSpatialTreeBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomSpatialTreeBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomSpatialTreeBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomSpatialTreeBudgetCertificate.controlled,
      sampleRandomSpatialTreeBudgetCertificate]
  · norm_num [RandomSpatialTreeBudgetCertificate.budgetControlled,
      sampleRandomSpatialTreeBudgetCertificate]

example :
    sampleRandomSpatialTreeBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomSpatialTreeBudgetCertificate.size := by
  apply randomSpatialTree_budgetCertificate_le_size
  constructor
  · norm_num [RandomSpatialTreeBudgetCertificate.controlled,
      sampleRandomSpatialTreeBudgetCertificate]
  · norm_num [RandomSpatialTreeBudgetCertificate.budgetControlled,
      sampleRandomSpatialTreeBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RandomSpatialTreeBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomSpatialTreeBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomSpatialTreeBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomSpatialTreeLimitSchemas
