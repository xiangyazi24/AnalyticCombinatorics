import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Partition saddle window schemas.

The finite record stores partition size, saddle scale, and tail slack.
-/

namespace AnalyticCombinatorics.PartB.Ch8.PartitionSaddleWindowSchemas

structure PartitionSaddleWindowData where
  partitionSize : ℕ
  saddleScale : ℕ
  tailSlack : ℕ
deriving DecidableEq, Repr

def saddleScalePositive (d : PartitionSaddleWindowData) : Prop :=
  0 < d.saddleScale

def partitionSizeControlled (d : PartitionSaddleWindowData) : Prop :=
  d.partitionSize ≤ d.saddleScale + d.tailSlack

def partitionSaddleWindowReady (d : PartitionSaddleWindowData) : Prop :=
  saddleScalePositive d ∧ partitionSizeControlled d

def partitionSaddleWindowBudget (d : PartitionSaddleWindowData) : ℕ :=
  d.partitionSize + d.saddleScale + d.tailSlack

theorem partitionSaddleWindowReady.scale
    {d : PartitionSaddleWindowData}
    (h : partitionSaddleWindowReady d) :
    saddleScalePositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem partitionSize_le_partitionSaddleBudget
    (d : PartitionSaddleWindowData) :
    d.partitionSize ≤ partitionSaddleWindowBudget d := by
  unfold partitionSaddleWindowBudget
  omega

def samplePartitionSaddleWindowData : PartitionSaddleWindowData :=
  { partitionSize := 7, saddleScale := 5, tailSlack := 3 }

example : partitionSaddleWindowReady samplePartitionSaddleWindowData := by
  norm_num [partitionSaddleWindowReady, saddleScalePositive]
  norm_num [partitionSizeControlled, samplePartitionSaddleWindowData]

example : partitionSaddleWindowBudget samplePartitionSaddleWindowData = 15 := by
  native_decide

structure PartitionSaddleWindowBudgetCertificate where
  partitionSizeWindow : ℕ
  saddleScaleWindow : ℕ
  tailSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PartitionSaddleWindowBudgetCertificate.controlled
    (c : PartitionSaddleWindowBudgetCertificate) : Prop :=
  0 < c.saddleScaleWindow ∧
    c.partitionSizeWindow ≤ c.saddleScaleWindow + c.tailSlackWindow + c.slack

def PartitionSaddleWindowBudgetCertificate.budgetControlled
    (c : PartitionSaddleWindowBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.partitionSizeWindow + c.saddleScaleWindow + c.tailSlackWindow + c.slack

def PartitionSaddleWindowBudgetCertificate.Ready
    (c : PartitionSaddleWindowBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PartitionSaddleWindowBudgetCertificate.size
    (c : PartitionSaddleWindowBudgetCertificate) : ℕ :=
  c.partitionSizeWindow + c.saddleScaleWindow + c.tailSlackWindow + c.slack

theorem partitionSaddleWindow_budgetCertificate_le_size
    (c : PartitionSaddleWindowBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePartitionSaddleWindowBudgetCertificate :
    PartitionSaddleWindowBudgetCertificate :=
  { partitionSizeWindow := 7
    saddleScaleWindow := 5
    tailSlackWindow := 3
    certificateBudgetWindow := 16
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    samplePartitionSaddleWindowBudgetCertificate.Ready := by
  constructor
  · norm_num [PartitionSaddleWindowBudgetCertificate.controlled,
      samplePartitionSaddleWindowBudgetCertificate]
  · norm_num [PartitionSaddleWindowBudgetCertificate.budgetControlled,
      samplePartitionSaddleWindowBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePartitionSaddleWindowBudgetCertificate.certificateBudgetWindow ≤
      samplePartitionSaddleWindowBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : samplePartitionSaddleWindowBudgetCertificate.Ready := by
  constructor
  · norm_num [PartitionSaddleWindowBudgetCertificate.controlled,
      samplePartitionSaddleWindowBudgetCertificate]
  · norm_num [PartitionSaddleWindowBudgetCertificate.budgetControlled,
      samplePartitionSaddleWindowBudgetCertificate]

example :
    samplePartitionSaddleWindowBudgetCertificate.certificateBudgetWindow ≤
      samplePartitionSaddleWindowBudgetCertificate.size := by
  apply partitionSaddleWindow_budgetCertificate_le_size
  constructor
  · norm_num [PartitionSaddleWindowBudgetCertificate.controlled,
      samplePartitionSaddleWindowBudgetCertificate]
  · norm_num [PartitionSaddleWindowBudgetCertificate.budgetControlled,
      samplePartitionSaddleWindowBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List PartitionSaddleWindowBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [samplePartitionSaddleWindowBudgetCertificate] = true := by
  unfold budgetCertificateListReady samplePartitionSaddleWindowBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.PartitionSaddleWindowSchemas
