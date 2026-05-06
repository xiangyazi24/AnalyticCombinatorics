import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform partition saddle remainder schemas.

This module records finite bookkeeping for partition saddle remainders.
-/

namespace AnalyticCombinatorics.PartB.Ch8.UniformPartitionSaddleRemainderSchemas

structure PartitionSaddleRemainderData where
  partitionScale : ℕ
  remainderWindow : ℕ
  saddleSlack : ℕ
deriving DecidableEq, Repr

def hasPartitionScale (d : PartitionSaddleRemainderData) : Prop :=
  0 < d.partitionScale

def remainderWindowControlled (d : PartitionSaddleRemainderData) : Prop :=
  d.remainderWindow ≤ d.partitionScale + d.saddleSlack

def partitionSaddleRemainderReady
    (d : PartitionSaddleRemainderData) : Prop :=
  hasPartitionScale d ∧ remainderWindowControlled d

def partitionSaddleRemainderBudget
    (d : PartitionSaddleRemainderData) : ℕ :=
  d.partitionScale + d.remainderWindow + d.saddleSlack

theorem partitionSaddleRemainderReady.hasPartitionScale
    {d : PartitionSaddleRemainderData}
    (h : partitionSaddleRemainderReady d) :
    hasPartitionScale d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem remainderWindow_le_budget (d : PartitionSaddleRemainderData) :
    d.remainderWindow ≤ partitionSaddleRemainderBudget d := by
  unfold partitionSaddleRemainderBudget
  omega

def samplePartitionSaddleRemainderData : PartitionSaddleRemainderData :=
  { partitionScale := 6, remainderWindow := 8, saddleSlack := 3 }

example : partitionSaddleRemainderReady
    samplePartitionSaddleRemainderData := by
  norm_num [partitionSaddleRemainderReady, hasPartitionScale]
  norm_num [remainderWindowControlled, samplePartitionSaddleRemainderData]

example :
    partitionSaddleRemainderBudget samplePartitionSaddleRemainderData = 17 := by
  native_decide


structure UniformPartitionSaddleRemainderSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformPartitionSaddleRemainderSchemasBudgetCertificate.controlled
    (c : UniformPartitionSaddleRemainderSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformPartitionSaddleRemainderSchemasBudgetCertificate.budgetControlled
    (c : UniformPartitionSaddleRemainderSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformPartitionSaddleRemainderSchemasBudgetCertificate.Ready
    (c : UniformPartitionSaddleRemainderSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformPartitionSaddleRemainderSchemasBudgetCertificate.size
    (c : UniformPartitionSaddleRemainderSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformPartitionSaddleRemainderSchemas_budgetCertificate_le_size
    (c : UniformPartitionSaddleRemainderSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformPartitionSaddleRemainderSchemasBudgetCertificate :
    UniformPartitionSaddleRemainderSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformPartitionSaddleRemainderSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformPartitionSaddleRemainderSchemasBudgetCertificate.controlled,
      sampleUniformPartitionSaddleRemainderSchemasBudgetCertificate]
  · norm_num [UniformPartitionSaddleRemainderSchemasBudgetCertificate.budgetControlled,
      sampleUniformPartitionSaddleRemainderSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformPartitionSaddleRemainderSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformPartitionSaddleRemainderSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformPartitionSaddleRemainderSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformPartitionSaddleRemainderSchemasBudgetCertificate.controlled,
      sampleUniformPartitionSaddleRemainderSchemasBudgetCertificate]
  · norm_num [UniformPartitionSaddleRemainderSchemasBudgetCertificate.budgetControlled,
      sampleUniformPartitionSaddleRemainderSchemasBudgetCertificate]

example :
    sampleUniformPartitionSaddleRemainderSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformPartitionSaddleRemainderSchemasBudgetCertificate.size := by
  apply uniformPartitionSaddleRemainderSchemas_budgetCertificate_le_size
  constructor
  · norm_num [UniformPartitionSaddleRemainderSchemasBudgetCertificate.controlled,
      sampleUniformPartitionSaddleRemainderSchemasBudgetCertificate]
  · norm_num [UniformPartitionSaddleRemainderSchemasBudgetCertificate.budgetControlled,
      sampleUniformPartitionSaddleRemainderSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List UniformPartitionSaddleRemainderSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformPartitionSaddleRemainderSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleUniformPartitionSaddleRemainderSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.UniformPartitionSaddleRemainderSchemas

