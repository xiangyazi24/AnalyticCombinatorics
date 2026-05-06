import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Integer partitions.
-/

namespace AnalyticCombinatorics.PartB.Ch8.IntegerPartitions

/-- Initial partition numbers used for finite saddle-window audits. -/
def partitionCountSmall : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 5
  | 5 => 7
  | 6 => 11
  | 7 => 15
  | 8 => 22
  | 9 => 30
  | 10 => 42
  | _ => 0

/-- Coarse exponential envelope for sampled partition numbers. -/
def partitionEnvelopeCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => partitionCountSmall n ≤ 2 ^ n

/-- Finite monotonicity window for partition counts. -/
def partitionMonotoneCheck (N : ℕ) : Bool :=
  (List.range N).all fun n => partitionCountSmall n ≤ partitionCountSmall (n + 1)

def PartitionSaddleWindow (N : ℕ) : Prop :=
  partitionEnvelopeCheck N = true ∧ partitionMonotoneCheck N = true

theorem partitionCountSmall_samples :
    partitionCountSmall 0 = 1 ∧
    partitionCountSmall 4 = 5 ∧
    partitionCountSmall 7 = 15 ∧
    partitionCountSmall 10 = 42 := by
  native_decide

theorem partitionSaddleWindow_small :
    PartitionSaddleWindow 10 := by
  unfold PartitionSaddleWindow partitionEnvelopeCheck partitionMonotoneCheck
    partitionCountSmall
  native_decide

/-- Prefix sum for the sampled partition table. -/
def partitionPrefixSum (N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl (fun total n => total + partitionCountSmall n) 0

theorem partitionPrefix_window :
    partitionPrefixSum 10 = 139 := by
  unfold partitionPrefixSum partitionCountSmall
  native_decide

example : partitionPrefixSum 5 = 19 := by
  unfold partitionPrefixSum partitionCountSmall
  native_decide

example : partitionMonotoneCheck 10 = true := by
  unfold partitionMonotoneCheck partitionCountSmall
  native_decide

structure IntegerPartitionsBudgetCertificate where
  partWindow : ℕ
  partitionWindow : ℕ
  saddleWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def IntegerPartitionsBudgetCertificate.controlled
    (c : IntegerPartitionsBudgetCertificate) : Prop :=
  0 < c.partWindow ∧
    c.saddleWindow ≤ c.partWindow + c.partitionWindow + c.slack

def IntegerPartitionsBudgetCertificate.budgetControlled
    (c : IntegerPartitionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.partWindow + c.partitionWindow + c.saddleWindow + c.slack

def IntegerPartitionsBudgetCertificate.Ready
    (c : IntegerPartitionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def IntegerPartitionsBudgetCertificate.size
    (c : IntegerPartitionsBudgetCertificate) : ℕ :=
  c.partWindow + c.partitionWindow + c.saddleWindow + c.slack

theorem integerPartitions_budgetCertificate_le_size
    (c : IntegerPartitionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleIntegerPartitionsBudgetCertificate :
    IntegerPartitionsBudgetCertificate :=
  { partWindow := 5
    partitionWindow := 6
    saddleWindow := 9
    certificateBudgetWindow := 21
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleIntegerPartitionsBudgetCertificate.Ready := by
  constructor
  · norm_num [IntegerPartitionsBudgetCertificate.controlled,
      sampleIntegerPartitionsBudgetCertificate]
  · norm_num [IntegerPartitionsBudgetCertificate.budgetControlled,
      sampleIntegerPartitionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleIntegerPartitionsBudgetCertificate.certificateBudgetWindow ≤
      sampleIntegerPartitionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleIntegerPartitionsBudgetCertificate.Ready := by
  constructor
  · norm_num [IntegerPartitionsBudgetCertificate.controlled,
      sampleIntegerPartitionsBudgetCertificate]
  · norm_num [IntegerPartitionsBudgetCertificate.budgetControlled,
      sampleIntegerPartitionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List IntegerPartitionsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleIntegerPartitionsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleIntegerPartitionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.IntegerPartitions
