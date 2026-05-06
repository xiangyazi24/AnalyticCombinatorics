import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Integer compositions and partitions.
-/

namespace AnalyticCombinatorics.PartA.Ch1.IntegerCompositionsPartitions

/-- Number of ordinary compositions of `n`, with the empty composition at `0`. -/
def compositionCount : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 ^ n

/-- Initial integer partition numbers used as a finite audit model. -/
def partitionCountSmall : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 5
  | 5 => 7
  | 6 => 11
  | _ => 0

/-- Finite comparison: partitions inject into coarser composition envelopes. -/
def partitionCompositionEnvelopeCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => partitionCountSmall n ≤ compositionCount n

theorem compositionCount_samples :
    compositionCount 0 = 1 ∧
    compositionCount 1 = 1 ∧
    compositionCount 2 = 2 ∧
    compositionCount 3 = 4 ∧
    compositionCount 4 = 8 := by
  native_decide

theorem partitionCompositionEnvelope_window :
    partitionCompositionEnvelopeCheck 6 = true := by
  unfold partitionCompositionEnvelopeCheck partitionCountSmall compositionCount
  native_decide

/-- Prefix count of ordinary compositions. -/
def compositionPrefixSum (N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl (fun total n => total + compositionCount n) 0

def CompositionPrefixWindow (N total : ℕ) : Prop :=
  compositionPrefixSum N = total

theorem compositionPrefix_window :
    CompositionPrefixWindow 5 32 := by
  unfold CompositionPrefixWindow compositionPrefixSum compositionCount
  native_decide

example : partitionCountSmall 6 = 11 := by
  unfold partitionCountSmall
  native_decide

example : compositionPrefixSum 4 = 16 := by
  unfold compositionPrefixSum compositionCount
  native_decide

structure IntegerCompositionsPartitionsBudgetCertificate where
  compositionWindow : ℕ
  partitionWindow : ℕ
  coefficientWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def IntegerCompositionsPartitionsBudgetCertificate.controlled
    (c : IntegerCompositionsPartitionsBudgetCertificate) : Prop :=
  0 < c.compositionWindow ∧
    c.coefficientWindow ≤ c.compositionWindow + c.partitionWindow + c.slack

def IntegerCompositionsPartitionsBudgetCertificate.budgetControlled
    (c : IntegerCompositionsPartitionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.compositionWindow + c.partitionWindow + c.coefficientWindow + c.slack

def IntegerCompositionsPartitionsBudgetCertificate.Ready
    (c : IntegerCompositionsPartitionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def IntegerCompositionsPartitionsBudgetCertificate.size
    (c : IntegerCompositionsPartitionsBudgetCertificate) : ℕ :=
  c.compositionWindow + c.partitionWindow + c.coefficientWindow + c.slack

theorem integerCompositionsPartitions_budgetCertificate_le_size
    (c : IntegerCompositionsPartitionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleIntegerCompositionsPartitionsBudgetCertificate :
    IntegerCompositionsPartitionsBudgetCertificate :=
  { compositionWindow := 5
    partitionWindow := 6
    coefficientWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleIntegerCompositionsPartitionsBudgetCertificate.Ready := by
  constructor
  · norm_num [IntegerCompositionsPartitionsBudgetCertificate.controlled,
      sampleIntegerCompositionsPartitionsBudgetCertificate]
  · norm_num [IntegerCompositionsPartitionsBudgetCertificate.budgetControlled,
      sampleIntegerCompositionsPartitionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleIntegerCompositionsPartitionsBudgetCertificate.certificateBudgetWindow ≤
      sampleIntegerCompositionsPartitionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleIntegerCompositionsPartitionsBudgetCertificate.Ready := by
  constructor
  · norm_num [IntegerCompositionsPartitionsBudgetCertificate.controlled,
      sampleIntegerCompositionsPartitionsBudgetCertificate]
  · norm_num [IntegerCompositionsPartitionsBudgetCertificate.budgetControlled,
      sampleIntegerCompositionsPartitionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List IntegerCompositionsPartitionsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleIntegerCompositionsPartitionsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleIntegerCompositionsPartitionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.IntegerCompositionsPartitions
