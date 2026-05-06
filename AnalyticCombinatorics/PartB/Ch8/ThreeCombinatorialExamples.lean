import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Three combinatorial examples.
-/

namespace AnalyticCombinatorics.PartB.Ch8.ThreeCombinatorialExamples

/-- Three standard coefficient models used as saddle-point examples. -/
def partitionSample : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 5
  | 5 => 7
  | _ => 0

def permutationSample (n : ℕ) : ℕ :=
  n.factorial

def sequenceSample (n : ℕ) : ℕ :=
  2 ^ n

/-- Finite audit that the example families are positive on their windows. -/
def examplesPositiveCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    0 < partitionSample n ∧ 0 < permutationSample n ∧ 0 < sequenceSample n

/-- Finite statement combining the three Chapter VIII examples. -/
def ThreeExamplesWindow (N : ℕ) : Prop :=
  examplesPositiveCheck N = true

theorem threeExamplesWindow_small :
    ThreeExamplesWindow 5 := by
  unfold ThreeExamplesWindow examplesPositiveCheck partitionSample
    permutationSample sequenceSample
  native_decide

/-- Prefix total for one of the sampled saddle-point example families. -/
def examplePrefixSum (a : ℕ → ℕ) (N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl (fun total n => total + a n) 0

def ThreeExamplePrefixWindow : Prop :=
  examplePrefixSum partitionSample 5 = 19 ∧
    examplePrefixSum sequenceSample 5 = 63

theorem threeExamples_prefixWindow :
    ThreeExamplePrefixWindow := by
  unfold ThreeExamplePrefixWindow examplePrefixSum partitionSample sequenceSample
  native_decide

example : partitionSample 4 = 5 := by
  unfold partitionSample
  native_decide

example : examplePrefixSum permutationSample 4 = 34 := by
  unfold examplePrefixSum permutationSample
  native_decide

structure ThreeCombinatorialExamplesBudgetCertificate where
  partitionWindow : ℕ
  permutationWindow : ℕ
  sequenceWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ThreeCombinatorialExamplesBudgetCertificate.controlled
    (c : ThreeCombinatorialExamplesBudgetCertificate) : Prop :=
  0 < c.partitionWindow ∧
    c.sequenceWindow ≤ c.partitionWindow + c.permutationWindow + c.slack

def ThreeCombinatorialExamplesBudgetCertificate.budgetControlled
    (c : ThreeCombinatorialExamplesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.partitionWindow + c.permutationWindow + c.sequenceWindow + c.slack

def ThreeCombinatorialExamplesBudgetCertificate.Ready
    (c : ThreeCombinatorialExamplesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ThreeCombinatorialExamplesBudgetCertificate.size
    (c : ThreeCombinatorialExamplesBudgetCertificate) : ℕ :=
  c.partitionWindow + c.permutationWindow + c.sequenceWindow + c.slack

theorem threeCombinatorialExamples_budgetCertificate_le_size
    (c : ThreeCombinatorialExamplesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleThreeCombinatorialExamplesBudgetCertificate :
    ThreeCombinatorialExamplesBudgetCertificate :=
  { partitionWindow := 4
    permutationWindow := 5
    sequenceWindow := 8
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleThreeCombinatorialExamplesBudgetCertificate.Ready := by
  constructor
  · norm_num [ThreeCombinatorialExamplesBudgetCertificate.controlled,
      sampleThreeCombinatorialExamplesBudgetCertificate]
  · norm_num [ThreeCombinatorialExamplesBudgetCertificate.budgetControlled,
      sampleThreeCombinatorialExamplesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleThreeCombinatorialExamplesBudgetCertificate.certificateBudgetWindow ≤
      sampleThreeCombinatorialExamplesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleThreeCombinatorialExamplesBudgetCertificate.Ready := by
  constructor
  · norm_num [ThreeCombinatorialExamplesBudgetCertificate.controlled,
      sampleThreeCombinatorialExamplesBudgetCertificate]
  · norm_num [ThreeCombinatorialExamplesBudgetCertificate.budgetControlled,
      sampleThreeCombinatorialExamplesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List ThreeCombinatorialExamplesBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleThreeCombinatorialExamplesBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleThreeCombinatorialExamplesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.ThreeCombinatorialExamples
