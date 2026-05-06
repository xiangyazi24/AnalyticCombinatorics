import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch6.SubexponentialSequences


/-!
Subexponential sequences and their asymptotics, following the Chapter VI
theme of contrasting subexponential, exponential, and superexponential
enumeration by finite coefficient checks.
-/

/-! ## Integer partitions -/

/-- The partition numbers `p(n)` for `n = 0, ..., 20`. -/
def partitionTable : Fin 21 → ℕ :=
  ![1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42, 56, 77, 101, 135, 176, 231, 297,
    385, 490, 627]

/-- Table lookup for partition numbers, with `0` outside the verified range. -/
def partitionSmall (n : ℕ) : ℕ :=
  if h : n < 21 then partitionTable ⟨n, h⟩ else 0

theorem partition_values_0_20 :
    partitionSmall 0 = 1 ∧
    partitionSmall 1 = 1 ∧
    partitionSmall 2 = 2 ∧
    partitionSmall 3 = 3 ∧
    partitionSmall 4 = 5 ∧
    partitionSmall 5 = 7 ∧
    partitionSmall 6 = 11 ∧
    partitionSmall 7 = 15 ∧
    partitionSmall 8 = 22 ∧
    partitionSmall 9 = 30 ∧
    partitionSmall 10 = 42 ∧
    partitionSmall 11 = 56 ∧
    partitionSmall 12 = 77 ∧
    partitionSmall 13 = 101 ∧
    partitionSmall 14 = 135 ∧
    partitionSmall 15 = 176 ∧
    partitionSmall 16 = 231 ∧
    partitionSmall 17 = 297 ∧
    partitionSmall 18 = 385 ∧
    partitionSmall 19 = 490 ∧
    partitionSmall 20 = 627 := by native_decide

/-- Numerators of `p(n+1)/p(n)` for `n = 5, ..., 19`. -/
def partitionRatioNumerator : Fin 15 → ℕ :=
  ![11, 15, 22, 30, 42, 56, 77, 101, 135, 176, 231, 297, 385, 490, 627]

/-- Denominators of `p(n+1)/p(n)` for `n = 5, ..., 19`. -/
def partitionRatioDenominator : Fin 15 → ℕ :=
  ![7, 11, 15, 22, 30, 42, 56, 77, 101, 135, 176, 231, 297, 385, 490]

theorem partition_ratio_table_n_5_19 :
    ∀ i : Fin 15,
      partitionRatioDenominator i = partitionSmall (i.val + 5) ∧
      partitionRatioNumerator i = partitionSmall (i.val + 6) := by native_decide

theorem partition_ratios_above_one_n_5_19 :
    ∀ i : Fin 15, partitionRatioDenominator i < partitionRatioNumerator i := by native_decide

theorem partition_ratios_below_eight_fifths_n_5_19 :
    ∀ i : Fin 15,
      5 * partitionRatioNumerator i < 8 * partitionRatioDenominator i := by
  native_decide

/-- Each checked ratio has gap from `1` no larger than the first checked ratio `11/7`. -/
theorem partition_ratio_gap_no_worse_than_first_n_5_19 :
    ∀ i : Fin 15,
      (partitionRatioNumerator i - partitionRatioDenominator i) * 7 ≤
        4 * partitionRatioDenominator i := by native_decide

theorem partition_ratio_19_closer_to_one_than_ratio_5 :
    (partitionSmall 20 - partitionSmall 19) * partitionSmall 5 <
      (partitionSmall 6 - partitionSmall 5) * partitionSmall 19 := by native_decide

/-! ## Compositions -/

/-- The number of compositions of `n`, with the Chapter I convention for `n ≥ 1`. -/
def compositionCount (n : ℕ) : ℕ :=
  if n = 0 then 0 else 2 ^ (n - 1)

/-- Composition counts `c(n) = 2^(n-1)` for `n = 1, ..., 15`. -/
def compositionTable : Fin 15 → ℕ :=
  ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384]

theorem composition_formula_1_15 :
    ∀ i : Fin 15, compositionTable i = compositionCount (i.val + 1) := by native_decide

/-- The finite window `p(n)/2^(n-1)` decreases for `n = 5, ..., 15`. -/
theorem partition_over_composition_decreases_5_15 :
    ∀ i : Fin 10,
      partitionSmall (i.val + 6) * compositionCount (i.val + 5) <
        partitionSmall (i.val + 5) * compositionCount (i.val + 6) := by native_decide

/-! ## Bounded-degree trees -/

/-- Binary tree counts are Catalan numbers. -/
def catalan (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

/-- Catalan numbers for `n = 0, ..., 10`. -/
def binaryTreeTable : Fin 11 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796]

theorem binary_tree_catalan_values_0_10 :
    ∀ i : Fin 11, binaryTreeTable i = catalan i.val := by native_decide

/-- Finite exponential-growth window for Catalan numbers around `4^n`. -/
theorem catalan_four_power_window_1_10 :
    ∀ i : Fin 10,
      let n := i.val + 1
      4 ^ n ≤ (n + 1) ^ 2 * catalan n ∧ catalan n < 4 ^ n := by native_decide

/-- Plane ternary tree counts: `binom(3n,n)/(2n+1)`. -/
def ternaryTree (n : ℕ) : ℕ :=
  Nat.choose (3 * n) n / (2 * n + 1)

/-- Ternary tree values for `n = 0, ..., 6`. -/
def ternaryTreeTable : Fin 7 → ℕ :=
  ![1, 1, 3, 12, 55, 273, 1428]

theorem ternary_tree_values_0_6 :
    ∀ i : Fin 7, ternaryTreeTable i = ternaryTree i.val := by native_decide

/-- The finite checks match the corrected exponential base `(27/4)^n`. -/
theorem ternary_tree_twenty_seven_over_four_window_1_6 :
    ∀ i : Fin 6,
      let n := i.val + 1
      4 ^ n * ternaryTree n < 27 ^ n ∧
        27 ^ n < (2 * n + 1) ^ 3 * 4 ^ n * ternaryTree n := by native_decide

/-! ## Involutions -/

/-- Involution numbers `I(n)` for `n = 0, ..., 10`. -/
def involutionTable : Fin 11 → ℕ :=
  ![1, 1, 2, 4, 10, 26, 76, 232, 764, 2620, 9496]

/-- Table lookup for involution numbers, with `0` outside the verified range. -/
def involutionSmall (n : ℕ) : ℕ :=
  if h : n < 11 then involutionTable ⟨n, h⟩ else 0

theorem involution_values_0_10 :
    ∀ i : Fin 11, involutionTable i = involutionSmall i.val := by native_decide

theorem involution_recurrence_2_10 :
    ∀ i : Fin 9,
      let n := i.val + 2
      involutionSmall n = involutionSmall (n - 1) + (n - 1) * involutionSmall (n - 2) :=
    by native_decide

/-- Finite subfactorial window for involutions, consistent with subexponential correction terms. -/
theorem involution_subfactorial_3_10 :
    ∀ i : Fin 8,
      let n := i.val + 3
      involutionSmall n < Nat.factorial n := by native_decide

/-! ## Set partitions -/

/-- Bell numbers `B(n)` for `n = 0, ..., 9`. -/
def bellTable : Fin 10 → ℕ :=
  ![1, 1, 2, 5, 15, 52, 203, 877, 4140, 21147]

/-- Table lookup for Bell numbers, with `0` outside the verified range. -/
def bellSmall (n : ℕ) : ℕ :=
  if h : n < 10 then bellTable ⟨n, h⟩ else 0

theorem bell_values_0_9 :
    ∀ i : Fin 10, bellTable i = bellSmall i.val := by native_decide

/-- Bell numbers grow quickly in this finite table. -/
theorem bell_more_than_doubles_3_9 :
    ∀ i : Fin 6,
      let n := i.val + 3
      2 * bellSmall n < bellSmall (n + 1) := by native_decide

/-- The strict claim `B(n) < n!` for every `n = 1, ..., 9` is false. -/
theorem bell_not_strictly_below_factorial_1_9 :
    ¬ (∀ i : Fin 9, bellSmall (i.val + 1) < Nat.factorial (i.val + 1)) := by native_decide

theorem bell_equal_factorial_at_1_and_2 :
    bellSmall 1 = Nat.factorial 1 ∧ bellSmall 2 = Nat.factorial 2 := by native_decide

theorem bell_le_factorial_1_9 :
    ∀ i : Fin 9, bellSmall (i.val + 1) ≤ Nat.factorial (i.val + 1) := by native_decide

theorem bell_lt_factorial_3_9 :
    ∀ i : Fin 7,
      let n := i.val + 3
      bellSmall n < Nat.factorial n := by native_decide



structure SubexponentialSequencesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SubexponentialSequencesBudgetCertificate.controlled
    (c : SubexponentialSequencesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SubexponentialSequencesBudgetCertificate.budgetControlled
    (c : SubexponentialSequencesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SubexponentialSequencesBudgetCertificate.Ready
    (c : SubexponentialSequencesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SubexponentialSequencesBudgetCertificate.size
    (c : SubexponentialSequencesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem subexponentialSequences_budgetCertificate_le_size
    (c : SubexponentialSequencesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSubexponentialSequencesBudgetCertificate :
    SubexponentialSequencesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleSubexponentialSequencesBudgetCertificate.Ready := by
  constructor
  · norm_num [SubexponentialSequencesBudgetCertificate.controlled,
      sampleSubexponentialSequencesBudgetCertificate]
  · norm_num [SubexponentialSequencesBudgetCertificate.budgetControlled,
      sampleSubexponentialSequencesBudgetCertificate]

example :
    sampleSubexponentialSequencesBudgetCertificate.certificateBudgetWindow ≤
      sampleSubexponentialSequencesBudgetCertificate.size := by
  apply subexponentialSequences_budgetCertificate_le_size
  constructor
  · norm_num [SubexponentialSequencesBudgetCertificate.controlled,
      sampleSubexponentialSequencesBudgetCertificate]
  · norm_num [SubexponentialSequencesBudgetCertificate.budgetControlled,
      sampleSubexponentialSequencesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSubexponentialSequencesBudgetCertificate.Ready := by
  constructor
  · norm_num [SubexponentialSequencesBudgetCertificate.controlled,
      sampleSubexponentialSequencesBudgetCertificate]
  · norm_num [SubexponentialSequencesBudgetCertificate.budgetControlled,
      sampleSubexponentialSequencesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSubexponentialSequencesBudgetCertificate.certificateBudgetWindow ≤
      sampleSubexponentialSequencesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SubexponentialSequencesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSubexponentialSequencesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSubexponentialSequencesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.SubexponentialSequences
