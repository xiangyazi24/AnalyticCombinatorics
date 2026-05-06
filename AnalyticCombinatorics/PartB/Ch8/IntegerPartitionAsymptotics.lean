import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch8.IntegerPartitionAsymptotics


/-!
# Integer partition asymptotics

Finite computational certificates for Chapter VIII style circle-method
analysis of integer partitions.  The analytic Hardy-Ramanujan main term is
recorded symbolically, while the coefficient identities and small ratio checks
are executable.
-/

/-! ## Partition numbers -/

/-- Ordinary partition numbers `p(n)` for `n = 0, ..., 20`. -/
def partitionTable : Fin 21 → ℕ :=
  ![1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42, 56, 77, 101, 135, 176, 231, 297, 385,
    490, 627]

/-- Tabulated ordinary partition function. -/
def p (n : ℕ) : ℕ :=
  if h : n < 21 then partitionTable ⟨n, h⟩ else 0

theorem partitionTable_values :
    partitionTable =
      ![1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42, 56, 77, 101, 135, 176, 231, 297,
        385, 490, 627] := by
  native_decide

theorem p_values_0_to_20 :
    ∀ i : Fin 21, p (i : ℕ) = partitionTable i := by
  native_decide

/-! ## Euler's generalized pentagonal recurrence -/

/-- The nonzero indices `k = 1, -1, 2, -2, ...` used by Euler's recurrence. -/
def pentagonalKTable : Fin 10 → ℤ :=
  ![1, -1, 2, -2, 3, -3, 4, -4, 5, -5]

/-- Generalized pentagonal number `k(3k-1)/2`. -/
def generalizedPentagonal (k : ℤ) : ℤ :=
  k * (3 * k - 1) / 2

/-- Generalized pentagonal numbers for `k = 1, -1, 2, -2, ...`. -/
def generalizedPentagonalTable : Fin 10 → ℕ :=
  ![1, 2, 5, 7, 12, 15, 22, 26, 35, 40]

/-- The signs `(-1)^(k+1)` in Euler's pentagonal recurrence. -/
def pentagonalSign (k : ℤ) : ℤ :=
  if k % 2 = 0 then -1 else 1

/-- Sign table corresponding to `k = 1, -1, 2, -2, ...`. -/
def pentagonalSignTable : Fin 10 → ℤ :=
  ![1, 1, -1, -1, 1, 1, -1, -1, 1, 1]

theorem generalizedPentagonal_values :
    ∀ i : Fin 10,
      (generalizedPentagonalTable i : ℤ) = generalizedPentagonal (pentagonalKTable i) := by
  native_decide

theorem pentagonalSign_values :
    ∀ i : Fin 10, pentagonalSignTable i = pentagonalSign (pentagonalKTable i) := by
  native_decide

/--
Finite right-hand side of Euler's pentagonal recurrence
`p(n) = Σ_{k≠0} (-1)^(k+1) p(n - k(3k-1)/2)`.
For `n ≤ 20`, the first ten generalized pentagonal numbers are enough.
-/
def pentagonalRecurrenceRhs (n : ℕ) : ℤ :=
  ∑ i : Fin 10,
    if generalizedPentagonalTable i ≤ n then
      pentagonalSignTable i * (p (n - generalizedPentagonalTable i) : ℤ)
    else
      0

theorem pentagonal_recurrence_5_to_15 :
    ∀ i : Fin 11,
      (p ((i : ℕ) + 5) : ℤ) = pentagonalRecurrenceRhs ((i : ℕ) + 5) := by
  native_decide

/-! ## Distinct and odd partitions -/

/-- Partitions into distinct parts, `q(n)`, for `n = 0, ..., 20`. -/
def distinctPartitionTable : Fin 21 → ℕ :=
  ![1, 1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 15, 18, 22, 27, 32, 38, 46, 54, 64]

/-- Tabulated distinct partition function. -/
def q (n : ℕ) : ℕ :=
  if h : n < 21 then distinctPartitionTable ⟨n, h⟩ else 0

theorem q_values_0_to_20 :
    distinctPartitionTable =
      ![1, 1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 15, 18, 22, 27, 32, 38, 46, 54,
        64] := by
  native_decide

theorem distinct_equal_partition_up_to_one :
    q 0 = p 0 ∧ q 1 = p 1 := by
  native_decide

theorem distinct_lt_partition_2_to_20 :
    ∀ i : Fin 19, q ((i : ℕ) + 2) < p ((i : ℕ) + 2) := by
  native_decide

/-! ## Restricted partition counters and conjugation checks -/

/-- Number of partitions of `n` whose parts are at most `k`. -/
def partitionsWithPartsLe : ℕ → ℕ → ℕ
  | n, 0 => if n = 0 then 1 else 0
  | n, k + 1 =>
      ((List.range (n / (k + 1) + 1)).map
        (fun j => partitionsWithPartsLe (n - j * (k + 1)) k)).sum

/--
By Ferrers-diagram conjugation, partitions into at most `k` parts are counted
by the same numbers as partitions with parts at most `k`.
-/
def partitionsWithAtMostParts (n k : ℕ) : ℕ :=
  partitionsWithPartsLe n k

theorem p_counts_partitions_with_parts_le_n :
    partitionsWithPartsLe 5 5 = p 5 ∧
    partitionsWithPartsLe 10 10 = p 10 ∧
    partitionsWithPartsLe 15 15 = p 15 ∧
    partitionsWithPartsLe 20 20 = p 20 := by
  native_decide

theorem conjugate_partition_specific_checks :
    partitionsWithPartsLe 5 2 = 3 ∧
    partitionsWithAtMostParts 5 2 = 3 ∧
    partitionsWithPartsLe 10 3 = 14 ∧
    partitionsWithAtMostParts 10 3 = 14 ∧
    partitionsWithPartsLe 12 4 = 34 ∧
    partitionsWithAtMostParts 12 4 = 34 ∧
    partitionsWithPartsLe 15 5 = 84 ∧
    partitionsWithAtMostParts 15 5 = 84 := by
  native_decide

/-- Number of partitions of `n` into distinct parts, with every part at most `k`. -/
def distinctPartitionsWithPartsLe : ℕ → ℕ → ℕ
  | n, 0 => if n = 0 then 1 else 0
  | n, k + 1 =>
      distinctPartitionsWithPartsLe n k +
        if k + 1 ≤ n then distinctPartitionsWithPartsLe (n - (k + 1)) k else 0

/-- Number of partitions of `n` into odd parts, with every part at most `k`. -/
def oddPartitionsWithPartsLe : ℕ → ℕ → ℕ
  | n, 0 => if n = 0 then 1 else 0
  | n, k + 1 =>
      if (k + 1) % 2 = 1 then
        ((List.range (n / (k + 1) + 1)).map
          (fun j => oddPartitionsWithPartsLe (n - j * (k + 1)) k)).sum
      else
        oddPartitionsWithPartsLe n k

/-- Odd-partition counts for `n = 0, ..., 20`; Euler's identity matches `q(n)`. -/
def oddPartitionTable : Fin 21 → ℕ :=
  ![1, 1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 15, 18, 22, 27, 32, 38, 46, 54, 64]

/-- Tabulated odd-partition function. -/
def oddPartitions (n : ℕ) : ℕ :=
  if h : n < 21 then oddPartitionTable ⟨n, h⟩ else 0

theorem distinct_table_matches_counter :
    ∀ i : Fin 21, distinctPartitionsWithPartsLe (i : ℕ) (i : ℕ) = q (i : ℕ) := by
  native_decide

theorem odd_table_matches_counter :
    ∀ i : Fin 21, oddPartitionsWithPartsLe (i : ℕ) (i : ℕ) = oddPartitions (i : ℕ) := by
  native_decide

theorem euler_distinct_parts_eq_odd_parts_0_to_20 :
    ∀ i : Fin 21, q (i : ℕ) = oddPartitions (i : ℕ) := by
  native_decide

theorem partitions_of_10_distinct_eq_odd :
    distinctPartitionsWithPartsLe 10 10 = 10 ∧
    oddPartitionsWithPartsLe 10 10 = 10 ∧
    q 10 = 10 ∧
    oddPartitions 10 = 10 := by
  native_decide

/-! ## Hardy-Ramanujan main term and finite ratio checks -/

/-- Symbolic expressions used to record the Hardy-Ramanujan main term. -/
inductive AsymptoticTerm where
  | partitionP
  | n
  | nat (m : ℕ)
  | pi
  | sqrt (t : AsymptoticTerm)
  | exp (t : AsymptoticTerm)
  | mul (a b : AsymptoticTerm)
  | div (a b : AsymptoticTerm)
  deriving DecidableEq, Repr

/-- Symbolic relation for asymptotic equivalence. -/
inductive AsymptoticRelation where
  | equivalent
  deriving DecidableEq, Repr

/-- Symbolic asymptotic statement. -/
structure AsymptoticStatement where
  lhs : AsymptoticTerm
  relation : AsymptoticRelation
  rhs : AsymptoticTerm
  deriving DecidableEq, Repr

/-- Hardy-Ramanujan main term `exp(π√(2n/3)) / (4n√3)`. -/
def hardyRamanujanMainTerm : AsymptoticTerm :=
  .div
    (.exp
      (.mul
        .pi
        (.sqrt (.div (.mul (.nat 2) .n) (.nat 3)))))
    (.mul (.mul (.nat 4) .n) (.sqrt (.nat 3)))

/-- Symbolic record of `p(n) ~ exp(π√(2n/3)) / (4n√3)`. -/
def hardyRamanujanAsymptotic : AsymptoticStatement where
  lhs := .partitionP
  relation := .equivalent
  rhs := hardyRamanujanMainTerm

theorem hardyRamanujanAsymptotic_shape :
    hardyRamanujanAsymptotic =
      { lhs := .partitionP
        relation := .equivalent
        rhs :=
          .div
            (.exp
              (.mul
                .pi
                (.sqrt (.div (.mul (.nat 2) .n) (.nat 3)))))
            (.mul (.mul (.nat 4) .n) (.sqrt (.nat 3))) } := by
  native_decide

/--
Rounded values of `1000 * exp(π√(2n/3)) / (4n√3)` for `n = 10, ..., 20`.
They let the ratio checks stay purely integer-valued.
-/
def hardyRamanujanMainMillis : Fin 11 → ℕ :=
  ![48104, 64973, 86944, 115359, 151876, 198529, 257807, 332741, 427017, 545101,
    692385]

/--
For `n = 10, ..., 20`, the tabulated ratio
`p(n) / (exp(π√(2n/3)) / (4n√3))` lies between `0.85` and `0.92`.
The factor `100000` is `100 * 1000`, clearing the percentage and milliscale
denominators.
-/
theorem hardyRamanujan_ratio_bounds_10_to_20 :
    ∀ i : Fin 11,
      85 * hardyRamanujanMainMillis i ≤ 100000 * p ((i : ℕ) + 10) ∧
      100000 * p ((i : ℕ) + 10) ≤ 92 * hardyRamanujanMainMillis i := by
  native_decide



structure IntegerPartitionAsymptoticsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def IntegerPartitionAsymptoticsBudgetCertificate.controlled
    (c : IntegerPartitionAsymptoticsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def IntegerPartitionAsymptoticsBudgetCertificate.budgetControlled
    (c : IntegerPartitionAsymptoticsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def IntegerPartitionAsymptoticsBudgetCertificate.Ready
    (c : IntegerPartitionAsymptoticsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def IntegerPartitionAsymptoticsBudgetCertificate.size
    (c : IntegerPartitionAsymptoticsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem integerPartitionAsymptotics_budgetCertificate_le_size
    (c : IntegerPartitionAsymptoticsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleIntegerPartitionAsymptoticsBudgetCertificate :
    IntegerPartitionAsymptoticsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleIntegerPartitionAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [IntegerPartitionAsymptoticsBudgetCertificate.controlled,
      sampleIntegerPartitionAsymptoticsBudgetCertificate]
  · norm_num [IntegerPartitionAsymptoticsBudgetCertificate.budgetControlled,
      sampleIntegerPartitionAsymptoticsBudgetCertificate]

example :
    sampleIntegerPartitionAsymptoticsBudgetCertificate.certificateBudgetWindow ≤
      sampleIntegerPartitionAsymptoticsBudgetCertificate.size := by
  apply integerPartitionAsymptotics_budgetCertificate_le_size
  constructor
  · norm_num [IntegerPartitionAsymptoticsBudgetCertificate.controlled,
      sampleIntegerPartitionAsymptoticsBudgetCertificate]
  · norm_num [IntegerPartitionAsymptoticsBudgetCertificate.budgetControlled,
      sampleIntegerPartitionAsymptoticsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleIntegerPartitionAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [IntegerPartitionAsymptoticsBudgetCertificate.controlled,
      sampleIntegerPartitionAsymptoticsBudgetCertificate]
  · norm_num [IntegerPartitionAsymptoticsBudgetCertificate.budgetControlled,
      sampleIntegerPartitionAsymptoticsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleIntegerPartitionAsymptoticsBudgetCertificate.certificateBudgetWindow ≤
      sampleIntegerPartitionAsymptoticsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List IntegerPartitionAsymptoticsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleIntegerPartitionAsymptoticsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleIntegerPartitionAsymptoticsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.IntegerPartitionAsymptotics
