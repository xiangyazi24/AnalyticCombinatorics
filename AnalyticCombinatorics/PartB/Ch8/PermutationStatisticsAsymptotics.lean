import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch8.PermutationStatisticsAsymptotics


/-!
# Permutation Statistics Asymptotics

Finite computational certificates for Chapter VIII style saddle-point
analysis of permutation statistics.  The tables record unsigned Stirling
numbers of the first kind, counting permutations of `[n]` by number of cycles,
and the corresponding small involution numbers.
-/

/-! ## Unsigned Stirling numbers of the first kind -/

/-- `|s(n,k)|`, the number of permutations of `[n]` with exactly `k` cycles. -/
def unsignedStirlingFirstKind : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 =>
      n * unsignedStirlingFirstKind n (k + 1) + unsignedStirlingFirstKind n k

/-- The permutation statistic counted by cycles is `|s(n,k)|`. -/
def permutationsWithKCycles (n k : Nat) : Nat :=
  unsignedStirlingFirstKind n k

/-- Naming check: permutations of `[n]` with `k` cycles are counted by `|s(n,k)|`. -/
theorem permutationsWithKCycles_eq_unsignedStirling_0_to_6 :
    ∀ n : Fin 7, ∀ k : Fin 7,
      permutationsWithKCycles (n : Nat) (k : Nat) =
        unsignedStirlingFirstKind (n : Nat) (k : Nat) := by
  native_decide

/-- Row `n = 1`: `|s(1,k)|`, `k = 1`. -/
def unsignedStirlingRow1 : Fin 1 → Nat := ![1]

/-- Row `n = 2`: `|s(2,k)|`, `k = 1..2`. -/
def unsignedStirlingRow2 : Fin 2 → Nat := ![1, 1]

/-- Row `n = 3`: `|s(3,k)|`, `k = 1..3`. -/
def unsignedStirlingRow3 : Fin 3 → Nat := ![2, 3, 1]

/-- Row `n = 4`: `|s(4,k)|`, `k = 1..4`. -/
def unsignedStirlingRow4 : Fin 4 → Nat := ![6, 11, 6, 1]

/-- Row `n = 5`: `|s(5,k)|`, `k = 1..5`. -/
def unsignedStirlingRow5 : Fin 5 → Nat := ![24, 50, 35, 10, 1]

/-- Row `n = 6`: `|s(6,k)|`, `k = 1..6`. -/
def unsignedStirlingRow6 : Fin 6 → Nat := ![120, 274, 225, 85, 15, 1]

/-- Upper triangular table of `|s(n,k)|` for `n = 1..6`, `k = 1..n`. -/
theorem unsignedStirlingTable_values :
    unsignedStirlingRow1 = ![1] ∧
    unsignedStirlingRow2 = ![1, 1] ∧
    unsignedStirlingRow3 = ![2, 3, 1] ∧
    unsignedStirlingRow4 = ![6, 11, 6, 1] ∧
    unsignedStirlingRow5 = ![24, 50, 35, 10, 1] ∧
    unsignedStirlingRow6 = ![120, 274, 225, 85, 15, 1] := by
  native_decide

/-- The tabulated rows agree with the recursive definition of `|s(n,k)|`. -/
theorem unsignedStirlingRows_match_definition :
    unsignedStirlingRow1 0 = unsignedStirlingFirstKind 1 1 ∧
    unsignedStirlingRow2 0 = unsignedStirlingFirstKind 2 1 ∧
    unsignedStirlingRow2 1 = unsignedStirlingFirstKind 2 2 ∧
    unsignedStirlingRow3 0 = unsignedStirlingFirstKind 3 1 ∧
    unsignedStirlingRow3 1 = unsignedStirlingFirstKind 3 2 ∧
    unsignedStirlingRow3 2 = unsignedStirlingFirstKind 3 3 ∧
    unsignedStirlingRow4 0 = unsignedStirlingFirstKind 4 1 ∧
    unsignedStirlingRow4 1 = unsignedStirlingFirstKind 4 2 ∧
    unsignedStirlingRow4 2 = unsignedStirlingFirstKind 4 3 ∧
    unsignedStirlingRow4 3 = unsignedStirlingFirstKind 4 4 ∧
    unsignedStirlingRow5 0 = unsignedStirlingFirstKind 5 1 ∧
    unsignedStirlingRow5 1 = unsignedStirlingFirstKind 5 2 ∧
    unsignedStirlingRow5 2 = unsignedStirlingFirstKind 5 3 ∧
    unsignedStirlingRow5 3 = unsignedStirlingFirstKind 5 4 ∧
    unsignedStirlingRow5 4 = unsignedStirlingFirstKind 5 5 ∧
    unsignedStirlingRow6 0 = unsignedStirlingFirstKind 6 1 ∧
    unsignedStirlingRow6 1 = unsignedStirlingFirstKind 6 2 ∧
    unsignedStirlingRow6 2 = unsignedStirlingFirstKind 6 3 ∧
    unsignedStirlingRow6 3 = unsignedStirlingFirstKind 6 4 ∧
    unsignedStirlingRow6 4 = unsignedStirlingFirstKind 6 5 ∧
    unsignedStirlingRow6 5 = unsignedStirlingFirstKind 6 6 := by
  native_decide

/-- Row sums: `sum_k |s(n,k)| = n!` for `n = 1..6`. -/
theorem unsignedStirling_row_sums_factorial_1_to_6 :
    unsignedStirlingRow1 0 = Nat.factorial 1 ∧
    unsignedStirlingRow2 0 + unsignedStirlingRow2 1 = Nat.factorial 2 ∧
    unsignedStirlingRow3 0 + unsignedStirlingRow3 1 + unsignedStirlingRow3 2 =
      Nat.factorial 3 ∧
    unsignedStirlingRow4 0 + unsignedStirlingRow4 1 + unsignedStirlingRow4 2 +
        unsignedStirlingRow4 3 =
      Nat.factorial 4 ∧
    unsignedStirlingRow5 0 + unsignedStirlingRow5 1 + unsignedStirlingRow5 2 +
        unsignedStirlingRow5 3 + unsignedStirlingRow5 4 =
      Nat.factorial 5 ∧
    unsignedStirlingRow6 0 + unsignedStirlingRow6 1 + unsignedStirlingRow6 2 +
        unsignedStirlingRow6 3 + unsignedStirlingRow6 4 + unsignedStirlingRow6 5 =
      Nat.factorial 6 := by
  native_decide

/-- Single-cycle permutations: `|s(n,1)| = (n-1)!` for `n = 1..6`. -/
theorem unsignedStirling_single_cycle_factorial_1_to_6 :
    unsignedStirlingFirstKind 1 1 = Nat.factorial 0 ∧
    unsignedStirlingFirstKind 2 1 = Nat.factorial 1 ∧
    unsignedStirlingFirstKind 3 1 = Nat.factorial 2 ∧
    unsignedStirlingFirstKind 4 1 = Nat.factorial 3 ∧
    unsignedStirlingFirstKind 5 1 = Nat.factorial 4 ∧
    unsignedStirlingFirstKind 6 1 = Nat.factorial 5 := by
  native_decide

/-- Identity permutation: `|s(n,n)| = 1` for `n = 1..6`. -/
theorem unsignedStirling_identity_1_to_6 :
    unsignedStirlingFirstKind 1 1 = 1 ∧
    unsignedStirlingFirstKind 2 2 = 1 ∧
    unsignedStirlingFirstKind 3 3 = 1 ∧
    unsignedStirlingFirstKind 4 4 = 1 ∧
    unsignedStirlingFirstKind 5 5 = 1 ∧
    unsignedStirlingFirstKind 6 6 = 1 := by
  native_decide

/-- One transposition and all other points fixed: `|s(n,n-1)| = C(n,2)`. -/
theorem unsignedStirling_one_two_cycle_2_to_6 :
    unsignedStirlingFirstKind 2 1 = Nat.choose 2 2 ∧
    unsignedStirlingFirstKind 3 2 = Nat.choose 3 2 ∧
    unsignedStirlingFirstKind 4 3 = Nat.choose 4 2 ∧
    unsignedStirlingFirstKind 5 4 = Nat.choose 5 2 ∧
    unsignedStirlingFirstKind 6 5 = Nat.choose 6 2 := by
  native_decide

/-- Recurrence: `|s(n+1,k)| = n * |s(n,k)| + |s(n,k-1)|`, checked on the table range. -/
theorem unsignedStirling_recurrence_0_to_6 :
    ∀ n : Fin 6, ∀ k : Fin 6,
      unsignedStirlingFirstKind ((n : Nat) + 1) ((k : Nat) + 1) =
        (n : Nat) * unsignedStirlingFirstKind (n : Nat) ((k : Nat) + 1) +
          unsignedStirlingFirstKind (n : Nat) (k : Nat) := by
  native_decide

/-! ## Involutions -/

/-- Number of involutions on an `n`-element set. -/
def involutionNumber : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n + 2 => involutionNumber (n + 1) + (n + 1) * involutionNumber n

/-- Involution numbers `I(n)` for `n = 0..6`. -/
def involutionTable : Fin 7 → Nat := ![1, 1, 2, 4, 10, 26, 76]

/-- Values `I(0)..I(6)`. -/
theorem involutionTable_values :
    involutionTable = ![1, 1, 2, 4, 10, 26, 76] := by
  native_decide

/-- The involution table agrees with the recurrence definition. -/
theorem involutionTable_matches_definition :
    involutionTable 0 = involutionNumber 0 ∧
    involutionTable 1 = involutionNumber 1 ∧
    involutionTable 2 = involutionNumber 2 ∧
    involutionTable 3 = involutionNumber 3 ∧
    involutionTable 4 = involutionNumber 4 ∧
    involutionTable 5 = involutionNumber 5 ∧
    involutionTable 6 = involutionNumber 6 := by
  native_decide

/-- Recurrence: `I(n) = I(n-1) + (n-1) * I(n-2)` for `n = 2..6`. -/
theorem involution_recurrence_2_to_6 :
    ∀ i : Fin 5,
      involutionNumber ((i : Nat) + 2) =
        involutionNumber ((i : Nat) + 1) + ((i : Nat) + 1) * involutionNumber (i : Nat) := by
  native_decide



structure PermutationStatisticsAsymptoticsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PermutationStatisticsAsymptoticsBudgetCertificate.controlled
    (c : PermutationStatisticsAsymptoticsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PermutationStatisticsAsymptoticsBudgetCertificate.budgetControlled
    (c : PermutationStatisticsAsymptoticsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PermutationStatisticsAsymptoticsBudgetCertificate.Ready
    (c : PermutationStatisticsAsymptoticsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PermutationStatisticsAsymptoticsBudgetCertificate.size
    (c : PermutationStatisticsAsymptoticsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem permutationStatisticsAsymptotics_budgetCertificate_le_size
    (c : PermutationStatisticsAsymptoticsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePermutationStatisticsAsymptoticsBudgetCertificate :
    PermutationStatisticsAsymptoticsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : samplePermutationStatisticsAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [PermutationStatisticsAsymptoticsBudgetCertificate.controlled,
      samplePermutationStatisticsAsymptoticsBudgetCertificate]
  · norm_num [PermutationStatisticsAsymptoticsBudgetCertificate.budgetControlled,
      samplePermutationStatisticsAsymptoticsBudgetCertificate]

example :
    samplePermutationStatisticsAsymptoticsBudgetCertificate.certificateBudgetWindow ≤
      samplePermutationStatisticsAsymptoticsBudgetCertificate.size := by
  apply permutationStatisticsAsymptotics_budgetCertificate_le_size
  constructor
  · norm_num [PermutationStatisticsAsymptoticsBudgetCertificate.controlled,
      samplePermutationStatisticsAsymptoticsBudgetCertificate]
  · norm_num [PermutationStatisticsAsymptoticsBudgetCertificate.budgetControlled,
      samplePermutationStatisticsAsymptoticsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePermutationStatisticsAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [PermutationStatisticsAsymptoticsBudgetCertificate.controlled,
      samplePermutationStatisticsAsymptoticsBudgetCertificate]
  · norm_num [PermutationStatisticsAsymptoticsBudgetCertificate.budgetControlled,
      samplePermutationStatisticsAsymptoticsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePermutationStatisticsAsymptoticsBudgetCertificate.certificateBudgetWindow ≤
      samplePermutationStatisticsAsymptoticsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List PermutationStatisticsAsymptoticsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePermutationStatisticsAsymptoticsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePermutationStatisticsAsymptoticsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.PermutationStatisticsAsymptotics
