import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch2.EGFApplications


open Finset

/-!
# Applications of exponential generating functions

Chapter II of *Analytic Combinatorics* uses labelled constructions and
exponential generating functions to organize families such as labelled trees,
forests, graphs, and permutations decomposed into cycles.  This file records
small numerical checks for those applications.
-/

/-! ## Cayley labelled trees and forests -/

/-- Cayley's formula for labelled rooted trees: `n^(n-1)`. -/
def labelledRootedTrees (n : ℕ) : ℕ := n ^ (n - 1)

/-- Cayley's Prüfer formula for labelled unrooted trees: `n^(n-2)`. -/
def labelledUnrootedTrees (n : ℕ) : ℕ := n ^ (n - 2)

/-- Labelled forests on `n` labelled vertices: `(n+1)^(n-1)`. -/
def labelledForests (n : ℕ) : ℕ := (n + 1) ^ (n - 1)

/-- The rooted Cayley table for `n = 1, ..., 7`. -/
def labelledRootedTreeTable : Fin 7 → ℕ := ![1, 2, 9, 64, 625, 7776, 117649]

/-- The forest table for `n = 1, ..., 6`. -/
def labelledForestTable : Fin 6 → ℕ := ![1, 3, 16, 125, 1296, 16807]

/-- The Prüfer/unrooted Cayley table for `n = 1, ..., 7`. -/
def labelledUnrootedTreeTable : Fin 7 → ℕ := ![1, 1, 3, 16, 125, 1296, 16807]

theorem labelledRootedTreeTable_correct :
    ∀ i : Fin 7, labelledRootedTreeTable i = labelledRootedTrees (i.val + 1) := by
  native_decide

theorem labelledForestTable_correct :
    ∀ i : Fin 6, labelledForestTable i = labelledForests (i.val + 1) := by
  native_decide

theorem labelledUnrootedTreeTable_correct :
    ∀ i : Fin 7, labelledUnrootedTreeTable i = labelledUnrootedTrees (i.val + 1) := by
  native_decide

theorem rootedTrees_one : labelledRootedTrees 1 = 1 := by native_decide
theorem rootedTrees_two : labelledRootedTrees 2 = 2 := by native_decide
theorem rootedTrees_three : labelledRootedTrees 3 = 9 := by native_decide
theorem rootedTrees_four : labelledRootedTrees 4 = 64 := by native_decide
theorem rootedTrees_five : labelledRootedTrees 5 = 625 := by native_decide
theorem rootedTrees_six : labelledRootedTrees 6 = 7776 := by native_decide
theorem rootedTrees_seven : labelledRootedTrees 7 = 117649 := by native_decide

theorem forests_one : labelledForests 1 = 1 := by native_decide
theorem forests_two : labelledForests 2 = 3 := by native_decide
theorem forests_three : labelledForests 3 = 16 := by native_decide
theorem forests_four : labelledForests 4 = 125 := by native_decide
theorem forests_five : labelledForests 5 = 1296 := by native_decide
theorem forests_six : labelledForests 6 = 16807 := by native_decide

theorem unrootedTrees_one : labelledUnrootedTrees 1 = 1 := by native_decide
theorem unrootedTrees_two : labelledUnrootedTrees 2 = 1 := by native_decide
theorem unrootedTrees_three : labelledUnrootedTrees 3 = 3 := by native_decide
theorem unrootedTrees_four : labelledUnrootedTrees 4 = 16 := by native_decide
theorem unrootedTrees_five : labelledUnrootedTrees 5 = 125 := by native_decide
theorem unrootedTrees_six : labelledUnrootedTrees 6 = 1296 := by native_decide
theorem unrootedTrees_seven : labelledUnrootedTrees 7 = 16807 := by native_decide

/-- Prüfer verification: rooting each unrooted labelled tree gives Cayley's rooted count. -/
theorem cayleyViaPrufer_upto_seven :
    ∀ n ∈ Finset.Icc 1 7, n * labelledUnrootedTrees n = labelledRootedTrees n := by
  native_decide

/-! ## Labelled graphs -/

/-- Total labelled graphs on `n` vertices: each possible edge is present or absent. -/
def totalLabelledGraphs (n : ℕ) : ℕ := 2 ^ Nat.choose n 2

/-- Small connected labelled graph counts. -/
def connectedLabelledGraphs : ℕ → ℕ
  | 1 => 1
  | 2 => 1
  | 3 => 4
  | 4 => 38
  | 5 => 728
  | _ => 0

/-- Connected labelled graph counts for `n = 1, ..., 5`. -/
def connectedGraphTable : Fin 5 → ℕ := ![1, 1, 4, 38, 728]

/-- Total labelled graph counts for `n = 1, ..., 6`. -/
def totalGraphTable : Fin 6 → ℕ := ![1, 2, 8, 64, 1024, 32768]

theorem connectedGraphTable_correct :
    ∀ i : Fin 5, connectedGraphTable i = connectedLabelledGraphs (i.val + 1) := by
  native_decide

theorem totalGraphTable_correct :
    ∀ i : Fin 6, totalGraphTable i = totalLabelledGraphs (i.val + 1) := by
  native_decide

theorem connectedGraphs_one : connectedLabelledGraphs 1 = 1 := by native_decide
theorem connectedGraphs_two : connectedLabelledGraphs 2 = 1 := by native_decide
theorem connectedGraphs_three : connectedLabelledGraphs 3 = 4 := by native_decide
theorem connectedGraphs_four : connectedLabelledGraphs 4 = 38 := by native_decide
theorem connectedGraphs_five : connectedLabelledGraphs 5 = 728 := by native_decide

theorem totalGraphs_one : totalLabelledGraphs 1 = 1 := by native_decide
theorem totalGraphs_two : totalLabelledGraphs 2 = 2 := by native_decide
theorem totalGraphs_three : totalLabelledGraphs 3 = 8 := by native_decide
theorem totalGraphs_four : totalLabelledGraphs 4 = 64 := by native_decide
theorem totalGraphs_five : totalLabelledGraphs 5 = 1024 := by native_decide
theorem totalGraphs_six : totalLabelledGraphs 6 = 32768 := by native_decide

/-- From `n = 2` through `n = 5`, the connected/total ratio is nondecreasing. -/
theorem connectedRatio_increases_two_to_five :
    (connectedLabelledGraphs 2 : ℚ) / totalLabelledGraphs 2 ≤
        (connectedLabelledGraphs 3 : ℚ) / totalLabelledGraphs 3 ∧
      (connectedLabelledGraphs 3 : ℚ) / totalLabelledGraphs 3 ≤
        (connectedLabelledGraphs 4 : ℚ) / totalLabelledGraphs 4 ∧
      (connectedLabelledGraphs 4 : ℚ) / totalLabelledGraphs 4 ≤
        (connectedLabelledGraphs 5 : ℚ) / totalLabelledGraphs 5 := by
  native_decide

/-- The checked ratios remain at most `1`, as expected on the way toward `1`. -/
theorem connectedRatio_at_most_one_upto_five :
    ∀ n ∈ Finset.Icc 1 5,
      (connectedLabelledGraphs n : ℚ) / totalLabelledGraphs n ≤ 1 := by
  native_decide

/-- Disconnected labelled graphs on three vertices: empty graph plus one-edge choices. -/
def disconnectedGraphArrangementsThree : ℕ := 1 + Nat.choose 3 2

/-- Exponential-formula check for `n = 3`: connected plus disconnected arrangements. -/
theorem exponentialFormula_graphs_three :
    totalLabelledGraphs 3 =
      connectedLabelledGraphs 3 + disconnectedGraphArrangementsThree := by
  native_decide

/-! ## Permutations as sets of cycles -/

/-- Unsigned Stirling numbers of the first kind, `|s(n,k)|`. -/
def unsignedStirling1 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => n * unsignedStirling1 n (k + 1) + unsignedStirling1 n k

/-- Row sums of `|s(n,k)|` count all permutations, for `n = 0, ..., 7`. -/
theorem cycleSetPartition_permutations_upto_seven :
    ∀ n ∈ Finset.Icc 0 7,
      (∑ k ∈ Finset.range (n + 1), unsignedStirling1 n k) = Nat.factorial n := by
  native_decide

theorem cycleSetPartition_permutations_one :
    (∑ k ∈ Finset.range 2, unsignedStirling1 1 k) = Nat.factorial 1 := by
  native_decide

theorem cycleSetPartition_permutations_two :
    (∑ k ∈ Finset.range 3, unsignedStirling1 2 k) = Nat.factorial 2 := by
  native_decide

theorem cycleSetPartition_permutations_three :
    (∑ k ∈ Finset.range 4, unsignedStirling1 3 k) = Nat.factorial 3 := by
  native_decide

theorem cycleSetPartition_permutations_four :
    (∑ k ∈ Finset.range 5, unsignedStirling1 4 k) = Nat.factorial 4 := by
  native_decide

theorem cycleSetPartition_permutations_five :
    (∑ k ∈ Finset.range 6, unsignedStirling1 5 k) = Nat.factorial 5 := by
  native_decide

theorem cycleSetPartition_permutations_six :
    (∑ k ∈ Finset.range 7, unsignedStirling1 6 k) = Nat.factorial 6 := by
  native_decide

theorem cycleSetPartition_permutations_seven :
    (∑ k ∈ Finset.range 8, unsignedStirling1 7 k) = Nat.factorial 7 := by
  native_decide



structure EGFApplicationsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EGFApplicationsBudgetCertificate.controlled
    (c : EGFApplicationsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def EGFApplicationsBudgetCertificate.budgetControlled
    (c : EGFApplicationsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def EGFApplicationsBudgetCertificate.Ready
    (c : EGFApplicationsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def EGFApplicationsBudgetCertificate.size
    (c : EGFApplicationsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem eGFApplications_budgetCertificate_le_size
    (c : EGFApplicationsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleEGFApplicationsBudgetCertificate :
    EGFApplicationsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleEGFApplicationsBudgetCertificate.Ready := by
  constructor
  · norm_num [EGFApplicationsBudgetCertificate.controlled,
      sampleEGFApplicationsBudgetCertificate]
  · norm_num [EGFApplicationsBudgetCertificate.budgetControlled,
      sampleEGFApplicationsBudgetCertificate]

example :
    sampleEGFApplicationsBudgetCertificate.certificateBudgetWindow ≤
      sampleEGFApplicationsBudgetCertificate.size := by
  apply eGFApplications_budgetCertificate_le_size
  constructor
  · norm_num [EGFApplicationsBudgetCertificate.controlled,
      sampleEGFApplicationsBudgetCertificate]
  · norm_num [EGFApplicationsBudgetCertificate.budgetControlled,
      sampleEGFApplicationsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleEGFApplicationsBudgetCertificate.Ready := by
  constructor
  · norm_num [EGFApplicationsBudgetCertificate.controlled,
      sampleEGFApplicationsBudgetCertificate]
  · norm_num [EGFApplicationsBudgetCertificate.budgetControlled,
      sampleEGFApplicationsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleEGFApplicationsBudgetCertificate.certificateBudgetWindow ≤
      sampleEGFApplicationsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List EGFApplicationsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleEGFApplicationsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleEGFApplicationsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.EGFApplications
