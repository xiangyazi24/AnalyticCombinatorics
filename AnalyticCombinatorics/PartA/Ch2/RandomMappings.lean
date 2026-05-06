import Mathlib.Tactic

namespace AnalyticCombinatorics.PartA.Ch2.RandomMappings

open Finset

set_option linter.style.nativeDecide false


/-- Number of all mappings `[n] → [n]`.  The value at `n = 0` is the usual
empty-function convention `0^0 = 1`. -/
def mappingCount (n : ℕ) : ℕ :=
  n ^ n

/-- Number of idempotent mappings on `[n]`.

Choose the `k` fixed points in the image, then send each of the remaining
`n-k` elements to one of those fixed points. -/
def idempotentCount (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), Nat.choose n k * k ^ (n - k)

/-- Cayley's labelled rooted tree count, with the empty size normalized to `1`
for a total counting sequence. -/
def labeledRootedTreeCount (n : ℕ) : ℕ :=
  if n = 0 then 1 else n ^ (n - 1)

/-- Cayley's labelled unrooted tree count, with both exceptional small sizes
normalized to `1`. -/
def labeledTreeCount (n : ℕ) : ℕ :=
  if n ≤ 1 then 1 else n ^ (n - 2)

theorem mappingCount_zero : mappingCount 0 = 1 := by
  native_decide

theorem mappingCount_one : mappingCount 1 = 1 := by
  native_decide

theorem mappingCount_two : mappingCount 2 = 4 := by
  native_decide

theorem mappingCount_three : mappingCount 3 = 27 := by
  native_decide

theorem mappingCount_four : mappingCount 4 = 256 := by
  native_decide

theorem idempotentCount_zero : idempotentCount 0 = 1 := by
  native_decide

theorem idempotentCount_one : idempotentCount 1 = 1 := by
  native_decide

theorem idempotentCount_two : idempotentCount 2 = 3 := by
  native_decide

theorem idempotentCount_three : idempotentCount 3 = 10 := by
  native_decide

theorem idempotentCount_four : idempotentCount 4 = 41 := by
  native_decide

theorem idempotentCount_five : idempotentCount 5 = 196 := by
  native_decide

theorem idempotentCount_six : idempotentCount 6 = 1057 := by
  native_decide

theorem labeledTreeCount_one : labeledTreeCount 1 = 1 := by
  native_decide

theorem labeledTreeCount_three : labeledTreeCount 3 = 3 := by
  native_decide

theorem labeledTreeCount_four : labeledTreeCount 4 = 16 := by
  native_decide

theorem labeledTreeCount_five : labeledTreeCount 5 = 125 := by
  native_decide

theorem labeledTreeCount_six : labeledTreeCount 6 = 1296 := by
  native_decide

theorem labeledRootedTreeCount_one : labeledRootedTreeCount 1 = 1 := by
  native_decide

theorem labeledRootedTreeCount_two : labeledRootedTreeCount 2 = 2 := by
  native_decide

theorem labeledRootedTreeCount_three : labeledRootedTreeCount 3 = 9 := by
  native_decide

theorem labeledRootedTreeCount_four : labeledRootedTreeCount 4 = 64 := by
  native_decide

theorem labeledRootedTreeCount_five : labeledRootedTreeCount 5 = 625 := by
  native_decide

/-- For `n ≥ 2`, rooting an unrooted labelled tree at one of its vertices gives
the labelled rooted tree count. -/
theorem labeledRootedTreeCount_eq_mul_labeledTreeCount (n : ℕ) (hn : 2 ≤ n) :
    labeledRootedTreeCount n = n * labeledTreeCount n := by
  rw [labeledRootedTreeCount, labeledTreeCount]
  simp only [if_neg (by omega : ¬n = 0), if_neg (by omega : ¬n ≤ 1)]
  have hsub : n - 1 = n - 2 + 1 := by
    omega
  rw [hsub, pow_succ, mul_comm]



structure RandomMappingsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomMappingsBudgetCertificate.controlled
    (c : RandomMappingsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RandomMappingsBudgetCertificate.budgetControlled
    (c : RandomMappingsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RandomMappingsBudgetCertificate.Ready
    (c : RandomMappingsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomMappingsBudgetCertificate.size
    (c : RandomMappingsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem randomMappings_budgetCertificate_le_size
    (c : RandomMappingsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomMappingsBudgetCertificate :
    RandomMappingsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleRandomMappingsBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomMappingsBudgetCertificate.controlled,
      sampleRandomMappingsBudgetCertificate]
  · norm_num [RandomMappingsBudgetCertificate.budgetControlled,
      sampleRandomMappingsBudgetCertificate]

example :
    sampleRandomMappingsBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomMappingsBudgetCertificate.size := by
  apply randomMappings_budgetCertificate_le_size
  constructor
  · norm_num [RandomMappingsBudgetCertificate.controlled,
      sampleRandomMappingsBudgetCertificate]
  · norm_num [RandomMappingsBudgetCertificate.budgetControlled,
      sampleRandomMappingsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleRandomMappingsBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomMappingsBudgetCertificate.controlled,
      sampleRandomMappingsBudgetCertificate]
  · norm_num [RandomMappingsBudgetCertificate.budgetControlled,
      sampleRandomMappingsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomMappingsBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomMappingsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List RandomMappingsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomMappingsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleRandomMappingsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.RandomMappings
