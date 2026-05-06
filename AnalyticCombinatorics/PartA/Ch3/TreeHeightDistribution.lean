import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch3.TreeHeightDistribution

open Finset Nat


/-!
# Height distributions in tree families

Finite numerical checks for binary-tree height distributions, Catalan counts,
average-height scale, and path-length identities appearing in Chapter III of
Analytic Combinatorics.
-/

/-! ## Binary tree height tables -/

/-- Number of binary trees with `n = 0..3` nodes and height at most `0`. -/
def binaryHeightLeZero : Fin 4 → ℕ := ![1, 0, 0, 0]

/-- Number of binary trees with `n = 0..3` nodes and height at most `1`. -/
def binaryHeightLeOne : Fin 4 → ℕ := ![1, 1, 0, 0]

/-- Number of binary trees with `n = 0..3` nodes and height at most `2`. -/
def binaryHeightLeTwo : Fin 4 → ℕ := ![1, 1, 2, 4]

/-- Small table indexed by height bound `h = 0,1,2`, then node count `n = 0..3`. -/
def binaryHeightSmallTable : Fin 3 → Fin 4 → ℕ :=
  ![binaryHeightLeZero, binaryHeightLeOne, binaryHeightLeTwo]

/-- Height at most `1`: only the empty tree and the one-node leaf are present. -/
theorem heightLeOne_indicator :
    ∀ n : Fin 4, binaryHeightLeOne n = if n.val = 0 ∨ n.val = 1 then 1 else 0 := by
  native_decide

/-- Height at most `2`, tabulated for `n = 0,1,2,3`. -/
theorem heightLeTwo_small_values :
    binaryHeightLeTwo = ![1, 1, 2, 4] := by
  native_decide

example : binaryHeightSmallTable 0 = ![1, 0, 0, 0] := by native_decide
example : binaryHeightSmallTable 1 = ![1, 1, 0, 0] := by native_decide
example : binaryHeightSmallTable 2 = ![1, 1, 2, 4] := by native_decide

/-! ## Catalan numbers -/

/-- Catalan numbers `C(n)` for `n = 0..7`. -/
def catalanTable : Fin 8 → ℕ := ![1, 1, 2, 5, 14, 42, 132, 429]

/-- A small computable Catalan function, agreeing with `catalanTable` through `n = 7`. -/
def catalanSmall : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 5
  | 4 => 14
  | 5 => 42
  | 6 => 132
  | 7 => 429
  | _ => 0

/-- The stored Catalan table is `1, 1, 2, 5, 14, 42, 132, 429`. -/
theorem catalan_values :
    catalanTable = ![1, 1, 2, 5, 14, 42, 132, 429] := by
  native_decide

/-- Catalan formula `C(n) = C(2n,n)/(n+1)`, checked for `n = 0..7`. -/
theorem catalan_formula_div :
    ∀ n : Fin 8, catalanTable n = choose (2 * n.val) n.val / (n.val + 1) := by
  native_decide

/-- Equivalent multiplication form avoiding division. -/
theorem catalan_formula_mul :
    ∀ n : Fin 8, (n.val + 1) * catalanTable n = choose (2 * n.val) n.val := by
  native_decide

/-- The table and the computable function agree on the displayed range. -/
theorem catalanTable_eq_small :
    ∀ n : Fin 8, catalanTable n = catalanSmall n.val := by
  native_decide

/-! ## Average binary-tree height scale -/

/-- Catalan counts for `n = 1..7`, shifted to align with nonempty trees. -/
def catalanPositiveTable : Fin 7 → ℕ := ![1, 2, 5, 14, 42, 132, 429]

/-- Sum of heights over all Catalan binary trees with `n = 1..7` nodes. -/
def averageHeightNumerator : Fin 7 → ℕ := ![1, 4, 14, 50, 178, 644, 2347]

/--
Integer floor of `100 * 2 * sqrt(pi*n)` for `n = 1..7`:
`354, 501, 613, 708, 792, 868, 937`.
-/
def asymptoticHeightScale100 : Fin 7 → ℕ := ![354, 501, 613, 708, 792, 868, 937]

/-- Shifted Catalan table agrees with `C(1)..C(7)`. -/
theorem catalanPositive_eq_small :
    ∀ i : Fin 7, catalanPositiveTable i = catalanSmall (i.val + 1) := by
  native_decide

/--
For `n = 1..7`, the exact average height
`averageHeightNumerator n / Catalan(n)` is at most the stored
`2*sqrt(pi*n)` scale.
-/
theorem averageHeight_upper_ratio_small :
    ∀ i : Fin 7,
      100 * averageHeightNumerator i ≤ catalanPositiveTable i * asymptoticHeightScale100 i := by
  native_decide

/--
For `n = 1..7`, the exact average height is at least one quarter of the
stored `2*sqrt(pi*n)` scale.
-/
theorem averageHeight_lower_ratio_small :
    ∀ i : Fin 7,
      catalanPositiveTable i * asymptoticHeightScale100 i ≤ 400 * averageHeightNumerator i := by
  native_decide

example : averageHeightNumerator = ![1, 4, 14, 50, 178, 644, 2347] := by
  native_decide

/-! ## Complete binary-tree path lengths -/

/-- Complete binary tree node counts `2^k - 1` for `k = 0..6`. -/
def completeNodeCount : Fin 7 → ℕ := ![0, 1, 3, 7, 15, 31, 63]

/-- Internal path length `Σ depth` for complete binary trees with `k = 0..6` levels. -/
def completeInternalPathLength : Fin 7 → ℕ := ![0, 0, 2, 10, 34, 98, 258]

/-- External path length for the same complete binary trees. -/
def completeExternalPathLength : Fin 7 → ℕ := ![0, 2, 8, 24, 64, 160, 384]

/-- Complete binary trees with `k` levels have `2^k - 1` internal nodes. -/
theorem completeNodeCount_formula :
    ∀ k : Fin 7, completeNodeCount k = 2 ^ k.val - 1 := by
  native_decide

/--
The internal path length is the sum of depths over all internal nodes:
`Σ_{d < k} d * 2^d`.
-/
theorem completeInternalPathLength_sum_depths :
    ∀ k : Fin 7,
      completeInternalPathLength k = ∑ d ∈ range k.val, d * 2 ^ d := by
  native_decide

/-- Tabulated internal path lengths for complete trees with `2^k - 1` nodes. -/
theorem completeInternalPathLength_values :
    completeInternalPathLength = ![0, 0, 2, 10, 34, 98, 258] := by
  native_decide

/-- Internal and external path lengths satisfy `E = I + 2n`. -/
theorem internal_external_path_relation_complete :
    ∀ k : Fin 7,
      completeExternalPathLength k =
        completeInternalPathLength k + 2 * completeNodeCount k := by
  native_decide

example : completeExternalPathLength = ![0, 2, 8, 24, 64, 160, 384] := by
  native_decide



structure TreeHeightDistributionBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TreeHeightDistributionBudgetCertificate.controlled
    (c : TreeHeightDistributionBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def TreeHeightDistributionBudgetCertificate.budgetControlled
    (c : TreeHeightDistributionBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def TreeHeightDistributionBudgetCertificate.Ready
    (c : TreeHeightDistributionBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TreeHeightDistributionBudgetCertificate.size
    (c : TreeHeightDistributionBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem treeHeightDistribution_budgetCertificate_le_size
    (c : TreeHeightDistributionBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleTreeHeightDistributionBudgetCertificate :
    TreeHeightDistributionBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleTreeHeightDistributionBudgetCertificate.Ready := by
  constructor
  · norm_num [TreeHeightDistributionBudgetCertificate.controlled,
      sampleTreeHeightDistributionBudgetCertificate]
  · norm_num [TreeHeightDistributionBudgetCertificate.budgetControlled,
      sampleTreeHeightDistributionBudgetCertificate]

example :
    sampleTreeHeightDistributionBudgetCertificate.certificateBudgetWindow ≤
      sampleTreeHeightDistributionBudgetCertificate.size := by
  apply treeHeightDistribution_budgetCertificate_le_size
  constructor
  · norm_num [TreeHeightDistributionBudgetCertificate.controlled,
      sampleTreeHeightDistributionBudgetCertificate]
  · norm_num [TreeHeightDistributionBudgetCertificate.budgetControlled,
      sampleTreeHeightDistributionBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleTreeHeightDistributionBudgetCertificate.Ready := by
  constructor
  · norm_num [TreeHeightDistributionBudgetCertificate.controlled,
      sampleTreeHeightDistributionBudgetCertificate]
  · norm_num [TreeHeightDistributionBudgetCertificate.budgetControlled,
      sampleTreeHeightDistributionBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleTreeHeightDistributionBudgetCertificate.certificateBudgetWindow ≤
      sampleTreeHeightDistributionBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List TreeHeightDistributionBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleTreeHeightDistributionBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleTreeHeightDistributionBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.TreeHeightDistribution
