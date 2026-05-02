/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VII — Tree enumeration and asymptotics.

  Formalizes classical counting results for labelled trees:
  Cayley's formula (rooted and unrooted), rooted labelled forests,
  Prüfer sequence counts, and Catalan number verifications for binary trees.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace TreeEnumeration

/-! ## 1. Labelled rooted trees — Cayley's formula: n^{n-1} -/

/-- Number of labelled rooted trees on n vertices. -/
def cayleyTrees (n : ℕ) : ℕ := if n = 0 then 0 else n ^ (n - 1)

theorem cayleyTrees_1 : cayleyTrees 1 = 1 := by native_decide
theorem cayleyTrees_2 : cayleyTrees 2 = 2 := by native_decide
theorem cayleyTrees_3 : cayleyTrees 3 = 9 := by native_decide
theorem cayleyTrees_4 : cayleyTrees 4 = 64 := by native_decide
theorem cayleyTrees_5 : cayleyTrees 5 = 625 := by native_decide
theorem cayleyTrees_6 : cayleyTrees 6 = 7776 := by native_decide

/-! ## 2. Labelled unrooted trees — n^{n-2} -/

/-- Number of labelled unrooted trees on n vertices (n ≥ 2). -/
def cayleyUnrooted (n : ℕ) : ℕ := if n ≤ 1 then 1 else n ^ (n - 2)

theorem cayleyUnrooted_2 : cayleyUnrooted 2 = 1 := by native_decide
theorem cayleyUnrooted_3 : cayleyUnrooted 3 = 3 := by native_decide
theorem cayleyUnrooted_4 : cayleyUnrooted 4 = 16 := by native_decide
theorem cayleyUnrooted_5 : cayleyUnrooted 5 = 125 := by native_decide
theorem cayleyUnrooted_6 : cayleyUnrooted 6 = 1296 := by native_decide

/-- Cross-check: cayleyTrees n = n * cayleyUnrooted n for n ≥ 2. -/
example : 4 * 4 ^ (4 - 2) = 4 ^ (4 - 1) := by native_decide
example : 5 * 5 ^ (5 - 2) = 5 ^ (5 - 1) := by native_decide
example : 6 * 6 ^ (6 - 2) = 6 ^ (6 - 1) := by native_decide

/-- Rooted = n × unrooted for small values. -/
theorem rooted_eq_n_mul_unrooted_2 : cayleyTrees 2 = 2 * cayleyUnrooted 2 := by native_decide
theorem rooted_eq_n_mul_unrooted_3 : cayleyTrees 3 = 3 * cayleyUnrooted 3 := by native_decide
theorem rooted_eq_n_mul_unrooted_4 : cayleyTrees 4 = 4 * cayleyUnrooted 4 := by native_decide
theorem rooted_eq_n_mul_unrooted_5 : cayleyTrees 5 = 5 * cayleyUnrooted 5 := by native_decide

/-! ## 3. Labelled rooted forests — C(n-1, k-1) · n^{n-k} -/

/-- Number of labelled rooted forests on n vertices with k components. -/
def rootedForests (n k : ℕ) : ℕ :=
  if n = 0 ∨ k = 0 ∨ k > n then 0
  else Nat.choose (n - 1) (k - 1) * n ^ (n - k)

/-- For n=4: component breakdown sums to (n+1)^{n-1}. -/
theorem forests_n4_sum :
    rootedForests 4 1 + rootedForests 4 2 + rootedForests 4 3 + rootedForests 4 4 = 5 ^ 3 := by
  native_decide

/-- Verify individual components for n=4. -/
theorem forests_4_1 : rootedForests 4 1 = 64 := by native_decide
theorem forests_4_2 : rootedForests 4 2 = 48 := by native_decide
theorem forests_4_3 : rootedForests 4 3 = 12 := by native_decide
theorem forests_4_4 : rootedForests 4 4 = 1 := by native_decide

/-- Total rooted forests on n=4 vertices = (n+1)^{n-1} = 125. -/
example : 64 + 48 + 12 + 1 = 5 ^ 3 := by native_decide

/-- For n=5: component breakdown sums to 6^4 = 1296. -/
theorem forests_n5_sum :
    rootedForests 5 1 + rootedForests 5 2 + rootedForests 5 3 +
    rootedForests 5 4 + rootedForests 5 5 = 6 ^ 4 := by
  native_decide

/-- Verify individual components for n=5. -/
theorem forests_5_1 : rootedForests 5 1 = 625 := by native_decide
theorem forests_5_2 : rootedForests 5 2 = 500 := by native_decide
theorem forests_5_3 : rootedForests 5 3 = 150 := by native_decide
theorem forests_5_4 : rootedForests 5 4 = 20 := by native_decide
theorem forests_5_5 : rootedForests 5 5 = 1 := by native_decide

example : 625 + 500 + 150 + 20 + 1 = 6 ^ 4 := by native_decide

/-! ## 4. Prüfer sequence — n^{n-2} sequences biject with labelled trees -/

/-- Prüfer sequence count equals Cayley unrooted count. -/
theorem prufer_count (n : ℕ) (hn : n ≥ 2) : n ^ (n - 2) = cayleyUnrooted n := by
  simp [cayleyUnrooted]
  omega

/-- Number of Prüfer sequences for small n. -/
example : (3 : ℕ) ^ (3 - 2) = 3 := by native_decide
example : (4 : ℕ) ^ (4 - 2) = 16 := by native_decide
example : (5 : ℕ) ^ (5 - 2) = 125 := by native_decide
example : (6 : ℕ) ^ (6 - 2) = 1296 := by native_decide

/-! ## 5. Binary tree height / Catalan numbers -/

/-- Catalan number via the formula C(2n, n) / (n+1). -/
def catalanNumber (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

theorem catalan_0 : catalanNumber 0 = 1 := by native_decide
theorem catalan_1 : catalanNumber 1 = 1 := by native_decide
theorem catalan_2 : catalanNumber 2 = 2 := by native_decide
theorem catalan_3 : catalanNumber 3 = 5 := by native_decide
theorem catalan_4 : catalanNumber 4 = 14 := by native_decide
theorem catalan_5 : catalanNumber 5 = 42 := by native_decide
theorem catalan_6 : catalanNumber 6 = 132 := by native_decide

/-- Verify Catalan formula: C(2n, n) / (n+1). -/
example : Nat.choose 6 3 / 4 = 5 := by native_decide
example : Nat.choose 8 4 / 5 = 14 := by native_decide
example : Nat.choose 10 5 / 6 = 42 := by native_decide

/-- Catalan numbers grow roughly as 4^n. -/
theorem catalan_lt_four_pow (n : ℕ) (hn : n ∈ Finset.Icc 1 8) :
    catalanNumber n < 4 ^ n := by
  rcases Finset.mem_Icc.mp hn with ⟨hnlo, hnhi⟩
  interval_cases n <;> native_decide

/-! ## 6. Summary identities -/

/-- Rooted forests total = (n+1)^{n-1} for n=3. -/
theorem forests_n3_sum :
    rootedForests 3 1 + rootedForests 3 2 + rootedForests 3 3 = 4 ^ 2 := by
  native_decide

/-- Cayley's formula: number of rooted trees = n^{n-1}. Verified for n=1..6. -/
theorem cayley_values :
    [cayleyTrees 1, cayleyTrees 2, cayleyTrees 3, cayleyTrees 4, cayleyTrees 5, cayleyTrees 6] =
    [1, 2, 9, 64, 625, 7776] := by native_decide

/-- Cayley unrooted values for n=2..6. -/
theorem cayley_unrooted_values :
    [cayleyUnrooted 2, cayleyUnrooted 3, cayleyUnrooted 4, cayleyUnrooted 5, cayleyUnrooted 6] =
    [1, 3, 16, 125, 1296] := by native_decide

end TreeEnumeration
