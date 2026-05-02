/-
  Analytic Combinatorics — Part B
  Chapter V — Digital Trees

  Formalized numerical checks for binary tries, Patricia tries,
  BST depth bounds, and radix vs comparison sort work.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace DigitalTrees

/-! ## 1. Binary trie leaf count at depth d -/

/-- A complete binary trie of depth d has 2^d leaves. -/
def trieLeaves (d : ℕ) : ℕ := 2 ^ d

/-- A complete binary trie of depth d has 2^d - 1 internal nodes. -/
def trieInternalNodes (d : ℕ) : ℕ := 2 ^ d - 1

example : trieLeaves 3 = 8 := by native_decide
example : trieInternalNodes 3 = 7 := by native_decide
example : trieLeaves 5 = 32 := by native_decide
example : trieInternalNodes 5 = 31 := by native_decide

/-! ## 2. Integer logarithm (search depth) -/

example : Nat.log 2 1 = 0 := by native_decide
example : Nat.log 2 2 = 1 := by native_decide
example : Nat.log 2 4 = 2 := by native_decide
example : Nat.log 2 8 = 3 := by native_decide
example : Nat.log 2 16 = 4 := by native_decide
example : Nat.log 2 1024 = 10 := by native_decide

/-! ## 3. Patricia trie internal nodes (n keys → n-1 internal) -/

/-- A Patricia trie with n keys has n-1 internal nodes (for n ≥ 2). -/
def patriciaPaths (n : ℕ) : ℕ := if n ≤ 1 then 0 else n - 1

example : patriciaPaths 1 = 0 := by native_decide
example : patriciaPaths 2 = 1 := by native_decide
example : patriciaPaths 3 = 2 := by native_decide
example : patriciaPaths 4 = 3 := by native_decide
example : patriciaPaths 5 = 4 := by native_decide
example : patriciaPaths 6 = 5 := by native_decide
example : patriciaPaths 7 = 6 := by native_decide
example : patriciaPaths 8 = 7 := by native_decide
example : patriciaPaths 9 = 8 := by native_decide
example : patriciaPaths 10 = 9 := by native_decide

/-! ## 4. BST average depth bounds -/

/-- Floor bound on average BST depth: 2 * ⌊log₂ n⌋. -/
def bstDepthBound (n : ℕ) : ℕ := 2 * Nat.log 2 n

example : bstDepthBound 8 = 6 := by native_decide
example : bstDepthBound 16 = 8 := by native_decide
example : bstDepthBound 1024 = 20 := by native_decide

/-! ## 5. Radix sort vs comparison sort -/

/-- Radix sort work: n strings of length b costs n * b. -/
def radixWork (n b : ℕ) : ℕ := n * b

/-- Comparison sort work (floor): n * ⌊log₂ n⌋. -/
def compSortWork (n : ℕ) : ℕ := n * Nat.log 2 n

example : radixWork 1000 10 = 10000 := by native_decide
example : compSortWork 1024 = 10240 := by native_decide

/-- When b < log₂ n, radix sort wins. -/
example : radixWork 1024 5 < compSortWork 1024 := by native_decide

end DigitalTrees
