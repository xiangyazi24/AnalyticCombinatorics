import Mathlib.Tactic
set_option linter.style.nativeDecide false
namespace TrieAnalysis

/-!
# Analysis of Tries (Chapter IX, Flajolet–Sedgewick)

Expected internal node counts and path lengths for binary tries built from
n random binary strings. Expectations stored as numerator–denominator pairs
are verified via the fundamental trie recurrence using cross-multiplication
for n = 1, 2, 3, 4.
-/

/-! ## Binary Trie Data Structure -/

inductive BinaryTrie where
  | empty : BinaryTrie
  | leaf : BinaryTrie
  | node : BinaryTrie → BinaryTrie → BinaryTrie
  deriving DecidableEq

def BinaryTrie.internalNodes : BinaryTrie → ℕ
  | .empty => 0
  | .leaf => 0
  | .node l r => 1 + l.internalNodes + r.internalNodes

def BinaryTrie.leaves : BinaryTrie → ℕ
  | .empty => 0
  | .leaf => 1
  | .node l r => l.leaves + r.leaves

def BinaryTrie.depth : BinaryTrie → ℕ
  | .empty => 0
  | .leaf => 0
  | .node l r => 1 + max l.depth r.depth

/-! ## Small Explicit Trie Statistics -/

def trieN0 : BinaryTrie := .empty
def trieN1 : BinaryTrie := .leaf
def trieN2a : BinaryTrie := .node .leaf .leaf
def trieN2b : BinaryTrie := .node (.node .leaf .leaf) .empty
def trieN3 : BinaryTrie := .node .leaf (.node .leaf .leaf)
def trieN4 : BinaryTrie := .node (.node .leaf .leaf) (.node .leaf .leaf)

theorem small_trie_internal_nodes :
    trieN0.internalNodes = 0 ∧ trieN1.internalNodes = 0 ∧
    trieN2a.internalNodes = 1 ∧ trieN2b.internalNodes = 2 ∧
    trieN3.internalNodes = 2 ∧ trieN4.internalNodes = 3 := by native_decide

theorem small_trie_leaves :
    trieN0.leaves = 0 ∧ trieN1.leaves = 1 ∧
    trieN2a.leaves = 2 ∧ trieN3.leaves = 3 ∧ trieN4.leaves = 4 := by native_decide

theorem small_trie_depths :
    trieN2a.depth = 1 ∧ trieN2b.depth = 2 ∧
    trieN3.depth = 2 ∧ trieN4.depth = 2 := by native_decide

/-! ## Expected Internal Nodes E[I_n] -/

/-- Numerator of E[I_n] in lowest terms, for n = 0, ..., 4.
    E[I_0]=0, E[I_1]=0, E[I_2]=2, E[I_3]=10/3, E[I_4]=100/21. -/
def trieNodesNum : Fin 5 → ℕ := ![0, 0, 2, 10, 100]

/-- Denominator of E[I_n] in lowest terms. -/
def trieNodesDen : Fin 5 → ℕ := ![1, 1, 1, 3, 21]
theorem trieNodes_reduced :
    Nat.gcd 2 1 = 1 ∧ Nat.gcd 10 3 = 1 ∧ Nat.gcd 100 21 = 1 := by native_decide

-- Fundamental trie recurrence (F&S Proposition IX.3):
--   (2^n - 2) · E[I_n] = 2^n + 2 · Σ_{k=2}^{n-1} C(n,k) · E[I_k]
-- Verified via integer cross-multiplication to clear all denominators.

theorem trieRecurrence_n2 :
    (2 ^ 2 - 2) * trieNodesNum 2 = trieNodesDen 2 * 2 ^ 2 := by native_decide

theorem trieRecurrence_n3 :
    (2 ^ 3 - 2) * trieNodesNum 3 =
      trieNodesDen 3 * (2 ^ 3 + 2 * Nat.choose 3 2 * trieNodesNum 2) := by native_decide

theorem trieRecurrence_n4 :
    (2 ^ 4 - 2) * trieNodesNum 4 * trieNodesDen 3 =
      trieNodesDen 4 * (2 ^ 4 * trieNodesDen 3 +
        2 * (Nat.choose 4 2 * trieNodesNum 2 * trieNodesDen 3 +
             Nat.choose 4 3 * trieNodesNum 3 * trieNodesDen 2)) := by native_decide
/-! ## Expected Total Path Length P_n -/

/-- Numerator of P_n in lowest terms.
    P_0=0, P_1=0, P_2=4, P_3=8, P_4=88/7. -/
def pathLengthNum : Fin 5 → ℕ := ![0, 0, 4, 8, 88]

/-- Denominator of P_n in lowest terms. -/
def pathLengthDen : Fin 5 → ℕ := ![1, 1, 1, 1, 7]

theorem pathLength_reduced : Nat.gcd 88 7 = 1 := by native_decide

-- (2^n - 2) · P_n = n · 2^n + 2 · Σ_{k=2}^{n-1} C(n,k) · P_k

theorem pathRecurrence_n2 :
    (2 ^ 2 - 2) * pathLengthNum 2 = 2 * 2 ^ 2 * pathLengthDen 2 := by native_decide

theorem pathRecurrence_n3 :
    (2 ^ 3 - 2) * pathLengthNum 3 =
      pathLengthDen 3 * (3 * 2 ^ 3 + 2 * Nat.choose 3 2 * pathLengthNum 2) := by
  native_decide

theorem pathRecurrence_n4 :
    (2 ^ 4 - 2) * pathLengthNum 4 =
      pathLengthDen 4 * (4 * 2 ^ 4 +
        2 * (Nat.choose 4 2 * pathLengthNum 2 +
             Nat.choose 4 3 * pathLengthNum 3)) := by native_decide
/-! ## Average Search Depth D_n = P_n / n -/

def avgDepthNum : Fin 5 → ℕ := ![0, 0, 2, 8, 22]
def avgDepthDen : Fin 5 → ℕ := ![1, 1, 1, 3, 7]

theorem avgDepth_consistent :
    avgDepthNum 2 * 2 * pathLengthDen 2 = pathLengthNum 2 * avgDepthDen 2 ∧
    avgDepthNum 3 * 3 * pathLengthDen 3 = pathLengthNum 3 * avgDepthDen 3 ∧
    avgDepthNum 4 * 4 * pathLengthDen 4 = pathLengthNum 4 * avgDepthDen 4 := by
  native_decide
/-! ## Splitting Probability at Root -/

/-- Numerator of P[non-trivial split at root for n strings], scaled by 2^n. -/
def splitNumerator (n : ℕ) : ℕ := 2 ^ n - 2

theorem split_values :
    List.map splitNumerator [2, 3, 4, 5, 6, 7, 8] =
      [2, 6, 14, 30, 62, 126, 254] := by native_decide
/-! ## Per-Depth Node Contribution -/

/-- P[≥2 of n strings share a specific d-bit prefix], scaled by 2^{dn}. -/
def trieDepthNumerator (d n : ℕ) : ℕ :=
  if n < 2 then 0
  else 2 ^ (d * n) - (2 ^ d - 1) ^ n - n * (2 ^ d - 1) ^ (n - 1)

theorem depth_numerator_values :
    List.map (trieDepthNumerator 0) [2, 3, 4] = [1, 1, 1] ∧
    List.map (trieDepthNumerator 1) [2, 3, 4] = [1, 4, 11] ∧
    List.map (trieDepthNumerator 2) [2, 3, 4] = [1, 10, 67] ∧
    List.map (trieDepthNumerator 3) [2, 3, 4] = [1, 22, 323] := by native_decide

theorem depth_numerator_n2_constant :
    List.map (fun d => trieDepthNumerator d 2) [0, 1, 2, 3, 4, 5, 6, 7] =
      [1, 1, 1, 1, 1, 1, 1, 1] := by native_decide

/-! ## Cumulative Scaled Expected Nodes -/

/-- Expected internal nodes over depths 0..b-1, scaled by (2^b)^n. -/
def scaledTrieNodes (b n : ℕ) : ℕ :=
  (Finset.range b).sum fun d =>
    2 ^ d * 2 ^ ((b - d) * n) * trieDepthNumerator d n

theorem scaledTrieNodes_values :
    List.map (fun b => scaledTrieNodes b 2) [1, 2, 3, 4, 5] =
      [4, 24, 112, 480, 1984] ∧
    List.map (fun b => scaledTrieNodes b 3) [1, 2, 3, 4] =
      [8, 128, 1344, 12160] ∧
    List.map (fun b => scaledTrieNodes b 4) [1, 2, 3, 4] =
      [16, 608, 14016, 265600] := by native_decide

theorem scaledTrieNodes_n2_closed :
    scaledTrieNodes 1 2 + 2 ^ 2 = 2 ^ 3 ∧
    scaledTrieNodes 2 2 + 2 ^ 3 = 2 ^ 5 ∧
    scaledTrieNodes 3 2 + 2 ^ 4 = 2 ^ 7 ∧
    scaledTrieNodes 4 2 + 2 ^ 5 = 2 ^ 9 ∧
    scaledTrieNodes 5 2 + 2 ^ 6 = 2 ^ 11 := by native_decide

/-! ## Monotonicity and Bounds -/

theorem trieNodes_increasing :
    trieNodesNum 2 * trieNodesDen 3 < trieNodesNum 3 * trieNodesDen 2 ∧
    trieNodesNum 3 * trieNodesDen 4 < trieNodesNum 4 * trieNodesDen 3 := by native_decide

theorem avgDepth_increasing :
    avgDepthNum 2 * avgDepthDen 3 < avgDepthNum 3 * avgDepthDen 2 ∧
    avgDepthNum 3 * avgDepthDen 4 < avgDepthNum 4 * avgDepthDen 3 := by native_decide

theorem trieNodes_ge_n_minus_one :
    trieNodesNum 2 ≥ 1 * trieNodesDen 2 ∧
    trieNodesNum 3 ≥ 2 * trieNodesDen 3 ∧
    trieNodesNum 4 ≥ 3 * trieNodesDen 4 := by native_decide

theorem pathLength_ge_n :
    pathLengthNum 2 ≥ 2 * pathLengthDen 2 ∧
    pathLengthNum 3 ≥ 3 * pathLengthDen 3 ∧
    pathLengthNum 4 ≥ 4 * pathLengthDen 4 := by native_decide

-- The trie recurrence determines a unique sequence (strong induction, 2^n-2 ≠ 0)
theorem trie_recurrence_unique (f g : ℕ → ℚ)
    (hf0 : f 0 = 0) (hf1 : f 1 = 0) (hg0 : g 0 = 0) (hg1 : g 1 = 0)
    (hf : ∀ n, n ≥ 2 → ((2 : ℚ) ^ n - 2) * f n =
      (2 : ℚ) ^ n + 2 * ∑ k ∈ Finset.range n, (Nat.choose n k : ℚ) * f k)
    (hg : ∀ n, n ≥ 2 → ((2 : ℚ) ^ n - 2) * g n =
      (2 : ℚ) ^ n + 2 * ∑ k ∈ Finset.range n, (Nat.choose n k : ℚ) * g k) :
    f = g := by
  sorry

end TrieAnalysis
