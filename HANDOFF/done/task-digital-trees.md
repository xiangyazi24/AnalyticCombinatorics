# Task: Digital Trees (Tries) (Ch V/IX)

## Goal

Create `AnalyticCombinatorics/PartB/Ch5/DigitalTrees.lean`.

## What to formalize

Counting and analysis of digital search structures (tries).

1. **Binary trie internal path length:**
   For n random binary strings, expected internal path ≈ n * log2(n).
   
   Number of binary tries with n external nodes = number of ways to fill a binary tree:
   Actually the structure is determined by the strings. Just verify:
   ```lean
   -- Number of distinct binary tries on n keys = too complex.
   -- Instead: number of complete binary trees with n leaves.
   def completeBinaryTreeLeaves (depth : ℕ) : ℕ := 2^depth
   ```
   
2. **Expected depth in binary trie:**
   For n uniform random binary strings, average search depth ≈ log2(n).
   Just verify powers of 2:
   ```lean
   example : Nat.log 2 1 = 0 := by native_decide
   example : Nat.log 2 2 = 1 := by native_decide
   example : Nat.log 2 4 = 2 := by native_decide
   example : Nat.log 2 8 = 3 := by native_decide
   example : Nat.log 2 1024 = 10 := by native_decide
   ```

3. **Patricia trie (compressed):**
   Compressing unary paths. For binary strings, internal nodes = n - 1.
   ```lean
   def patriciaPaths (n : ℕ) : ℕ := if n ≤ 1 then 0 else n - 1
   ```
   Verify for n=1..10.

4. **Digital search tree profile:**
   Expected number of nodes at depth k in a random DST with n keys:
   For n=2^d, roughly 1 node at each depth 0..d-1.
   
   Simpler: total number of internal nodes in a trie/DST with n strings = n-1 (approximately).
   Actually: for BST, internal nodes = n (each key is internal). For trie, it varies.
   
   Just verify BST depth bounds:
   Minimum BST depth for n nodes = ⌊log2(n)⌋.
   ```lean
   def minBSTDepth (n : ℕ) : ℕ := Nat.log 2 n
   ```
   Verify: minBSTDepth 7 = 2, minBSTDepth 8 = 3, minBSTDepth 15 = 3, minBSTDepth 16 = 4.

5. **Radix sort complexity:**
   Radix sort on n d-digit numbers: work = O(n*d).
   For binary strings of length b: total comparisons = n*b.
   ```lean
   def radixWork (n b : ℕ) : ℕ := n * b
   ```
   Verify: for n=1000 binary strings of length 10: radixWork 1000 10 = 10000.
   Compare to comparison sort: n*log2(n) ≈ 1000*10 = 10000.
   Verify: 1000 * Nat.log 2 1000 = 1000 * 9 = 9000 (since log2(1000) = 9).

## Imports

```lean
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartB.Ch5.DigitalTrees`
- No sorry, no axiom
- Delete anything that doesn't compile
- native_decide for all checks
- **Must wrap all definitions in `namespace DigitalTrees`** and close with `end DigitalTrees`

## Output

Write file, verify build, report.
