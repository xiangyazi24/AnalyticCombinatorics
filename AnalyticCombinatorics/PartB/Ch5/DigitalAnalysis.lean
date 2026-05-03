/-
  Analytic Combinatorics — Part B
  Chapter V — Digital Analysis

  Numerical verifications related to digital/radix analysis of numbers and
  trees (trie analysis, Ch V of Flajolet & Sedgewick).
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace DigitalAnalysis

/-! ## 1. Binary representations -/

/-- Number of n-bit binary strings = 2^n. -/
example : (2 : ℕ) ^ 8 = 256 := by native_decide

/-- Number of n-bit strings with no two consecutive 1s satisfies a Fibonacci recurrence. -/
def noConsec1 : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | n + 2 => noConsec1 (n + 1) + noConsec1 n
  termination_by n => n

-- Spot checks
example : noConsec1 0 = 1 := by native_decide
example : noConsec1 1 = 2 := by native_decide
example : noConsec1 2 = 3 := by native_decide
example : noConsec1 3 = 5 := by native_decide
example : noConsec1 4 = 8 := by native_decide
example : noConsec1 5 = 13 := by native_decide

-- noConsec1 n = Nat.fib (n + 2) for n = 0 .. 8
example : noConsec1 0 = Nat.fib 2 := by native_decide
example : noConsec1 1 = Nat.fib 3 := by native_decide
example : noConsec1 2 = Nat.fib 4 := by native_decide
example : noConsec1 3 = Nat.fib 5 := by native_decide
example : noConsec1 4 = Nat.fib 6 := by native_decide
example : noConsec1 5 = Nat.fib 7 := by native_decide
example : noConsec1 6 = Nat.fib 8 := by native_decide
example : noConsec1 7 = Nat.fib 9 := by native_decide
example : noConsec1 8 = Nat.fib 10 := by native_decide

/-! ## 2. Trie depth analysis -/

-- Complete binary trie of depth d has 2^d - 1 internal nodes.
example : (2 : ℕ) ^ 4 - 1 = 15 := by native_decide
example : (2 : ℕ) ^ 5 - 1 = 31 := by native_decide

/-- Internal path length of a complete binary trie of depth d.
    IPL = Σ_{k=0}^{d-1} k * 2^k  (each node at depth k contributes k). -/
def trieIPL (d : ℕ) : ℕ := ∑ k ∈ Finset.range d, k * 2 ^ k

-- Spot checks
example : trieIPL 1 = 0 := by native_decide
example : trieIPL 2 = 2 := by native_decide
example : trieIPL 3 = 10 := by native_decide
example : trieIPL 4 = 34 := by native_decide
example : trieIPL 5 = 98 := by native_decide
example : trieIPL 6 = 258 := by native_decide

-- Closed-form verification in ℤ: Σ_{k=0}^{d-1} k·2^k = (d−2)·2^d + 2 for d ≥ 1.
-- We verify via cast to ℤ to handle the subtraction cleanly.
example : (trieIPL 2 : ℤ) = (2 - 2) * 2 ^ 2 + 2 := by native_decide
example : (trieIPL 3 : ℤ) = (3 - 2) * 2 ^ 3 + 2 := by native_decide
example : (trieIPL 4 : ℤ) = (4 - 2) * 2 ^ 4 + 2 := by native_decide
example : (trieIPL 5 : ℤ) = (5 - 2) * 2 ^ 5 + 2 := by native_decide
example : (trieIPL 6 : ℤ) = (6 - 2) * 2 ^ 6 + 2 := by native_decide

/-! ## 3. Digital sum / bit count -/

/-- s(n) = number of 1-bits in the binary representation of n. -/
def bitCount : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) % 2 + bitCount ((n + 1) / 2)
  termination_by n => n
  decreasing_by omega

-- Spot checks
example : bitCount 0 = 0 := by native_decide
example : bitCount 1 = 1 := by native_decide
example : bitCount 2 = 1 := by native_decide
example : bitCount 3 = 2 := by native_decide
example : bitCount 7 = 3 := by native_decide
example : bitCount 8 = 1 := by native_decide
example : bitCount 15 = 4 := by native_decide
example : bitCount 255 = 8 := by native_decide

/-- Total number of 1-bits over all n-bit numbers: Σ_{k=0}^{2^n-1} s(k). -/
def totalBitCount (n : ℕ) : ℕ := ∑ k ∈ Finset.range (2 ^ n), bitCount k

-- Spot checks
example : totalBitCount 1 = 1 := by native_decide
example : totalBitCount 2 = 4 := by native_decide
example : totalBitCount 3 = 12 := by native_decide
example : totalBitCount 4 = 32 := by native_decide
example : totalBitCount 5 = 80 := by native_decide

-- Formula: totalBitCount n = n * 2^(n-1) for n = 1 .. 5.
example : totalBitCount 1 = 1 * 2 ^ (1 - 1) := by native_decide
example : totalBitCount 2 = 2 * 2 ^ (2 - 1) := by native_decide
example : totalBitCount 3 = 3 * 2 ^ (3 - 1) := by native_decide
example : totalBitCount 4 = 4 * 2 ^ (4 - 1) := by native_decide
example : totalBitCount 5 = 5 * 2 ^ (5 - 1) := by native_decide

/-! ## 4. Radix-sort comparison count / number of bits -/

/-- Number of bits needed to represent n: ⌊log₂ n⌋ + 1 for n ≥ 1, 0 for n = 0. -/
def numBits (n : ℕ) : ℕ := if n = 0 then 0 else Nat.log 2 n + 1

-- Spot checks
example : numBits 1 = 1 := by native_decide
example : numBits 3 = 2 := by native_decide
example : numBits 4 = 3 := by native_decide
example : numBits 7 = 3 := by native_decide
example : numBits 8 = 4 := by native_decide
example : numBits 15 = 4 := by native_decide
example : numBits 16 = 5 := by native_decide
example : numBits 255 = 8 := by native_decide
example : numBits 256 = 9 := by native_decide

/-! ## 5. Patricia trie / compressed trie -/

-- A complete binary trie of depth d has 2^d leaves and 2^d - 1 internal nodes.
-- Verify the structural off-by-one: leaves = internal + 1.
example : (2 : ℕ) ^ 3 = (2 ^ 3 - 1) + 1 := by native_decide
example : (2 : ℕ) ^ 4 = (2 ^ 4 - 1) + 1 := by native_decide
example : (2 : ℕ) ^ 5 = (2 ^ 5 - 1) + 1 := by native_decide
example : (2 : ℕ) ^ 8 = (2 ^ 8 - 1) + 1 := by native_decide

-- For any binary tree with n leaves there are n - 1 internal nodes.
-- Equivalently, internal + 1 = leaves.  We verify for the complete-trie family
-- parametrised by depth d (d = 0 .. 9).
example : ∀ d : Fin 10, 2 ^ (d : ℕ) = (2 ^ (d : ℕ) - 1) + 1 := by native_decide

/-! ## 6. Gray code properties -/

/-- Standard binary-reflected Gray code: n ↦ n XOR (n / 2). -/
def grayCode (n : ℕ) : ℕ := n ^^^ (n / 2)

-- Spot checks for n = 0 .. 7
example : grayCode 0 = 0 := by native_decide
example : grayCode 1 = 1 := by native_decide
example : grayCode 2 = 3 := by native_decide
example : grayCode 3 = 2 := by native_decide
example : grayCode 4 = 6 := by native_decide
example : grayCode 5 = 7 := by native_decide
example : grayCode 6 = 5 := by native_decide
example : grayCode 7 = 4 := by native_decide

-- Adjacent Gray codes differ in exactly one bit (XOR is a power of 2).
example : grayCode 0 ^^^ grayCode 1 = 1 := by native_decide
example : grayCode 1 ^^^ grayCode 2 = 2 := by native_decide
example : grayCode 2 ^^^ grayCode 3 = 1 := by native_decide
example : grayCode 3 ^^^ grayCode 4 = 4 := by native_decide
example : grayCode 4 ^^^ grayCode 5 = 1 := by native_decide
example : grayCode 5 ^^^ grayCode 6 = 2 := by native_decide
example : grayCode 6 ^^^ grayCode 7 = 1 := by native_decide

-- All XOR differences above are powers of 2.
example : Nat.isPowerOfTwo (grayCode 0 ^^^ grayCode 1) := by native_decide
example : Nat.isPowerOfTwo (grayCode 1 ^^^ grayCode 2) := by native_decide
example : Nat.isPowerOfTwo (grayCode 2 ^^^ grayCode 3) := by native_decide
example : Nat.isPowerOfTwo (grayCode 3 ^^^ grayCode 4) := by native_decide
example : Nat.isPowerOfTwo (grayCode 4 ^^^ grayCode 5) := by native_decide
example : Nat.isPowerOfTwo (grayCode 5 ^^^ grayCode 6) := by native_decide
example : Nat.isPowerOfTwo (grayCode 6 ^^^ grayCode 7) := by native_decide

end DigitalAnalysis
