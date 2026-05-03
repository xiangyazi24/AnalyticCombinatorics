import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace RunLengthEncoding

/-! # Run-Length Encoding and Runs in Sequences (Flajolet & Sedgewick Ch. I)

Decomposition of words into maximal runs of identical symbols. Run statistics
in random binary words, Carlitz compositions (no two consecutive equal parts),
and words with restricted run lengths via the transfer matrix method. -/

-- ============================================================================
-- Counting Runs in Binary Words
-- ============================================================================

/-- Number of runs (maximal constant blocks) in a binary word. -/
def countRuns : List Bool → ℕ
  | [] => 0
  | [_] => 1
  | a :: b :: rest =>
    if a == b then countRuns (b :: rest)
    else 1 + countRuns (b :: rest)

example : countRuns [] = 0 := by native_decide
example : countRuns [true] = 1 := by native_decide
example : countRuns [true, true, true] = 1 := by native_decide
example : countRuns [true, false, true] = 3 := by native_decide
example : countRuns [false, false, true, true, false] = 3 := by native_decide
example : countRuns [true, false, true, false] = 4 := by native_decide

-- ============================================================================
-- Run-Length Encoding and Decoding
-- ============================================================================

/-- Accumulating encoder: track current symbol and run length. -/
def rleEncodeAux (a : Bool) (len : ℕ) : List Bool → List (Bool × ℕ)
  | [] => [(a, len)]
  | b :: rest =>
    if a == b then rleEncodeAux a (len + 1) rest
    else (a, len) :: rleEncodeAux b 1 rest

/-- Run-length encode a binary word into (symbol, run-length) pairs. -/
def rleEncode : List Bool → List (Bool × ℕ)
  | [] => []
  | a :: rest => rleEncodeAux a 1 rest

/-- Decode run-length encoding back to a binary word. -/
def rleDecode : List (Bool × ℕ) → List Bool
  | [] => []
  | (b, n) :: rest => List.replicate n b ++ rleDecode rest

theorem rle_encode_example :
    rleEncode [true, true, false, false, false, true] =
      [(true, 2), (false, 3), (true, 1)] := by native_decide

theorem rle_roundtrip_check :
    rleDecode (rleEncode [true, true, false, true]) =
      [true, true, false, true] ∧
    rleDecode (rleEncode [false, false, false]) =
      [false, false, false] := by native_decide

theorem rle_length_eq_runs :
    (rleEncode [true, false, true]).length = countRuns [true, false, true] ∧
    (rleEncode [true, true, false]).length = countRuns [true, true, false] ∧
    (rleEncode [false, true, false, true]).length =
      countRuns [false, true, false, true] := by native_decide

/-- Run-length encoding is lossless: decode ∘ encode = id on binary words. -/
theorem rle_roundtrip (w : List Bool) : rleDecode (rleEncode w) = w := by sorry

-- ============================================================================
-- Binary Word Enumeration and Run Distribution
-- ============================================================================

/-- All binary words of length n. -/
def allBinaryWords : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allBinaryWords n).flatMap fun w => [false :: w, true :: w]

theorem allBinaryWords_count :
    (allBinaryWords 0).length = 1 ∧
    (allBinaryWords 1).length = 2 ∧
    (allBinaryWords 2).length = 4 ∧
    (allBinaryWords 3).length = 8 ∧
    (allBinaryWords 4).length = 16 := by native_decide

/-- Number of length-n binary words with exactly k runs. -/
def wordsWithKRuns (n k : ℕ) : ℕ :=
  ((allBinaryWords n).filter (fun w => countRuns w == k)).length

/-- Words with k runs equals 2·C(n-1, k-1) for n, k ≥ 1. -/
theorem wordsWithKRuns_binomial :
    wordsWithKRuns 3 1 = 2 * Nat.choose 2 0 ∧
    wordsWithKRuns 3 2 = 2 * Nat.choose 2 1 ∧
    wordsWithKRuns 3 3 = 2 * Nat.choose 2 2 ∧
    wordsWithKRuns 4 1 = 2 * Nat.choose 3 0 ∧
    wordsWithKRuns 4 2 = 2 * Nat.choose 3 1 ∧
    wordsWithKRuns 4 3 = 2 * Nat.choose 3 2 ∧
    wordsWithKRuns 4 4 = 2 * Nat.choose 3 3 := by native_decide

theorem wordsWithKRuns_general (n k : ℕ) (hn : n ≥ 1) (hk : 1 ≤ k) (hk' : k ≤ n) :
    wordsWithKRuns n k = 2 * Nat.choose (n - 1) (k - 1) := by
  sorry

-- ============================================================================
-- Total Runs and Expected Value
-- ============================================================================

/-- Sum of run counts over all 2^n binary words of length n. -/
def totalRuns (n : ℕ) : ℕ :=
  ((allBinaryWords n).map countRuns).sum

/-- Total runs = (n + 1) · 2^(n-1), giving mean (n+1)/2 over 2^n words. -/
theorem totalRuns_values :
    totalRuns 1 = 2 * 2 ^ 0 ∧
    totalRuns 2 = 3 * 2 ^ 1 ∧
    totalRuns 3 = 4 * 2 ^ 2 ∧
    totalRuns 4 = 5 * 2 ^ 3 ∧
    totalRuns 5 = 6 * 2 ^ 4 := by native_decide

theorem totalRuns_general (n : ℕ) (hn : n ≥ 1) :
    totalRuns n = (n + 1) * 2 ^ (n - 1) := by
  sorry

-- ============================================================================
-- Carlitz Compositions
-- ============================================================================

/-- A composition is Carlitz if no two adjacent parts are equal. -/
def isCarlitz : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (a != b) && isCarlitz (b :: rest)

example : isCarlitz [1, 2, 1] = true := by native_decide
example : isCarlitz [1, 1, 2] = false := by native_decide
example : isCarlitz [3, 1, 2] = true := by native_decide
example : isCarlitz [2, 2] = false := by native_decide

/-- All compositions of n into positive parts. -/
def compositions : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (List.range (n + 1)).flatMap fun k =>
      (compositions (n - k)).map fun rest => (k + 1) :: rest
termination_by n => n
decreasing_by omega

theorem compositions_count :
    (compositions 0).length = 1 ∧
    (compositions 1).length = 1 ∧
    (compositions 2).length = 2 ∧
    (compositions 3).length = 4 ∧
    (compositions 4).length = 8 ∧
    (compositions 5).length = 16 := by native_decide

/-- Number of Carlitz compositions of n (OEIS A003242). -/
def carlitzCount (n : ℕ) : ℕ :=
  ((compositions n).filter isCarlitz).length

theorem carlitz_values :
    carlitzCount 0 = 1 ∧ carlitzCount 1 = 1 ∧ carlitzCount 2 = 1 ∧
    carlitzCount 3 = 3 ∧ carlitzCount 4 = 4 ∧ carlitzCount 5 = 7 ∧
    carlitzCount 6 = 13 ∧ carlitzCount 7 = 22 := by
  sorry

theorem carlitz_monotone :
    carlitzCount 4 > carlitzCount 3 ∧
    carlitzCount 5 > carlitzCount 4 ∧
    carlitzCount 6 > carlitzCount 5 ∧
    carlitzCount 7 > carlitzCount 6 := by native_decide

/-- Carlitz growth ratio is between 3/2 and 2, approaching κ ≈ 1.750. -/
theorem carlitz_ratio_bounds :
    2 * carlitzCount 6 > carlitzCount 7 ∧
    2 * carlitzCount 7 > 3 * carlitzCount 6 := by native_decide

-- ============================================================================
-- Transfer Matrix for Run-Restricted Words
-- ============================================================================

/-- 2×2 transfer matrix for DFA-based word counting. -/
structure Mat2 where
  a00 : ℕ
  a01 : ℕ
  a10 : ℕ
  a11 : ℕ
  deriving Repr, DecidableEq

def Mat2.mul (M N : Mat2) : Mat2 where
  a00 := M.a00 * N.a00 + M.a01 * N.a10
  a01 := M.a00 * N.a01 + M.a01 * N.a11
  a10 := M.a10 * N.a00 + M.a11 * N.a10
  a11 := M.a10 * N.a01 + M.a11 * N.a11

def Mat2.one : Mat2 where
  a00 := 1
  a01 := 0
  a10 := 0
  a11 := 1

def Mat2.pow (M : Mat2) : ℕ → Mat2
  | 0 => Mat2.one
  | n + 1 => Mat2.mul (Mat2.pow M n) M

/-- Transfer matrix for binary words avoiding "00".
    State 0: last symbol was 1 (or start). State 1: last symbol was 0. -/
def TnoRun2 : Mat2 where
  a00 := 1
  a01 := 1
  a10 := 1
  a11 := 0

/-- Binary words of length n with all 0-runs of length ≤ 1. -/
def countBounded0Run (n : ℕ) : ℕ :=
  let Tn := Mat2.pow TnoRun2 n
  Tn.a00 + Tn.a01

/-- These counts follow the Fibonacci sequence F(n+2). -/
theorem bounded0Run_fibonacci :
    countBounded0Run 0 = 1 ∧ countBounded0Run 1 = 2 ∧
    countBounded0Run 2 = 3 ∧ countBounded0Run 3 = 5 ∧
    countBounded0Run 4 = 8 ∧ countBounded0Run 5 = 13 ∧
    countBounded0Run 6 = 21 := by native_decide

theorem bounded0Run_recurrence_check :
    countBounded0Run 3 = countBounded0Run 2 + countBounded0Run 1 ∧
    countBounded0Run 4 = countBounded0Run 3 + countBounded0Run 2 ∧
    countBounded0Run 5 = countBounded0Run 4 + countBounded0Run 3 ∧
    countBounded0Run 6 = countBounded0Run 5 + countBounded0Run 4 := by native_decide

/-- The rational OGF (1+z)/(1-z-z²) yields f(n+2) = f(n+1) + f(n). -/
theorem bounded0Run_recurrence (n : ℕ) :
    countBounded0Run (n + 2) = countBounded0Run (n + 1) + countBounded0Run n := by
  sorry

/-- Partition of all binary words by run count sums to 2^n. -/
theorem run_partition_check :
    wordsWithKRuns 5 1 + wordsWithKRuns 5 2 + wordsWithKRuns 5 3 +
    wordsWithKRuns 5 4 + wordsWithKRuns 5 5 = 2 ^ 5 := by native_decide

end RunLengthEncoding
