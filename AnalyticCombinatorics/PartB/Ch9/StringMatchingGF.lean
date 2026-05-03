import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace StringMatchingGF

open Finset

/-!
# String Matching and Pattern Statistics via Generating Functions

Chapter IX of *Analytic Combinatorics* (Flajolet–Sedgewick).

Covers: autocorrelation polynomial, Guibas–Odlyzko theory, probability of
pattern occurrence in random text, overlap-free words, and waiting time
distributions.  All definitions are exact rational or natural-number
computations; proofs are by `native_decide`.
-/

-- ============================================================
-- §1  Autocorrelation polynomial
-- ============================================================

/-!
### 1. Autocorrelation of a binary pattern

Given a binary pattern `p` of length `m`, the autocorrelation set records
positions `k` (0 ≤ k < m) where the suffix of length `m - k` matches the
prefix of the same length.  The autocorrelation polynomial is
`C(z) = ∑_{k ∈ corr} z^k`.
-/

/-- Check whether the prefix of `p` of length `|p| - shift` equals the suffix
    starting at position `shift`. -/
def prefixMatchesSuffix (p : List Bool) (shift : Nat) : Bool :=
  let suf := p.drop shift
  let pre := p.take suf.length
  pre == suf

/-- Autocorrelation indicator vector. -/
def autocorrVec (p : List Bool) : List Bool :=
  (List.range p.length).map fun k => prefixMatchesSuffix p k

/-- Autocorrelation as a set of shift values. -/
def autocorrSet (p : List Bool) : List Nat :=
  (List.range p.length).filter fun k => prefixMatchesSuffix p k

/-- Rational autocorrelation polynomial evaluated at `z`:
    `C(z) = ∑_{k ∈ autocorrSet p} z^k`. -/
def autocorrPoly (p : List Bool) (z : ℚ) : ℚ :=
  (autocorrSet p).foldl (fun acc k => acc + z ^ k) 0

def pat_aaa : List Bool := [true, true, true]
def pat_aba : List Bool := [true, false, true]
def pat_aab : List Bool := [true, true, false]
def pat_abab : List Bool := [true, false, true, false]

example : autocorrSet pat_aaa = [0, 1, 2] := by native_decide
example : autocorrVec pat_aaa = [true, true, true] := by native_decide
example : autocorrSet pat_aba = [0, 2] := by native_decide
example : autocorrSet pat_aab = [0] := by native_decide
example : autocorrSet pat_abab = [0, 2] := by native_decide

-- ============================================================
-- §2  Guibas–Odlyzko: counting strings that avoid a pattern
-- ============================================================

/-!
### 2. Guibas–Odlyzko formula (numerical verification)

For a binary alphabet, the number `S_n` of strings of length `n` that
**avoid** a given pattern can be counted by brute force for small `n`.
Avoiding `aa = 11` on binary alphabet yields Fibonacci numbers.
-/

/-- Generate all binary strings of length `n`. -/
def allBinaryStrings : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
    let prev := allBinaryStrings n
    prev.map (true :: ·) ++ prev.map (false :: ·)

/-- Check if `p` occurs as a contiguous substring starting at position `i`. -/
def matchAt (text p : List Bool) (i : Nat) : Bool :=
  (text.drop i).take p.length == p

/-- Check if `p` occurs anywhere as a contiguous substring of `text`. -/
def containsPattern (text p : List Bool) : Bool :=
  match p with
  | [] => true
  | _ =>
    if p.length > text.length then false
    else (List.range (text.length - p.length + 1)).any fun i => matchAt text p i

/-- Count strings of length `n` **avoiding** pattern `p`. -/
def countAvoiding (p : List Bool) (n : Nat) : Nat :=
  (allBinaryStrings n).countP fun s => !containsPattern s p

def pat_aa : List Bool := [true, true]

/-! Avoidance of `aa = 11` on binary alphabet gives Fibonacci numbers. -/
theorem avoid_aa_fibonacci :
    [countAvoiding pat_aa 0, countAvoiding pat_aa 1, countAvoiding pat_aa 2,
     countAvoiding pat_aa 3, countAvoiding pat_aa 4, countAvoiding pat_aa 5] =
    [1, 2, 3, 5, 8, 13] := by native_decide

-- ============================================================
-- §3  Overlap-free words
-- ============================================================

/-!
### 3. Overlap-free words

A word is *overlap-free* if no proper prefix is also a suffix (apart from the
empty word).  Equivalently, its autocorrelation set is `{0}`.
-/

/-- A pattern is overlap-free when its only autocorrelation position is 0. -/
def isOverlapFree (p : List Bool) : Bool :=
  autocorrSet p == [0]

example : isOverlapFree pat_aab = true := by native_decide
example : isOverlapFree pat_aaa = false := by native_decide
example : isOverlapFree pat_aba = false := by native_decide
example : isOverlapFree pat_abab = false := by native_decide

/-- Count overlap-free binary patterns of length `m`. -/
def countOverlapFree (m : Nat) : Nat :=
  (allBinaryStrings m).countP fun p => isOverlapFree p

example : countOverlapFree 1 = 2 := by native_decide
example : countOverlapFree 2 = 2 := by native_decide
example : countOverlapFree 3 = 4 := by native_decide
example : countOverlapFree 4 = 6 := by native_decide

-- ============================================================
-- §4  Waiting time and occurrence probability
-- ============================================================

/-!
### 4. Waiting time for first occurrence

The expected waiting time for the first occurrence of pattern `p` in a random
binary string is  `E[T] = 2^m · C(1/2)`  where `m = |p|` and `C` is the
autocorrelation polynomial.
-/

/-- Expected waiting time for first occurrence over binary alphabet. -/
def expectedWaitingTime (p : List Bool) : ℚ :=
  let m := p.length
  (2 : ℚ) ^ m * autocorrPoly p (1 / 2)

example : expectedWaitingTime pat_aa = 6 := by native_decide
example : expectedWaitingTime pat_aaa = 14 := by native_decide
example : expectedWaitingTime pat_aba = 10 := by native_decide
example : expectedWaitingTime pat_aab = 8 := by native_decide
example : expectedWaitingTime pat_abab = 20 := by native_decide

/-! Overlap-free ⇒ minimal waiting time `2^m`. -/
theorem overlap_free_minimal_waiting :
    expectedWaitingTime pat_aab = 2 ^ pat_aab.length := by native_decide

-- ============================================================
-- §5  Conway leading number
-- ============================================================

/-!
### 5. Conway leading number

For two patterns `p` and `q`, the *leading number* `L(p, q)` sums
`r^{−k}` over lengths `k` where a length-`k` suffix of `p` matches
a length-`k` prefix of `q`.  When `p = q`, `L(p, p) = C(1/r)`.
-/

/-- Leading number `L(p, q)` for alphabet size `r`. -/
def leadingNumber (p q : List Bool) (r : ℚ) : ℚ :=
  let maxLen := min p.length q.length
  (List.range maxLen).foldl (fun acc i =>
    let len := i + 1
    let suffixP := p.drop (p.length - len)
    let prefixQ := q.take len
    if suffixP == prefixQ then acc + (1 / r) ^ (p.length - len)
    else acc) 0

example : leadingNumber pat_aaa pat_aaa 2 = 7 / 4 := by native_decide
example : leadingNumber pat_aab pat_aab 2 = 1 := by native_decide

/-! Self-leading number equals `C(1/r)`. -/
theorem self_leading_eq_autocorr_aaa :
    leadingNumber pat_aaa pat_aaa 2 = autocorrPoly pat_aaa (1 / 2) := by
  native_decide

theorem self_leading_eq_autocorr_aba :
    leadingNumber pat_aba pat_aba 2 = autocorrPoly pat_aba (1 / 2) := by
  native_decide

-- ============================================================
-- §6  Multiple pattern occurrences
-- ============================================================

/-!
### 6. Counting occurrences of a pattern

Distribution of the number of (possibly overlapping) occurrences of a
pattern in random binary strings of fixed length.
-/

/-- Count (possibly overlapping) occurrences of `p` in `text`. -/
def countOccurrences (text p : List Bool) : Nat :=
  if p.length > text.length then 0
  else
    (List.range (text.length - p.length + 1)).countP fun i =>
      matchAt text p i

/-- Number of length-`n` binary strings with exactly `k` occurrences of `p`. -/
def stringsWithExactly (p : List Bool) (n k : Nat) : Nat :=
  (allBinaryStrings n).countP fun s => countOccurrences s p == k

/-! Distribution of `a` occurrences in binary strings of length 3 is binomial. -/
theorem occurrence_dist_a_len3 :
    [stringsWithExactly [true] 3 0, stringsWithExactly [true] 3 1,
     stringsWithExactly [true] 3 2, stringsWithExactly [true] 3 3] =
    [1, 3, 3, 1] := by native_decide

/-! Distribution of `aa` occurrences in binary strings of length 4. -/
theorem occurrence_dist_aa_len4 :
    [stringsWithExactly [true, true] 4 0, stringsWithExactly [true, true] 4 1,
     stringsWithExactly [true, true] 4 2, stringsWithExactly [true, true] 4 3] =
    [8, 5, 2, 1] := by native_decide

/-! Total across all occurrence counts equals `2^n`. -/
theorem total_strings_aa_len4 :
    stringsWithExactly [true, true] 4 0 + stringsWithExactly [true, true] 4 1 +
    stringsWithExactly [true, true] 4 2 + stringsWithExactly [true, true] 4 3 =
    2 ^ 4 := by native_decide

end StringMatchingGF
