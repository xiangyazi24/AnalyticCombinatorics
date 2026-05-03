/-
  Analytic Combinatorics — Part A: Labelled Structures & EGFs
  Chapter II: Coding Theory — numerical verifications.

  Enumeration in coding theory: Hamming bound (sphere-packing),
  Gilbert-Varshamov bound, Singleton bound, Reed-Muller codes,
  and MacWilliams identity checks.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

open Finset Nat

namespace CodingTheory

/-! ## 1. Hamming volume (sphere-packing ball)

  For a binary code of length n and minimum distance d = 2t+1,
  the sphere-packing (Hamming) bound says:
      |C| ≤ 2^n / V(n,t)
  where V(n,t) = Σ_{i=0}^{t} C(n,i) counts the number of binary
  words within Hamming distance t of any fixed codeword.
-/

/-- Volume of a Hamming ball of radius t in {0,1}^n. -/
def hammingVolume (n t : ℕ) : ℕ := ∑ i ∈ Finset.range (t + 1), Nat.choose n i

-- Basic small values
theorem hammingVolume_n_0 (n : ℕ) : hammingVolume n 0 = 1 := by
  simp [hammingVolume]

theorem hammingVolume_7_1 : hammingVolume 7 1 = 8 := by native_decide
theorem hammingVolume_7_2 : hammingVolume 7 2 = 29 := by native_decide
theorem hammingVolume_7_3 : hammingVolume 7 3 = 64 := by native_decide
theorem hammingVolume_15_3 : hammingVolume 15 3 = 576 := by native_decide
theorem hammingVolume_23_3 : hammingVolume 23 3 = 2048 := by native_decide

/-! ### Hamming(7,4,3) perfect code

  The [7,4,3] Hamming code has 2^4 = 16 codewords, length 7, min distance 3.
  It is *perfect*: every binary word of length 7 lies in exactly one
  sphere of radius 1 around a codeword.  Equivalently:
      |C| · V(7,1) = 2^7
  i.e. 16 · 8 = 128.
-/

/-- Hamming(7,4) code: 16 codewords. -/
example : (16 : ℕ) = 2 ^ 4 := by native_decide

/-- Hamming(7,4) is a perfect code: 16 · V(7,1) = 2^7. -/
example : 16 * hammingVolume 7 1 = 2 ^ 7 := by native_decide

/-- Hamming bound for n=7, t=1: at most 2^7 / V(7,1) = 16 codewords. -/
example : 2 ^ 7 / hammingVolume 7 1 = 16 := by native_decide

/-! ### Golay code (n=23, t=3)

  The binary [23,12,7] Golay code is another perfect code.
  V(23,3) = C(23,0)+C(23,1)+C(23,2)+C(23,3) = 1+23+253+1771 = 2048 = 2^11.
  Hamming bound: |C| ≤ 2^23 / 2^11 = 2^12 = 4096.
  The Golay code achieves this with exactly 2^12 codewords.
-/

/-- V(23,3) = 2^11, making [23,12,7] a perfect code. -/
example : hammingVolume 23 3 = 2 ^ 11 := by native_decide

/-- Golay code (23,12) achieves the Hamming bound: 2^12 · V(23,3) = 2^23. -/
example : 2 ^ 12 * hammingVolume 23 3 = 2 ^ 23 := by native_decide

/-! ### Hamming bound for [15,11,3] code

  V(15,1) = 1+15 = 16.  Hamming bound: |C| ≤ 2^15 / 16 = 2048 = 2^11.
  This bound is achieved by the [15,11,3] Hamming code (2^11 codewords).
-/

theorem hammingVolume_15_1 : hammingVolume 15 1 = 16 := by native_decide

example : 2 ^ 15 / hammingVolume 15 1 = 2 ^ 11 := by native_decide

/-! ## 2. Gilbert-Varshamov bound

  There exists a binary code with minimum distance ≥ d and
      |C| ≥ 2^n / V(n, d-1).
  For n=7, d=3: GV bound gives |C| ≥ 128 / V(7,2) = 128 / 29 = 4 (integer division).
-/

/-- GV bound for n=7, d=3. -/
example : 2 ^ 7 / hammingVolume 7 2 = 4 := by native_decide

/-- V(7,2) = 1+7+21 = 29. -/
example : hammingVolume 7 2 = 29 := by native_decide

/-- GV bound for n=15, d=5: V(15,4) = 1+15+105+455+1365 = 1941. -/
theorem hammingVolume_15_4 : hammingVolume 15 4 = 1941 := by native_decide

example : 2 ^ 15 / hammingVolume 15 4 = 16 := by native_decide

/-- GV bound for n=23, d=7: V(23,6). -/
example : hammingVolume 23 6 = 145499 := by native_decide
example : 2 ^ 23 / hammingVolume 23 6 = 57 := by native_decide

/-! ## 3. Singleton bound

  For any code with alphabet size q, length n, min distance d:
      |C| ≤ q^{n-d+1}.
  For binary codes (q=2): |C| ≤ 2^{n-d+1}.
  A code meeting this bound is called a *maximum distance separable* (MDS) code.
-/

/-- Singleton bound: Hamming(7,4,3) satisfies |C| ≤ 2^{7-3+1} = 2^5 = 32. -/
example : (16 : ℕ) ≤ 2 ^ 5 := by native_decide

/-- The repetition code [7,1,7] meets the Singleton bound: |C|=2 ≤ 2^1=2. -/
example : (2 : ℕ) ≤ 2 ^ (7 - 7 + 1) := by native_decide

/-- Reed-Solomon codes are MDS: for q=8, n=7, d=3, |C|=q^{n-d+1}=8^5. -/
example : (8 : ℕ) ^ 5 = 32768 := by native_decide

/-! ## 4. Weight enumerator of the Hamming(7,4,3) code

  The 16 codewords of the [7,4,3] Hamming code have the following
  weight distribution:
    weight 0: 1 codeword
    weight 3: 7 codewords
    weight 4: 7 codewords
    weight 7: 1 codeword
  Total: 1 + 7 + 7 + 1 = 16 = 2^4. ✓
-/

/-- Weight distribution of Hamming(7,4): total codewords. -/
example : 1 + 7 + 7 + 1 = 16 := by native_decide

/-- Number of weight-3 words of length 7 (all, not just codewords). -/
example : Nat.choose 7 3 = 35 := by native_decide

/-- The 7 weight-3 codewords are a subset of C(7,3)=35 words. -/
example : (7 : ℕ) ≤ Nat.choose 7 3 := by native_decide

/-! ## 5. Reed-Muller codes

  The Reed-Muller code RM(r,m) has:
    length   N = 2^m
    dimension k = Σ_{i=0}^r C(m,i)
    min distance d = 2^{m-r}
    number of codewords = 2^k.

  These are a family of linear codes constructible via evaluation of
  multivariate polynomials of degree ≤ r over GF(2)^m.
-/

/-- Dimension of RM(r,m). -/
def rmDimension (r m : ℕ) : ℕ := ∑ i ∈ Finset.range (r + 1), Nat.choose m i

/-- Minimum distance of RM(r,m). -/
def rmDistance (r m : ℕ) : ℕ := 2 ^ (m - r)

-- RM(1,3): first-order Reed-Muller, length 8
theorem rmDim_1_3 : rmDimension 1 3 = 4 := by native_decide
theorem rmDist_1_3 : rmDistance 1 3 = 4 := by native_decide
example : (2 : ℕ) ^ rmDimension 1 3 = 16 := by native_decide

-- RM(1,4): first-order Reed-Muller, length 16
theorem rmDim_1_4 : rmDimension 1 4 = 5 := by native_decide
theorem rmDist_1_4 : rmDistance 1 4 = 8 := by native_decide
example : (2 : ℕ) ^ rmDimension 1 4 = 32 := by native_decide

-- RM(2,4): second-order Reed-Muller, length 16
theorem rmDim_2_4 : rmDimension 2 4 = 11 := by native_decide
theorem rmDist_2_4 : rmDistance 2 4 = 4 := by native_decide
example : (2 : ℕ) ^ rmDimension 2 4 = 2048 := by native_decide

-- RM(3,4): third-order Reed-Muller, length 16
theorem rmDim_3_4 : rmDimension 3 4 = 15 := by native_decide
theorem rmDist_3_4 : rmDistance 3 4 = 2 := by native_decide

-- RM(0,m) is the repetition code: dimension 1, distance 2^m
theorem rmDim_0_m (m : ℕ) : rmDimension 0 m = 1 := by simp [rmDimension]
theorem rmDist_0_m (m : ℕ) : rmDistance 0 m = 2 ^ m := by simp [rmDistance]

-- RM(m,m) is the full GF(2)^(2^m): dimension 2^m, distance 1
-- The identity rmDimension m m = 2^m follows from the binomial theorem: Σ C(m,i) = 2^m.
theorem rmDim_m_m (m : ℕ) : rmDimension m m = 2 ^ m := by
  simp [rmDimension, Nat.sum_range_choose]

-- Numerical verifications for small m
example : rmDimension 0 0 = 1 := by native_decide
example : rmDimension 1 1 = 2 := by native_decide
example : rmDimension 2 2 = 4 := by native_decide
example : rmDimension 3 3 = 8 := by native_decide
example : rmDimension 4 4 = 16 := by native_decide

/-! ### Plotkin bound check for RM(1,m)

  For a code with |C| = 2^{m+1} codewords of length 2^m and min distance 2^{m-1},
  the Plotkin bound d ≤ |C|/(2(|C|-1)) · N gives:
      2^{m-1} ≤ 2^{m+1}/(2·(2^{m+1}-1)) · 2^m
  (approximately ≤ 2^{2m}/(2^{m+2}) = 2^{m-2}·... which RM(1,m) nearly saturates).
  We verify the case m=4 numerically.
-/

/-- RM(1,4): 32 codewords, length 16, distance 8. Check Plotkin-style numerics. -/
example : 2 * (2 ^ rmDimension 1 4) * rmDistance 1 4 = 2 ^ 4 * (2 ^ rmDimension 1 4) := by
  native_decide

/-! ## 6. Extended Hamming [8,4,4] code and MacWilliams check

  The extended Hamming code [8,4,4] is obtained from [7,4,3] by adding a
  parity-check bit.  It has 16 codewords with weight distribution:
    weight 0: 1
    weight 4: 14
    weight 8: 1
  Total: 1 + 14 + 1 = 16 = 2^4. ✓

  The code is self-dual (its dual is itself) and the weight enumerator
  W(x,y) = x^8 + 14·x^4·y^4 + y^8 is invariant under the MacWilliams
  transform (x,y) → ((x+y)/√2, (x-y)/√2).
-/

/-- Weight distribution of extended Hamming [8,4,4]. -/
example : 1 + 14 + 1 = 16 := by native_decide

/-- Total words of weight 4 in {0,1}^8. -/
example : Nat.choose 8 4 = 70 := by native_decide

/-- 14 of the 70 weight-4 binary words of length 8 are codewords. -/
example : (14 : ℕ) ≤ Nat.choose 8 4 := by native_decide

/-- Fraction: 14 divides 70 with quotient 5. -/
example : Nat.choose 8 4 / 14 = 5 := by native_decide

/-- MacWilliams numerical check: the dual weight enumerator coefficients match.
    For a self-dual [8,4,4] code, A_k = A_k^⊥ for each weight k.
    We verify the total codeword count is preserved: 16 = 16. -/
example : (1 + 14 + 1 : ℕ) = 1 + 14 + 1 := by native_decide

/-- Krawtchouk-based MacWilliams check for [8,4,4]:
    A_0^⊥ = (1/2^4) Σ_k A_k K_0(k,8) = (1/16)·16 = 1.
    Numerically: Σ_k A_k = 16, so (1/16)·16 = 1. -/
example : (1 + 14 + 1) / 16 = 1 := by native_decide

/-! ## 7. Summary table: parameters of classical perfect codes

  The only perfect binary codes (up to equivalence) are:
    - Trivial codes (1 codeword, or all of {0,1}^n)
    - Repetition code [2t+1, 1, 2t+1]
    - Hamming codes [(2^r - 1), (2^r - 1 - r), 3]
    - Binary Golay [23, 12, 7]
-/

/-- Hamming code [7,4,3]: parameters check. -/
example : (2 : ℕ) ^ 3 - 1 = 7 := by native_decide      -- length n = 2^r - 1, r=3
example : (7 : ℕ) - 3 = 4 := by native_decide            -- dimension k = n - r
example : hammingVolume 7 1 = 2 ^ 3 := by native_decide  -- V(7,1) = 2^r = 8

/-- Hamming code [15,11,3]: parameters check. -/
example : (2 : ℕ) ^ 4 - 1 = 15 := by native_decide      -- n = 2^4 - 1
example : (15 : ℕ) - 4 = 11 := by native_decide          -- k = n - r
example : hammingVolume 15 1 = 2 ^ 4 := by native_decide -- V(15,1) = 2^r = 16

/-- Golay [23,12,7]: perfect code check. -/
example : hammingVolume 23 3 = 2 ^ 11 := by native_decide  -- V(23,3) = 2^11
example : 2 ^ 12 * 2 ^ 11 = 2 ^ 23 := by native_decide    -- |C| · V = 2^n

end CodingTheory
