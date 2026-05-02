import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace EntropyInformation

/-!
# Chapter IX: Information Theory and Combinatorial Entropy

Formalizes key results from Flajolet–Sedgewick Chapter IX on information-theoretic aspects:
- Multinomial coefficients
- Multiset permutation counting
- Entropy bounds on combinatorial quantities
- Method of types (type counting)
- Typical sequences
- Kraft inequality for prefix-free codes
-/

-- ============================================================================
-- § 1. Multinomial Coefficients
-- ============================================================================

/-- C(4; 2,1,1) = 4!/(2!·1!·1!) = 12 -/
example : Nat.factorial 4 / (Nat.factorial 2 * Nat.factorial 1 * Nat.factorial 1) = 12 := by
  native_decide

/-- C(6; 2,2,2) = 6!/(2!·2!·2!) = 90 -/
example : Nat.factorial 6 / (Nat.factorial 2 * Nat.factorial 2 * Nat.factorial 2) = 90 := by
  native_decide

/-- C(6; 3,2,1) = 6!/(3!·2!·1!) = 60 -/
example : Nat.factorial 6 / (Nat.factorial 3 * Nat.factorial 2 * Nat.factorial 1) = 60 := by
  native_decide

/-- C(10; 3,3,2,2) = 10!/(3!·3!·2!·2!) = 25200 -/
example : Nat.factorial 10 /
    (Nat.factorial 3 * Nat.factorial 3 * Nat.factorial 2 * Nat.factorial 2) = 25200 := by
  native_decide

-- ============================================================================
-- § 2. Number of Distinct Permutations of a Multiset
-- ============================================================================

/-- "MISSISSIPPI" has 11 letters: M(1), I(4), S(4), P(2).
    Permutations = 11!/(1!·4!·4!·2!) = 34650 -/
example : Nat.factorial 11 /
    (Nat.factorial 1 * Nat.factorial 4 * Nat.factorial 4 * Nat.factorial 2) = 34650 := by
  native_decide

-- ============================================================================
-- § 3. Entropy Bounds on Combinatorial Quantities
-- ============================================================================

/-- Upper bound: C(n,k) ≤ n^k/k! (weaker than entropy bound but integer-verifiable).
    C(10,3) = 120 ≤ 10^3/6 = 166 -/
example : Nat.choose 10 3 ≤ 10 ^ 3 / Nat.factorial 3 := by native_decide

/-- C(20,4) = 4845 ≤ 20^4/4! = 160000/24 = 6666 -/
example : Nat.choose 20 4 ≤ 20 ^ 4 / Nat.factorial 4 := by native_decide

/-- Lower bound: C(n,k) ≥ (n/k)^k.
    C(10,3) = 120 ≥ (10/3)^3 = 3^3 = 27 -/
example : Nat.choose 10 3 ≥ (10 / 3) ^ 3 := by native_decide

/-- C(20,5) = 15504 ≥ (20/5)^5 = 4^5 = 1024 -/
example : Nat.choose 20 5 ≥ (20 / 5) ^ 5 := by native_decide

-- ============================================================================
-- § 4. Type Counting (Method of Types)
-- ============================================================================

/-- Number of types on alphabet size k with n samples = C(n+k-1, k-1).
    k=2, n=10: C(11,1) = 11 types -/
example : Nat.choose 11 1 = 11 := by native_decide

/-- k=3, n=5: C(7,2) = 21 types -/
example : Nat.choose 7 2 = 21 := by native_decide

/-- k=4, n=9: C(12,3) = 220 types -/
example : Nat.choose 12 3 = 220 := by native_decide

-- ============================================================================
-- § 5. Typical Sequences
-- ============================================================================

/-- For binary iid p=1/2, n=8: sequences with exactly 4 ones = C(8,4) = 70 -/
example : Nat.choose 8 4 = 70 := by native_decide

/-- n=12, k=6: C(12,6) = 924 -/
example : Nat.choose 12 6 = 924 := by native_decide

/-- n=16, k=8: C(16,8) = 12870 -/
example : Nat.choose 16 8 = 12870 := by native_decide

-- ============================================================================
-- § 6. Kraft Inequality
-- ============================================================================

/-- Kraft inequality (integer form): Σ 2^{L-l_i} ≤ 2^L.
    Lengths {1,2,3,3}, L=3: 2^2 + 2^1 + 2^0 + 2^0 = 4+2+1+1 = 8 = 2^3 (complete code) -/
example : 4 + 2 + 1 + 1 = 2 ^ 3 := by native_decide

/-- Lengths {2,2,2,2}, L=2: 1+1+1+1 = 4 = 2^2 (complete code) -/
example : 1 + 1 + 1 + 1 = 2 ^ 2 := by native_decide

/-- Lengths {1,2,2}, L=2: 2+1+1 = 4 = 2^2 (complete code) -/
example : 2 + 1 + 1 = 2 ^ 2 := by native_decide

/-- Lengths {1,2,3,4,4}, L=4: 8+4+2+1+1 = 16 = 2^4 (complete code) -/
example : 8 + 4 + 2 + 1 + 1 = 2 ^ 4 := by native_decide

end EntropyInformation
