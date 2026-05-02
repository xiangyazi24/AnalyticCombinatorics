import Mathlib.Tactic

set_option linter.style.nativeDecide false

open Finset

namespace PolynomialMethods

/-!
# Polynomial Methods in Generating Functions (Chapter I)

Numerical verifications of classical generating-function identities from
Flajolet–Sedgewick Chapter I, covering Fibonacci/Cassini, Catalan recurrences,
Vandermonde-type convolutions, pentagonal numbers, binomial sums, and
factorial/central-binomial bounds.
-/

/-! ## 1. Fibonacci and Cassini's Identity -/

/-!
Cassini's identity: F(n-1)*F(n+1) - F(n)^2 = (-1)^n.
In ℕ, for odd n: F(n-1)*F(n+1) + 1 = F(n)^2.
For even n≥2: F(n-1)*F(n+1) = F(n)^2 + 1.
-/

-- Odd n (n=1,3,5,7,9): F(n-1)*F(n+1) + 1 = F(n)^2
example : Nat.fib 0 * Nat.fib 2 + 1 = Nat.fib 1 ^ 2 := by native_decide
example : Nat.fib 2 * Nat.fib 4 + 1 = Nat.fib 3 ^ 2 := by native_decide
example : Nat.fib 4 * Nat.fib 6 + 1 = Nat.fib 5 ^ 2 := by native_decide
example : Nat.fib 6 * Nat.fib 8 + 1 = Nat.fib 7 ^ 2 := by native_decide
example : Nat.fib 8 * Nat.fib 10 + 1 = Nat.fib 9 ^ 2 := by native_decide

-- Even n≥2 (n=2,4,6,8,10): F(n-1)*F(n+1) = F(n)^2 + 1
example : Nat.fib 1 * Nat.fib 3 = Nat.fib 2 ^ 2 + 1 := by native_decide
example : Nat.fib 3 * Nat.fib 5 = Nat.fib 4 ^ 2 + 1 := by native_decide
example : Nat.fib 5 * Nat.fib 7 = Nat.fib 6 ^ 2 + 1 := by native_decide
example : Nat.fib 7 * Nat.fib 9 = Nat.fib 8 ^ 2 + 1 := by native_decide
example : Nat.fib 9 * Nat.fib 11 = Nat.fib 10 ^ 2 + 1 := by native_decide

/-- Cassini's identity for odd indices 1,3,5,7,9 bundled. -/
theorem cassini_odd :
    Nat.fib 0 * Nat.fib 2 + 1 = Nat.fib 1 ^ 2 ∧
    Nat.fib 2 * Nat.fib 4 + 1 = Nat.fib 3 ^ 2 ∧
    Nat.fib 4 * Nat.fib 6 + 1 = Nat.fib 5 ^ 2 ∧
    Nat.fib 6 * Nat.fib 8 + 1 = Nat.fib 7 ^ 2 ∧
    Nat.fib 8 * Nat.fib 10 + 1 = Nat.fib 9 ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- Cassini's identity for even indices 2,4,6,8,10 bundled. -/
theorem cassini_even :
    Nat.fib 1 * Nat.fib 3 = Nat.fib 2 ^ 2 + 1 ∧
    Nat.fib 3 * Nat.fib 5 = Nat.fib 4 ^ 2 + 1 ∧
    Nat.fib 5 * Nat.fib 7 = Nat.fib 6 ^ 2 + 1 ∧
    Nat.fib 7 * Nat.fib 9 = Nat.fib 8 ^ 2 + 1 ∧
    Nat.fib 9 * Nat.fib 11 = Nat.fib 10 ^ 2 + 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## 2. Catalan Number Identities -/

/-- Catalan number via the binomial formula C(n) = C(2n,n)/(n+1). -/
def catalan (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

/-- Alternative form: C(n) = C(2n,n) - C(2n,n+1). -/
theorem catalan_alt_form_0 : catalan 0 = Nat.choose 0 0 - Nat.choose 0 1 := by native_decide
theorem catalan_alt_form_1 : catalan 1 = Nat.choose 2 1 - Nat.choose 2 2 := by native_decide
theorem catalan_alt_form_2 : catalan 2 = Nat.choose 4 2 - Nat.choose 4 3 := by native_decide
theorem catalan_alt_form_3 : catalan 3 = Nat.choose 6 3 - Nat.choose 6 4 := by native_decide
theorem catalan_alt_form_4 : catalan 4 = Nat.choose 8 4 - Nat.choose 8 5 := by native_decide
theorem catalan_alt_form_5 : catalan 5 = Nat.choose 10 5 - Nat.choose 10 6 := by native_decide
theorem catalan_alt_form_6 : catalan 6 = Nat.choose 12 6 - Nat.choose 12 7 := by native_decide
theorem catalan_alt_form_7 : catalan 7 = Nat.choose 14 7 - Nat.choose 14 8 := by native_decide
theorem catalan_alt_form_8 : catalan 8 = Nat.choose 16 8 - Nat.choose 16 9 := by native_decide

/-- Catalan recurrence: (n+2)*C(n+1) = 2*(2n+1)*C(n). Verified for n=0..8. -/
theorem catalan_recurrence_0 : (0 + 2) * catalan 1 = 2 * (2 * 0 + 1) * catalan 0 := by
  native_decide
theorem catalan_recurrence_1 : (1 + 2) * catalan 2 = 2 * (2 * 1 + 1) * catalan 1 := by
  native_decide
theorem catalan_recurrence_2 : (2 + 2) * catalan 3 = 2 * (2 * 2 + 1) * catalan 2 := by
  native_decide
theorem catalan_recurrence_3 : (3 + 2) * catalan 4 = 2 * (2 * 3 + 1) * catalan 3 := by
  native_decide
theorem catalan_recurrence_4 : (4 + 2) * catalan 5 = 2 * (2 * 4 + 1) * catalan 4 := by
  native_decide
theorem catalan_recurrence_5 : (5 + 2) * catalan 6 = 2 * (2 * 5 + 1) * catalan 5 := by
  native_decide
theorem catalan_recurrence_6 : (6 + 2) * catalan 7 = 2 * (2 * 6 + 1) * catalan 6 := by
  native_decide
theorem catalan_recurrence_7 : (7 + 2) * catalan 8 = 2 * (2 * 7 + 1) * catalan 7 := by
  native_decide
theorem catalan_recurrence_8 : (8 + 2) * catalan 9 = 2 * (2 * 8 + 1) * catalan 8 := by
  native_decide

/-! ## 3. Vandermonde Convolution: Σ C(n,k)² = C(2n,n) -/

theorem sum_sq_binom_1 :
    ∑ k ∈ Finset.range 2, (Nat.choose 1 k) ^ 2 = Nat.choose 2 1 := by native_decide
theorem sum_sq_binom_2 :
    ∑ k ∈ Finset.range 3, (Nat.choose 2 k) ^ 2 = Nat.choose 4 2 := by native_decide
theorem sum_sq_binom_3 :
    ∑ k ∈ Finset.range 4, (Nat.choose 3 k) ^ 2 = Nat.choose 6 3 := by native_decide
theorem sum_sq_binom_4 :
    ∑ k ∈ Finset.range 5, (Nat.choose 4 k) ^ 2 = Nat.choose 8 4 := by native_decide
theorem sum_sq_binom_5 :
    ∑ k ∈ Finset.range 6, (Nat.choose 5 k) ^ 2 = Nat.choose 10 5 := by native_decide
theorem sum_sq_binom_6 :
    ∑ k ∈ Finset.range 7, (Nat.choose 6 k) ^ 2 = Nat.choose 12 6 := by native_decide
theorem sum_sq_binom_7 :
    ∑ k ∈ Finset.range 8, (Nat.choose 7 k) ^ 2 = Nat.choose 14 7 := by native_decide
theorem sum_sq_binom_8 :
    ∑ k ∈ Finset.range 9, (Nat.choose 8 k) ^ 2 = Nat.choose 16 8 := by native_decide

/-! ## 4. Pentagonal Numbers -/

/-- Generalized pentagonal number: p(k) = k(3k-1)/2 for k ∈ ℤ. -/
def pentagonal (k : ℤ) : ℤ := k * (3 * k - 1) / 2

theorem pentagonal_pos_1 : pentagonal 1 = 1 := by native_decide
theorem pentagonal_pos_2 : pentagonal 2 = 5 := by native_decide
theorem pentagonal_pos_3 : pentagonal 3 = 12 := by native_decide
theorem pentagonal_pos_4 : pentagonal 4 = 22 := by native_decide
theorem pentagonal_pos_5 : pentagonal 5 = 35 := by native_decide
theorem pentagonal_pos_6 : pentagonal 6 = 51 := by native_decide

theorem pentagonal_neg_1 : pentagonal (-1) = 2 := by native_decide
theorem pentagonal_neg_2 : pentagonal (-2) = 7 := by native_decide
theorem pentagonal_neg_3 : pentagonal (-3) = 15 := by native_decide
theorem pentagonal_neg_4 : pentagonal (-4) = 26 := by native_decide
theorem pentagonal_neg_5 : pentagonal (-5) = 40 := by native_decide

/-! ## 5. Binomial Series at Special Values -/

/-- Sum of binomial coefficients: Σ_{k=0}^n C(n,k) = 2^n. -/
theorem binom_sum_0 : ∑ k ∈ Finset.range 1, Nat.choose 0 k = 2 ^ 0 := by native_decide
theorem binom_sum_1 : ∑ k ∈ Finset.range 2, Nat.choose 1 k = 2 ^ 1 := by native_decide
theorem binom_sum_2 : ∑ k ∈ Finset.range 3, Nat.choose 2 k = 2 ^ 2 := by native_decide
theorem binom_sum_3 : ∑ k ∈ Finset.range 4, Nat.choose 3 k = 2 ^ 3 := by native_decide
theorem binom_sum_4 : ∑ k ∈ Finset.range 5, Nat.choose 4 k = 2 ^ 4 := by native_decide
theorem binom_sum_5 : ∑ k ∈ Finset.range 6, Nat.choose 5 k = 2 ^ 5 := by native_decide
theorem binom_sum_6 : ∑ k ∈ Finset.range 7, Nat.choose 6 k = 2 ^ 6 := by native_decide
theorem binom_sum_7 : ∑ k ∈ Finset.range 8, Nat.choose 7 k = 2 ^ 7 := by native_decide
theorem binom_sum_8 : ∑ k ∈ Finset.range 9, Nat.choose 8 k = 2 ^ 8 := by native_decide
theorem binom_sum_9 : ∑ k ∈ Finset.range 10, Nat.choose 9 k = 2 ^ 9 := by native_decide
theorem binom_sum_10 : ∑ k ∈ Finset.range 11, Nat.choose 10 k = 2 ^ 10 := by native_decide
theorem binom_sum_11 : ∑ k ∈ Finset.range 12, Nat.choose 11 k = 2 ^ 11 := by native_decide
theorem binom_sum_12 : ∑ k ∈ Finset.range 13, Nat.choose 12 k = 2 ^ 12 := by native_decide

/-- Even-indexed binomial sum = odd-indexed binomial sum = 2^{n-1} for n≥1.
    Equivalently: Σ_{k even} C(n,k) = 2^{n-1}. -/
theorem binom_even_odd_split_1 :
    ∑ k ∈ (Finset.range 2).filter (fun k => k % 2 = 0), Nat.choose 1 k = 2 ^ 0 := by
  native_decide
theorem binom_even_odd_split_2 :
    ∑ k ∈ (Finset.range 3).filter (fun k => k % 2 = 0), Nat.choose 2 k = 2 ^ 1 := by
  native_decide
theorem binom_even_odd_split_3 :
    ∑ k ∈ (Finset.range 4).filter (fun k => k % 2 = 0), Nat.choose 3 k = 2 ^ 2 := by
  native_decide
theorem binom_even_odd_split_4 :
    ∑ k ∈ (Finset.range 5).filter (fun k => k % 2 = 0), Nat.choose 4 k = 2 ^ 3 := by
  native_decide
theorem binom_even_odd_split_5 :
    ∑ k ∈ (Finset.range 6).filter (fun k => k % 2 = 0), Nat.choose 5 k = 2 ^ 4 := by
  native_decide
theorem binom_even_odd_split_6 :
    ∑ k ∈ (Finset.range 7).filter (fun k => k % 2 = 0), Nat.choose 6 k = 2 ^ 5 := by
  native_decide
theorem binom_even_odd_split_7 :
    ∑ k ∈ (Finset.range 8).filter (fun k => k % 2 = 0), Nat.choose 7 k = 2 ^ 6 := by
  native_decide
theorem binom_even_odd_split_8 :
    ∑ k ∈ (Finset.range 9).filter (fun k => k % 2 = 0), Nat.choose 8 k = 2 ^ 7 := by
  native_decide

/-! ## 6. Factorial and Central Binomial Bounds -/

/-- n! * n! ≤ (2n)! for n=1..10. -/
example : Nat.factorial 1 * Nat.factorial 1 ≤ Nat.factorial 2 := by native_decide
example : Nat.factorial 2 * Nat.factorial 2 ≤ Nat.factorial 4 := by native_decide
example : Nat.factorial 3 * Nat.factorial 3 ≤ Nat.factorial 6 := by native_decide
example : Nat.factorial 4 * Nat.factorial 4 ≤ Nat.factorial 8 := by native_decide
example : Nat.factorial 5 * Nat.factorial 5 ≤ Nat.factorial 10 := by native_decide
example : Nat.factorial 6 * Nat.factorial 6 ≤ Nat.factorial 12 := by native_decide
example : Nat.factorial 7 * Nat.factorial 7 ≤ Nat.factorial 14 := by native_decide
example : Nat.factorial 8 * Nat.factorial 8 ≤ Nat.factorial 16 := by native_decide
example : Nat.factorial 9 * Nat.factorial 9 ≤ Nat.factorial 18 := by native_decide
example : Nat.factorial 10 * Nat.factorial 10 ≤ Nat.factorial 20 := by native_decide

/-- Central binomial coefficient bound: C(2n,n) ≤ 4^n, i.e., (2n)! ≤ 4^n * (n!)^2. -/
theorem central_binom_bound_1 : Nat.choose 2 1 ≤ 4 ^ 1 := by native_decide
theorem central_binom_bound_2 : Nat.choose 4 2 ≤ 4 ^ 2 := by native_decide
theorem central_binom_bound_3 : Nat.choose 6 3 ≤ 4 ^ 3 := by native_decide
theorem central_binom_bound_4 : Nat.choose 8 4 ≤ 4 ^ 4 := by native_decide
theorem central_binom_bound_5 : Nat.choose 10 5 ≤ 4 ^ 5 := by native_decide
theorem central_binom_bound_6 : Nat.choose 12 6 ≤ 4 ^ 6 := by native_decide
theorem central_binom_bound_7 : Nat.choose 14 7 ≤ 4 ^ 7 := by native_decide
theorem central_binom_bound_8 : Nat.choose 16 8 ≤ 4 ^ 8 := by native_decide

/-- Equivalent formulation: (2n)! ≤ 4^n * (n!)^2 for n=1..8. -/
example : Nat.factorial 2 ≤ 4 ^ 1 * (Nat.factorial 1) ^ 2 := by native_decide
example : Nat.factorial 4 ≤ 4 ^ 2 * (Nat.factorial 2) ^ 2 := by native_decide
example : Nat.factorial 6 ≤ 4 ^ 3 * (Nat.factorial 3) ^ 2 := by native_decide
example : Nat.factorial 8 ≤ 4 ^ 4 * (Nat.factorial 4) ^ 2 := by native_decide
example : Nat.factorial 10 ≤ 4 ^ 5 * (Nat.factorial 5) ^ 2 := by native_decide
example : Nat.factorial 12 ≤ 4 ^ 6 * (Nat.factorial 6) ^ 2 := by native_decide
example : Nat.factorial 14 ≤ 4 ^ 7 * (Nat.factorial 7) ^ 2 := by native_decide
example : Nat.factorial 16 ≤ 4 ^ 8 * (Nat.factorial 8) ^ 2 := by native_decide

end PolynomialMethods
