/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter IV — Ordinary Generating Function Applications

  OGF coefficient extraction and combinatorial applications:
  geometric series, negative binomial / multiset coefficients,
  Fibonacci via Cassini's identity, partial-sum GFs, convolution,
  and Catalan numbers.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

open Finset Nat

namespace OrdinaryGFApplications

/-! ## 1. Geometric series coefficients

  [z^n] 1/(1-rz) = r^n.
-/

/-- `geoCoeff r n = r^n` is the n-th coefficient of 1/(1-rz). -/
def geoCoeff (r n : ℕ) : ℕ := r ^ n

-- Spot checks
example : geoCoeff 2 10 = 1024 := by native_decide
example : geoCoeff 3 5  = 243  := by native_decide
example : geoCoeff 1 7  = 1    := by native_decide
example : geoCoeff 0 3  = 0    := by native_decide
example : geoCoeff 5 0  = 1    := by native_decide

/-- geoCoeff satisfies the recurrence r^(n+1) = r * r^n. -/
theorem geoCoeff_rec (r n : ℕ) : geoCoeff r (n + 1) = r * geoCoeff r n := by
  simp [geoCoeff, pow_succ, mul_comm]

/-! ## 2. Negative binomial / multiset coefficients

  [z^n] 1/(1-z)^k = C(n+k-1, k-1) = C(n+k-1, n).

  Special case k=0: the constant series 1, so coeff is 1 at n=0 and 0 elsewhere.
-/

/-- Multiset coefficient: number of k-multisets of size n. -/
def negBinomCoeff (k n : ℕ) : ℕ :=
  if k = 0 then (if n = 0 then 1 else 0)
  else Nat.choose (n + k - 1) n

-- k=1: 1/(1-z), coefficients are all 1
example : negBinomCoeff 1 0 = 1 := by native_decide
example : negBinomCoeff 1 5 = 1 := by native_decide
example : negBinomCoeff 1 9 = 1 := by native_decide

-- k=2: 1/(1-z)^2, [z^n] = n+1
example : negBinomCoeff 2 0 = 1 := by native_decide
example : negBinomCoeff 2 1 = 2 := by native_decide
example : negBinomCoeff 2 2 = 3 := by native_decide
example : negBinomCoeff 2 3 = 4 := by native_decide
example : negBinomCoeff 2 4 = 5 := by native_decide
example : negBinomCoeff 2 5 = 6 := by native_decide
example : negBinomCoeff 2 6 = 7 := by native_decide
example : negBinomCoeff 2 7 = 8 := by native_decide
example : negBinomCoeff 2 8 = 9 := by native_decide

-- k=3: 1/(1-z)^3, [z^n] = C(n+2,2) = (n+1)(n+2)/2
example : negBinomCoeff 3 0 = 1  := by native_decide
example : negBinomCoeff 3 1 = 3  := by native_decide
example : negBinomCoeff 3 2 = 6  := by native_decide
example : negBinomCoeff 3 3 = 10 := by native_decide
example : negBinomCoeff 3 4 = 15 := by native_decide
example : negBinomCoeff 3 5 = 21 := by native_decide
example : negBinomCoeff 3 6 = 28 := by native_decide

-- k=0 boundary
example : negBinomCoeff 0 0 = 1 := by native_decide
example : negBinomCoeff 0 3 = 0 := by native_decide

/-- For k ≥ 1, negBinomCoeff matches the closed form C(n+k-1, n). -/
theorem negBinomCoeff_eq (k n : ℕ) (hk : k ≠ 0) :
    negBinomCoeff k n = Nat.choose (n + k - 1) n := by
  simp [negBinomCoeff, hk]

/-- For k=2, the coefficient is n+1. Verified for n=0..19. -/
example : ∀ n ∈ Finset.range 20, negBinomCoeff 2 n = n + 1 := by native_decide

/-! ## 3. Fibonacci GF and Cassini's identity

  The GF of Fibonacci is z/(1-z-z^2), so [z^n] = Nat.fib n.

  Cassini's identity: fib(n-1)*fib(n+1) - fib(n)^2 = (-1)^n.
  In ℕ-arithmetic (no negatives):
    * For even m≥2: fib(m)^2 + 1 = fib(m-1)*fib(m+1)
    * For odd  m≥1: fib(m-1)*fib(m+1) + 1 = fib(m)^2
-/

-- Fibonacci values: Nat.fib 0 = 0, Nat.fib 1 = 1, etc.
example : Nat.fib 0  = 0  := by native_decide
example : Nat.fib 1  = 1  := by native_decide
example : Nat.fib 2  = 1  := by native_decide
example : Nat.fib 3  = 2  := by native_decide
example : Nat.fib 4  = 3  := by native_decide
example : Nat.fib 5  = 5  := by native_decide
example : Nat.fib 6  = 8  := by native_decide
example : Nat.fib 7  = 13 := by native_decide
example : Nat.fib 8  = 21 := by native_decide
example : Nat.fib 9  = 34 := by native_decide
example : Nat.fib 10 = 55 := by native_decide

-- Cassini's identity — even index instances (fib(m)^2 + 1 = fib(m-1)*fib(m+1) for even m≥2):
-- m=2: 1^2 + 1 = 2 = 1*2 ✓
example : Nat.fib 2 ^ 2 + 1 = Nat.fib 1 * Nat.fib 3   := by native_decide
-- m=4: 3^2 + 1 = 10 = 2*5 ✓
example : Nat.fib 4 ^ 2 + 1 = Nat.fib 3 * Nat.fib 5   := by native_decide
-- m=6: 8^2 + 1 = 65 = 5*13 ✓
example : Nat.fib 6 ^ 2 + 1 = Nat.fib 5 * Nat.fib 7   := by native_decide
-- m=8: 21^2 + 1 = 442 = 13*34 ✓
example : Nat.fib 8 ^ 2 + 1 = Nat.fib 7 * Nat.fib 9   := by native_decide
example : Nat.fib 10 ^ 2 + 1 = Nat.fib 9 * Nat.fib 11 := by native_decide

-- Cassini's identity — odd index instances (fib(m-1)*fib(m+1) + 1 = fib(m)^2 for odd m≥1):
-- m=1: fib(0)*fib(2)+1 = 0+1=1 = fib(1)^2=1 ✓
example : Nat.fib 0 * Nat.fib 2 + 1 = Nat.fib 1 ^ 2  := by native_decide
-- m=3: fib(2)*fib(4)+1 = 1*3+1=4 = fib(3)^2=4 ✓
example : Nat.fib 2 * Nat.fib 4 + 1 = Nat.fib 3 ^ 2  := by native_decide
-- m=5: fib(4)*fib(6)+1 = 3*8+1=25 = fib(5)^2=25 ✓
example : Nat.fib 4 * Nat.fib 6 + 1 = Nat.fib 5 ^ 2  := by native_decide
-- m=7: fib(6)*fib(8)+1 = 8*21+1=169 = 13^2 ✓
example : Nat.fib 6 * Nat.fib 8 + 1 = Nat.fib 7 ^ 2  := by native_decide
-- m=9: fib(8)*fib(10)+1 = 21*55+1=1156 = 34^2 ✓
example : Nat.fib 8 * Nat.fib 10 + 1 = Nat.fib 9 ^ 2 := by native_decide

-- Named instances from the spec:
example : Nat.fib 4 * Nat.fib 6 + 1 = Nat.fib 5 ^ 2 := by native_decide  -- 3*8+1=25=5^2
example : Nat.fib 5 * Nat.fib 7 = Nat.fib 6 ^ 2 + 1 := by native_decide  -- 5*13=65=64+1

/-! ## 4. Partial sums: [z^n] f(z)/(1-z) = Σ_{k=0}^n a_k

  Multiplying by 1/(1-z) accumulates partial sums.
-/

/-- Triangular numbers: T(n) = n*(n+1)/2 = Σ_{k=0}^n k. -/
def triangular (n : ℕ) : ℕ := n * (n + 1) / 2

-- Spot checks: triangular n
example : triangular 0  = 0  := by native_decide
example : triangular 1  = 1  := by native_decide
example : triangular 2  = 3  := by native_decide
example : triangular 3  = 6  := by native_decide
example : triangular 4  = 10 := by native_decide
example : triangular 5  = 15 := by native_decide
example : triangular 6  = 21 := by native_decide
example : triangular 7  = 28 := by native_decide
example : triangular 8  = 36 := by native_decide
example : triangular 9  = 45 := by native_decide
example : triangular 10 = 55 := by native_decide

-- Closed-form match: ∑_{k=0}^n k = triangular n, verified for specific n
example : ∑ k ∈ Finset.range 6,  k = triangular 5  := by native_decide
example : ∑ k ∈ Finset.range 11, k = triangular 10 := by native_decide

-- Partial sums of all-1 sequence equal n+1 (variable n in the open namespace)
example (n : ℕ) : ∑ _k ∈ Finset.range (n + 1), 1 = n + 1 := by simp

-- triangular n equals the Gauss sum Σ_{k=0}^n k
-- We work with 2 * (sum) = n*(n+1) to avoid Nat division in proofs.

/-- Double of the triangular number equals n*(n+1). -/
theorem two_mul_triangular (n : ℕ) : 2 * triangular n = n * (n + 1) := by
  simp only [triangular]
  have hdvd : 2 ∣ n * (n + 1) := (Nat.even_mul_succ_self n).two_dvd
  omega

/-- The double of the partial sum Σ_{k=0}^n k equals n*(n+1). -/
theorem two_mul_sum_range (n : ℕ) :
    2 * ∑ k ∈ Finset.range (n + 1), k = n * (n + 1) := by
  have := Finset.sum_range_id_mul_two (n + 1)
  simp at this
  linarith

theorem triangular_eq_sum (n : ℕ) :
    triangular n = ∑ k ∈ Finset.range (n + 1), k := by
  have h1 := two_mul_triangular n
  have h2 := two_mul_sum_range n
  omega

/-! ## 5. Convolution: [z^n] f(z)*g(z) = Σ_{k=0}^n a_k * b_{n-k}

  Example 1: 1/(1-z)^2 — coefficient n+1.
  Example 2: 1/(1-z) * 1/(1-2z) — coefficient 2^(n+1) - 1.
-/

/-- Finite convolution of two sequences at index n. -/
def conv (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), a k * b (n - k)

-- Conv of all-1 with all-1 = n+1  (i.e., [z^n] 1/(1-z)^2 = n+1)
theorem conv_ones_eq (n : ℕ) :
    conv (fun _ => 1) (fun _ => 1) n = n + 1 := by
  simp [conv]

-- Spot checks for conv of 1 and 2^k = [z^n] 1/(1-z)*1/(1-2z) = 2^(n+1)-1
def twoMinusOne (n : ℕ) : ℕ := 2 ^ (n + 1) - 1

example : twoMinusOne 0 = 1  := by native_decide
example : twoMinusOne 1 = 3  := by native_decide
example : twoMinusOne 2 = 7  := by native_decide
example : twoMinusOne 3 = 15 := by native_decide
example : twoMinusOne 4 = 31 := by native_decide

-- Convolution identity conv(1, 2^k)(n) = 2^(n+1)-1, proved by induction
theorem conv_one_two_eq (n : ℕ) :
    conv (fun _ => 1) (fun k => 2 ^ k) n = twoMinusOne n := by
  simp only [conv, twoMinusOne, one_mul]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero]
    -- rewrite the remaining sum: 2^((n+1)-k) = 2 * 2^(n-k) for k ≤ n
    have hshift : ∑ k ∈ Finset.range (n + 1), 2 ^ (n + 1 - k) =
        2 * ∑ k ∈ Finset.range (n + 1), 2 ^ (n - k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      have hle : k ≤ n := Nat.lt_succ_iff.mp hk
      rw [show n + 1 - k = (n - k) + 1 from by omega]
      ring
    rw [hshift, ih]
    have h : (1 : ℕ) ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
    omega

-- Convolution spot checks verified directly
example : conv (fun _ => 1) (fun k => 2 ^ k) 0 = twoMinusOne 0 := by native_decide
example : conv (fun _ => 1) (fun k => 2 ^ k) 1 = twoMinusOne 1 := by native_decide
example : conv (fun _ => 1) (fun k => 2 ^ k) 2 = twoMinusOne 2 := by native_decide
example : conv (fun _ => 1) (fun k => 2 ^ k) 3 = twoMinusOne 3 := by native_decide
example : conv (fun _ => 1) (fun k => 2 ^ k) 4 = twoMinusOne 4 := by native_decide
example : conv (fun _ => 1) (fun k => 2 ^ k) 5 = twoMinusOne 5 := by native_decide
example : conv (fun _ => 1) (fun k => 2 ^ k) 6 = twoMinusOne 6 := by native_decide
example : conv (fun _ => 1) (fun k => 2 ^ k) 7 = twoMinusOne 7 := by native_decide
example : conv (fun _ => 1) (fun k => 2 ^ k) 8 = twoMinusOne 8 := by native_decide

/-! ## 6. Catalan numbers

  C(z) = (1 - √(1-4z))/(2z), with [z^n]C(z) = C(2n,n)/(n+1).
  The sequence begins: 1, 1, 2, 5, 14, 42, 132, 429, ...
-/

/-- Catalan number: C_n = C(2n,n) / (n+1). -/
def catalan (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

-- Verify the first 8 Catalan numbers
example : catalan 0 = 1   := by native_decide
example : catalan 1 = 1   := by native_decide
example : catalan 2 = 2   := by native_decide
example : catalan 3 = 5   := by native_decide
example : catalan 4 = 14  := by native_decide
example : catalan 5 = 42  := by native_decide
example : catalan 6 = 132 := by native_decide
example : catalan 7 = 429 := by native_decide

-- Catalan recurrence: C_{n+1} = Σ_{k=0}^n C_k * C_{n-k}
-- Verified via conv for small indices
example : conv catalan catalan 0 = catalan 1 := by native_decide
example : conv catalan catalan 1 = catalan 2 := by native_decide
example : conv catalan catalan 2 = catalan 3 := by native_decide
example : conv catalan catalan 3 = catalan 4 := by native_decide
example : conv catalan catalan 4 = catalan 5 := by native_decide
example : conv catalan catalan 5 = catalan 6 := by native_decide

end OrdinaryGFApplications
