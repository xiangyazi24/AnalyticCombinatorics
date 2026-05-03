/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VIII — Numerical verifications for saddle-point examples.

  Covers: integer partition recurrence, Bell numbers via Stirling,
  involution counts, surjection counts, derangement (subfactorial),
  and factorial-vs-exponential growth bounds.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace SaddlePointExamples

open Finset

/-! ## 1. Integer partitions — Euler pentagonal recurrence -/

/-- The partition numbers p(n) for n = 0..15, from Hardy-Ramanujan table. -/
def partTable : Fin 16 → ℕ :=
  ![1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42, 56, 77, 101, 135, 176]

/-- p(5) = p(4)+p(3)-p(0) via Euler pentagonal recurrence. -/
example : partTable ⟨5, by omega⟩ =
    partTable ⟨4, by omega⟩ + partTable ⟨3, by omega⟩ - partTable ⟨0, by omega⟩ := by
  native_decide

/-- p(6) = p(5)+p(4)-p(1). -/
example : partTable ⟨6, by omega⟩ =
    partTable ⟨5, by omega⟩ + partTable ⟨4, by omega⟩ - partTable ⟨1, by omega⟩ := by
  native_decide

/-- p(7) = p(6)+p(5)-p(2)-p(0) (pentagonal offset 5 reached). -/
example : partTable ⟨7, by omega⟩ =
    partTable ⟨6, by omega⟩ + partTable ⟨5, by omega⟩ -
    partTable ⟨2, by omega⟩ - partTable ⟨0, by omega⟩ := by
  native_decide

/-- p(8) = p(7)+p(6)-p(3)-p(1). -/
example : partTable ⟨8, by omega⟩ =
    partTable ⟨7, by omega⟩ + partTable ⟨6, by omega⟩ -
    partTable ⟨3, by omega⟩ - partTable ⟨1, by omega⟩ := by
  native_decide

/-- p(9) = p(8)+p(7)-p(4)-p(2). -/
example : partTable ⟨9, by omega⟩ =
    partTable ⟨8, by omega⟩ + partTable ⟨7, by omega⟩ -
    partTable ⟨4, by omega⟩ - partTable ⟨2, by omega⟩ := by
  native_decide

/-- p(10) = p(9)+p(8)-p(5)-p(3)  (next pentagonal 12 > 10). -/
example : partTable ⟨10, by omega⟩ =
    partTable ⟨9, by omega⟩ + partTable ⟨8, by omega⟩ -
    partTable ⟨5, by omega⟩ - partTable ⟨3, by omega⟩ := by
  native_decide

/-! ## 2. Set partitions — Bell numbers via Stirling numbers of the 2nd kind -/

/-- Stirling numbers of the second kind, by their standard recurrence.
    S(0,0)=1; S(0,k+1)=0; S(n+1,0)=0;
    S(n+1,k+1) = (k+1)*S(n,k+1) + S(n,k). -/
def stirling2SP : ℕ → ℕ → ℕ
  | 0, 0       => 1
  | 0, _ + 1   => 0
  | _ + 1, 0   => 0
  | n + 1, k + 1 => (k + 1) * stirling2SP n (k + 1) + stirling2SP n k

/-- B_n = ∑_{k=0}^n S(n,k). -/
def bellSP (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), stirling2SP n k

example : bellSP 0 = 1   := by native_decide
example : bellSP 1 = 1   := by native_decide
example : bellSP 2 = 2   := by native_decide
example : bellSP 3 = 5   := by native_decide
example : bellSP 4 = 15  := by native_decide
example : bellSP 5 = 52  := by native_decide
example : bellSP 6 = 203 := by native_decide
example : bellSP 7 = 877 := by native_decide

/-- Batch verification of bellSP for n = 0..7. -/
theorem bellSP_values_0_7 :
    bellSP 0 = 1 ∧ bellSP 1 = 1 ∧ bellSP 2 = 2 ∧ bellSP 3 = 5 ∧
    bellSP 4 = 15 ∧ bellSP 5 = 52 ∧ bellSP 6 = 203 ∧ bellSP 7 = 877 := by
  native_decide

/-! ## 3. Involution count — saddle-point example -/

/-- Number of involutions of [n]: permutations equal to their own inverse.
    Recurrence: I_0=1, I_1=1, I_{n+2} = I_{n+1} + (n+1)*I_n. -/
def involutionSP : ℕ → ℕ
  | 0     => 1
  | 1     => 1
  | n + 2 => involutionSP (n + 1) + (n + 1) * involutionSP n

example : involutionSP 0 = 1   := by native_decide
example : involutionSP 1 = 1   := by native_decide
example : involutionSP 2 = 2   := by native_decide
example : involutionSP 3 = 4   := by native_decide
example : involutionSP 4 = 10  := by native_decide
example : involutionSP 5 = 26  := by native_decide
example : involutionSP 6 = 76  := by native_decide
example : involutionSP 7 = 232 := by native_decide
example : involutionSP 8 = 764 := by native_decide

/-- Batch verification of involutionSP for n = 0..8. -/
theorem involutionSP_values_0_8 :
    involutionSP 0 = 1 ∧ involutionSP 1 = 1 ∧ involutionSP 2 = 2 ∧
    involutionSP 3 = 4 ∧ involutionSP 4 = 10 ∧ involutionSP 5 = 26 ∧
    involutionSP 6 = 76 ∧ involutionSP 7 = 232 ∧ involutionSP 8 = 764 := by
  native_decide

/-- Alternative formula: I_n = ∑_{j=0}^{⌊n/2⌋} C(n,2j) * (2j-1)!!.
    Verify for n=4: C(4,0)*1 + C(4,2)*1 + C(4,4)*3 = 1+6+3 = 10. -/
example : Nat.choose 4 0 * 1 + Nat.choose 4 2 * 1 + Nat.choose 4 4 * 3 = 10 := by
  native_decide

/-- Same formula for n=5: C(5,0)*1 + C(5,2)*1 + C(5,4)*3 = 1+10+15 = 26. -/
example : Nat.choose 5 0 * 1 + Nat.choose 5 2 * 1 + Nat.choose 5 4 * 3 = 26 := by
  native_decide

/-- Same formula for n=6: C(6,0)*1 + C(6,2)*1 + C(6,4)*3 + C(6,6)*15 = 1+15+45+15 = 76. -/
example : Nat.choose 6 0 * 1 + Nat.choose 6 2 * 1 +
          Nat.choose 6 4 * 3 + Nat.choose 6 6 * 15 = 76 := by
  native_decide

/-! ## 4. Surjection count — inclusion-exclusion via Stirling -/

/-- Number of surjections from an n-set to a k-set = k! * S(n,k). -/
def surjectionCount (n k : ℕ) : ℕ := Nat.factorial k * stirling2SP n k

-- Basic Stirling values needed
example : stirling2SP 3 2 = 3  := by native_decide
example : stirling2SP 4 2 = 7  := by native_decide
example : stirling2SP 4 3 = 6  := by native_decide
example : stirling2SP 4 4 = 1  := by native_decide
example : stirling2SP 5 3 = 25 := by native_decide

-- Surjection counts
example : surjectionCount 3 2 = 6   := by native_decide  -- 2! * 3
example : surjectionCount 3 3 = 6   := by native_decide  -- 3! * 1
example : surjectionCount 4 2 = 14  := by native_decide  -- 2! * 7
example : surjectionCount 4 3 = 36  := by native_decide  -- 3! * 6
example : surjectionCount 4 4 = 24  := by native_decide  -- 4! * 1
example : surjectionCount 5 3 = 150 := by native_decide  -- 3! * 25

/-- Batch verification of surjection counts. -/
theorem surjectionCount_samples :
    surjectionCount 3 2 = 6 ∧ surjectionCount 3 3 = 6 ∧
    surjectionCount 4 2 = 14 ∧ surjectionCount 4 3 = 36 ∧
    surjectionCount 4 4 = 24 ∧ surjectionCount 5 3 = 150 := by
  native_decide

/-! ## 5. Derangement (subfactorial) — D_n = (n-1)*(D_{n-1}+D_{n-2}) -/

/-- Subfactorial / derangement numbers.
    D_0=1, D_1=0, D_{n+2} = (n+1)*(D_{n+1}+D_n). -/
def subfactorial : ℕ → ℕ
  | 0     => 1
  | 1     => 0
  | n + 2 => (n + 1) * (subfactorial (n + 1) + subfactorial n)

example : subfactorial 0 = 1    := by native_decide
example : subfactorial 1 = 0    := by native_decide
example : subfactorial 2 = 1    := by native_decide
example : subfactorial 3 = 2    := by native_decide
example : subfactorial 4 = 9    := by native_decide
example : subfactorial 5 = 44   := by native_decide
example : subfactorial 6 = 265  := by native_decide
example : subfactorial 7 = 1854 := by native_decide

/-- Batch verification of subfactorial for n = 0..7. -/
theorem subfactorial_values_0_7 :
    subfactorial 0 = 1 ∧ subfactorial 1 = 0 ∧ subfactorial 2 = 1 ∧
    subfactorial 3 = 2 ∧ subfactorial 4 = 9 ∧ subfactorial 5 = 44 ∧
    subfactorial 6 = 265 ∧ subfactorial 7 = 1854 := by
  native_decide

/-- Verify the recurrence D_n = n*D_{n-1} + (-1)^n in ℕ.
    For even n: D_n = n*D_{n-1} + 1. -/
example : subfactorial 2 = 2 * subfactorial 1 + 1 := by native_decide  -- 1 = 0+1
example : subfactorial 4 = 4 * subfactorial 3 + 1 := by native_decide  -- 9 = 8+1
example : subfactorial 6 = 6 * subfactorial 5 + 1 := by native_decide  -- 265 = 264+1

/-- For odd n: D_n = n*D_{n-1} - 1. -/
example : subfactorial 3 + 1 = 3 * subfactorial 2 := by native_decide  -- 3 = 3
example : subfactorial 5 + 1 = 5 * subfactorial 4 := by native_decide  -- 45 = 45
example : subfactorial 7 + 1 = 7 * subfactorial 6 := by native_decide  -- 1855 = 1855

/-! ## 6. Factorial vs exponential growth — saddle point at z=n for n! -/

/-- 10! > 3^10: factorial eventually dominates exponential base 3. -/
example : Nat.factorial 10 > 3 ^ 10 := by native_decide

/-- 12! > 4^12: factorial dominates base 4 at n=12. -/
example : Nat.factorial 12 > 4 ^ 12 := by native_decide

/-- 15! > 5^15: factorial dominates base 5 at n=15. -/
example : Nat.factorial 15 > 5 ^ 15 := by native_decide

/-- Batch: factorial dominates fixed-base exponentials. -/
theorem factorial_dominates_exp :
    Nat.factorial 10 > 3 ^ 10 ∧
    Nat.factorial 12 > 4 ^ 12 ∧
    Nat.factorial 15 > 5 ^ 15 := by
  native_decide

/-- Cross-checks: 8! > 2^8 * 4!  (40320 > 6144). -/
example : Nat.factorial 8 > 2 ^ 8 * Nat.factorial 4 := by native_decide

/-- 10! > (5!)^2  (3628800 > 14400). -/
example : Nat.factorial 10 > (Nat.factorial 5) ^ 2 := by native_decide

/-- Super-factorial growth: n! > (n/2)!^2 for n=10. -/
example : Nat.factorial 10 > (Nat.factorial 5) ^ 2 := by native_decide

end SaddlePointExamples
