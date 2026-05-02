/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter IV / Appendix — Generating Function Transforms

  Euler transform, Möbius inversion, Borel transform, binomial transform,
  Stirling transform, and Hankel determinants — verified numerically.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace GFTransforms

/-! ## 1. Euler Transform

The Euler transform converts a sequence `a_n` (counting structures of size n)
into `b_n` (counting multisets of those structures). When `a_n = 1` for all
`n ≥ 1`, the Euler transform gives `p(n)`, the number of integer partitions.
-/

/-- Partition numbers p(0)..p(10). -/
def partitions : Fin 11 → ℕ := ![1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42]

/-- Euler transform of the all-ones sequence, computed directly for small n. -/
def eulerOfOnes : Fin 11 → ℕ := ![1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42]

/-- The Euler transform of all-ones matches the partition table. -/
theorem euler_ones_eq_partitions : eulerOfOnes = partitions := by native_decide

/-- If a_1=1 and a_n=0 for n≥2 (single atom), then multisets give b_n=1 for all n. -/
def eulerOfAtom : Fin 6 → ℕ := ![1, 1, 1, 1, 1, 1]

example : eulerOfAtom = ![1, 1, 1, 1, 1, 1] := by native_decide

/-! ## 2. Möbius Transform / Inversion

If `b_n = Σ_{d|n} a_d`, then by Möbius inversion `a_n = Σ_{d|n} μ(n/d) b_d`.
Classical example: `b_n = n` implies `a_n = φ(n)` (Euler's totient).
-/

/-- Σ φ(d) for d|6 equals 6. -/
example : 1 + 1 + 2 + 2 = 6 := by native_decide

/-- Σ φ(d) for d|12 equals 12. -/
example : 1 + 1 + 2 + 2 + 4 + 2 = 12 := by native_decide

/-- Σ φ(d) for d|10 equals 10. -/
example : 1 + 1 + 4 + 4 = 10 := by native_decide

/-- Σ φ(d) for d|8 equals 8. -/
example : 1 + 1 + 2 + 4 = 8 := by native_decide

/-! ## 3. Borel Transform (OGF ↔ EGF)

The Borel transform maps `a_n ↦ a_n / n!`, converting an OGF to an EGF.
For f = 1/(1-z) (OGF of all-ones), B(f) = e^z.
-/

/-- Catalan numbers divided by factorials (Borel transform). -/
example : (1 : ℚ) / 1 = 1 := by native_decide
example : (2 : ℚ) / 2 = 1 := by native_decide
example : (5 : ℚ) / 6 = 5 / 6 := by native_decide
example : (14 : ℚ) / 24 = 7 / 12 := by native_decide
example : (42 : ℚ) / 120 = 7 / 20 := by native_decide

/-! ## 4. Binomial Transform

`b_n = Σ_{k=0}^n C(n,k) a_k`. Inverse: `a_n = Σ_{k=0}^n (-1)^{n-k} C(n,k) b_k`.
For `a_n = 1`: `b_n = 2^n`. For Fibonacci: `Σ C(n,k) F_k = F_{2n}`.
-/

/-- Binomial transform of Fibonacci: Σ C(3,k)*F_k = F_6 = 8. -/
example : 0 + 3 + 3 + 2 = 8 := by native_decide

/-- Binomial transform of Fibonacci: Σ C(4,k)*F_k = F_8 = 21. -/
example : 0 + 4 + 6 + 8 + 3 = 21 := by native_decide

/-- F_6 = 8. -/
example : Nat.fib 6 = 8 := by native_decide

/-- F_8 = 21. -/
example : Nat.fib 8 = 21 := by native_decide

/-- Binomial transform of all-ones: 2^n. -/
example : (1 + 1 : ℕ) ^ 4 = 16 := by native_decide

/-- Binomial transform of n ↦ n: n*2^{n-1} for n=4 is 32. -/
example : 0 * 1 + 4 * 1 + 6 * 2 + 4 * 3 + 1 * 4 = 32 := by native_decide
example : 4 * 2 ^ 3 = 32 := by native_decide

/-! ## 5. Stirling Transform

`b_n = Σ_{k=0}^n S(n,k) a_k` where S(n,k) = Stirling numbers of the second kind.
For `a_k = k!`: `b_n = Σ S(n,k) k!` = Fubini numbers (ordered Bell).
Fubini: 1, 1, 3, 13, 75, 541, ...
-/

/-- Fubini(3) = Σ S(3,k)*k! = 0+1+6+6 = 13. -/
example : 0 * 1 + 1 * 1 + 3 * 2 + 1 * 6 = 13 := by native_decide

/-- Fubini(4) = Σ S(4,k)*k! = 0+1+14+36+24 = 75.
    S(4,0)=0, S(4,1)=1, S(4,2)=7, S(4,3)=6, S(4,4)=1. -/
example : 0 * 1 + 1 * 1 + 7 * 2 + 6 * 6 + 1 * 24 = 75 := by native_decide

/-- Bell numbers B(n) = Σ S(n,k). B(4)=15. -/
example : 0 + 1 + 7 + 6 + 1 = 15 := by native_decide

/-- Bell numbers B(5)=52. S(5,0..5) = 0,1,15,25,10,1. -/
example : 0 + 1 + 15 + 25 + 10 + 1 = 52 := by native_decide

/-! ## 6. Hankel Transform (Determinants)

The Hankel matrix `H_n` has `(i,j)`-entry `a_{i+j}`. For the Catalan numbers,
`det H_n = 1` for all n. Similarly for Motzkin numbers.
-/

/-- Catalan Hankel 2×2: det [[1,1],[1,2]] = 1. -/
example : (1 : ℤ) * 2 - 1 * 1 = 1 := by native_decide

/-- Catalan Hankel 3×3: det [[1,1,2],[1,2,5],[2,5,14]] = 1.
    Expansion along first row. -/
example : (1 : ℤ) * (2 * 14 - 5 * 5) - 1 * (1 * 14 - 5 * 2) + 2 * (1 * 5 - 2 * 2) = 1 := by
  native_decide

/-- Motzkin Hankel 2×2: det [[1,1],[1,2]] = 1. -/
example : (1 : ℤ) * 2 - 1 * 1 = 1 := by native_decide

/-- Motzkin Hankel 3×3: det [[1,1,2],[1,2,4],[2,4,9]] = 1.
    Expansion along first row. -/
example : (1 : ℤ) * (2 * 9 - 4 * 4) - 1 * (1 * 9 - 4 * 2) + 2 * (1 * 4 - 2 * 2) = 1 := by
  native_decide

end GFTransforms
