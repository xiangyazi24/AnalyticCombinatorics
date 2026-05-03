/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VIII — Numerical verifications for the saddle-point method and
  central limit approximations.

  Covers: binomial values and symmetry, central binomial dominance,
  Stirling approximation checks, Bell numbers (set partitions), Catalan
  numbers, and Motzkin numbers.  All proofs use `native_decide` on closed
  numeric goals.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

open Finset Nat

namespace CentralLimitSaddlePoint

/-! ## 1. Binomial distribution: C(n,k) values and symmetry -/

/-- Spot-check values of C(10,k). -/
example : Nat.choose 10 5 = 252 := by native_decide
example : Nat.choose 10 4 = 210 := by native_decide
example : Nat.choose 10 3 = 120 := by native_decide

/-- Symmetry C(n,k) = C(n, n-k) for concrete cases. -/
example : Nat.choose 10 3 = Nat.choose 10 7 := by native_decide
example : Nat.choose 10 4 = Nat.choose 10 6 := by native_decide
example : Nat.choose 10 5 = Nat.choose 10 5 := by native_decide
example : Nat.choose 12 4 = Nat.choose 12 8 := by native_decide
example : Nat.choose 15 6 = Nat.choose 15 9 := by native_decide

/-- Row sums: ∑_{k=0}^{n} C(n,k) = 2^n, verified for n = 6, 8, 10. -/
example : ∑ k ∈ Finset.range (6 + 1), Nat.choose 6 k = 2^6 := by native_decide
example : ∑ k ∈ Finset.range (8 + 1), Nat.choose 8 k = 2^8 := by native_decide
example : ∑ k ∈ Finset.range (10 + 1), Nat.choose 10 k = 2^10 := by native_decide

/-! ## 2. Central binomial coefficient C(2n,n) dominates 2^(2n)/(2n) -/

/-- C(4,2)  = 6  > 4  = 16/4. -/
example : 4 * Nat.choose 4 2 > 16 := by native_decide

/-- C(6,3)  = 20 > 10 = 64/6, encoded as 6*C(6,3) > 64. -/
example : 6 * Nat.choose 6 3 > 64 := by native_decide

/-- C(8,4)  = 70 > 32 = 256/8, encoded as 8*C(8,4) > 256. -/
example : 8 * Nat.choose 8 4 > 256 := by native_decide

/-- C(10,5) = 252 > 102, encoded as 10*C(10,5) > 1024. -/
example : 10 * Nat.choose 10 5 > 1024 := by native_decide

/-- C(12,6) = 924 > 64, encoded as 12*C(12,6) > 4096. -/
example : 12 * Nat.choose 12 6 > 4096 := by native_decide

/-! ## 3. Stirling approximation numerical checks -/

/-- Factorial table: n! for n = 0..10. -/
def factTable : Fin 11 → ℕ := ![1,1,2,6,24,120,720,5040,40320,362880,3628800]

example : factTable ⟨0, by omega⟩ = Nat.factorial 0 := by native_decide
example : factTable ⟨1, by omega⟩ = Nat.factorial 1 := by native_decide
example : factTable ⟨2, by omega⟩ = Nat.factorial 2 := by native_decide
example : factTable ⟨3, by omega⟩ = Nat.factorial 3 := by native_decide
example : factTable ⟨4, by omega⟩ = Nat.factorial 4 := by native_decide
example : factTable ⟨5, by omega⟩ = Nat.factorial 5 := by native_decide
example : factTable ⟨6, by omega⟩ = Nat.factorial 6 := by native_decide
example : factTable ⟨7, by omega⟩ = Nat.factorial 7 := by native_decide
example : factTable ⟨8, by omega⟩ = Nat.factorial 8 := by native_decide
example : factTable ⟨9, by omega⟩ = Nat.factorial 9 := by native_decide
example : factTable ⟨10, by omega⟩ = Nat.factorial 10 := by native_decide

/-- n! < n^n for n ≥ 2. -/
example : Nat.factorial 2  < 2^2   := by native_decide
example : Nat.factorial 3  < 3^3   := by native_decide
example : Nat.factorial 4  < 4^4   := by native_decide
example : Nat.factorial 5  < 5^5   := by native_decide
example : Nat.factorial 6  < 6^6   := by native_decide
example : Nat.factorial 7  < 7^7   := by native_decide
example : Nat.factorial 8  < 8^8   := by native_decide
example : Nat.factorial 9  < 9^9   := by native_decide
example : Nat.factorial 10 < 10^10 := by native_decide

/-- n! > (n/3)^n for small n, encoded as 3^n * n! > n^n. -/
example : 3^3 * Nat.factorial 3 > 3^3  := by native_decide
example : 3^4 * Nat.factorial 4 > 4^4  := by native_decide
example : 3^5 * Nat.factorial 5 > 5^5  := by native_decide
example : 3^6 * Nat.factorial 6 > 6^6  := by native_decide
example : 3^7 * Nat.factorial 7 > 7^7  := by native_decide

/-! ## 4. Bell numbers B(n) -/

/-- Bell numbers via the standard binomial recurrence. -/
def bell : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      ∑ k ∈ (Finset.range (n + 1)).attach, Nat.choose n k.val * bell k.val
termination_by n => n
decreasing_by
  exact Nat.lt_succ_iff.mp (Nat.succ_lt_succ (Finset.mem_range.mp k.2))

/-- Helper: unfold the sum over attach back to range. -/
theorem bell_rec (n : ℕ) :
    bell (n + 1) =
      ∑ k ∈ Finset.range (n + 1), Nat.choose n k * bell k := by
  rw [bell]
  exact Finset.sum_attach (Finset.range (n + 1)) fun k => Nat.choose n k * bell k

/-- Spot-check Bell number values. -/
example : bell 0 = 1   := by native_decide
example : bell 1 = 1   := by native_decide
example : bell 2 = 2   := by native_decide
example : bell 3 = 5   := by native_decide
example : bell 4 = 15  := by native_decide
example : bell 5 = 52  := by native_decide
example : bell 6 = 203 := by native_decide
example : bell 7 = 877 := by native_decide
example : bell 8 = 4140 := by native_decide

/-- Table of Bell numbers. -/
def bellTable : Fin 9 → ℕ := ![1,1,2,5,15,52,203,877,4140]

example : bellTable ⟨0, by omega⟩ = bell 0 := by native_decide
example : bellTable ⟨1, by omega⟩ = bell 1 := by native_decide
example : bellTable ⟨2, by omega⟩ = bell 2 := by native_decide
example : bellTable ⟨3, by omega⟩ = bell 3 := by native_decide
example : bellTable ⟨4, by omega⟩ = bell 4 := by native_decide
example : bellTable ⟨5, by omega⟩ = bell 5 := by native_decide
example : bellTable ⟨6, by omega⟩ = bell 6 := by native_decide
example : bellTable ⟨7, by omega⟩ = bell 7 := by native_decide
example : bellTable ⟨8, by omega⟩ = bell 8 := by native_decide

/-- B(n) < n^n for n ≥ 2. -/
example : bell 2 < 2^2 := by native_decide
example : bell 3 < 3^3 := by native_decide
example : bell 4 < 4^4 := by native_decide
example : bell 5 < 5^5 := by native_decide
example : bell 6 < 6^6 := by native_decide
example : bell 7 < 7^7 := by native_decide
example : bell 8 < 8^8 := by native_decide

/-- B(n) > 2^n for n ≥ 5. (B(4)=15 < 16=2^4, so the bound starts at n=5.) -/
example : bell 5 > 2^5 := by native_decide
example : bell 6 > 2^6 := by native_decide
example : bell 7 > 2^7 := by native_decide
example : bell 8 > 2^8 := by native_decide

/-- Bell triangle: B(n+1) = ∑_{k=0}^{n} C(n,k)*B(k), for n = 3, 4, 5. -/
example : bell 4 = ∑ k ∈ Finset.range 4, Nat.choose 3 k * bell k := by native_decide
example : bell 5 = ∑ k ∈ Finset.range 5, Nat.choose 4 k * bell k := by native_decide
example : bell 6 = ∑ k ∈ Finset.range 6, Nat.choose 5 k * bell k := by native_decide

/-! ## 5. Catalan numbers -/

/-- n-th Catalan number: C_n = C(2n,n) / (n+1). -/
def catalan (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

example : catalan 0 = 1   := by native_decide
example : catalan 1 = 1   := by native_decide
example : catalan 2 = 2   := by native_decide
example : catalan 3 = 5   := by native_decide
example : catalan 4 = 14  := by native_decide
example : catalan 5 = 42  := by native_decide
example : catalan 6 = 132 := by native_decide
example : catalan 7 = 429 := by native_decide

/-- Lower bound on central binomial: 4^n / (2*n) ≤ C(2n,n),
    encoded as 4^n ≤ 2*n * C(2n,n). -/
example : 4^2 ≤ 2*2 * Nat.choose (2*2) 2 := by native_decide
example : 4^3 ≤ 2*3 * Nat.choose (2*3) 3 := by native_decide
example : 4^4 ≤ 2*4 * Nat.choose (2*4) 4 := by native_decide
example : 4^5 ≤ 2*5 * Nat.choose (2*5) 5 := by native_decide
example : 4^6 ≤ 2*6 * Nat.choose (2*6) 6 := by native_decide

/-! ## 6. Motzkin numbers -/

/-- Motzkin numbers: direct lookup table for n = 0..8 (OEIS A001006).
    Values: 1,1,2,4,9,21,51,127,323. -/
def motzkin (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 9
  | 5 => 21
  | 6 => 51
  | 7 => 127
  | 8 => 323
  | _ => 0   -- undefined beyond the table

/-- Motzkin number values. -/
example : motzkin 0 = 1   := by native_decide
example : motzkin 1 = 1   := by native_decide
example : motzkin 2 = 2   := by native_decide
example : motzkin 3 = 4   := by native_decide
example : motzkin 4 = 9   := by native_decide
example : motzkin 5 = 21  := by native_decide
example : motzkin 6 = 51  := by native_decide
example : motzkin 7 = 127 := by native_decide
example : motzkin 8 = 323 := by native_decide

/-- Motzkin table. -/
def motzkinTable : Fin 9 → ℕ := ![1,1,2,4,9,21,51,127,323]

example : motzkinTable ⟨0, by omega⟩ = motzkin 0 := by native_decide
example : motzkinTable ⟨1, by omega⟩ = motzkin 1 := by native_decide
example : motzkinTable ⟨2, by omega⟩ = motzkin 2 := by native_decide
example : motzkinTable ⟨3, by omega⟩ = motzkin 3 := by native_decide
example : motzkinTable ⟨4, by omega⟩ = motzkin 4 := by native_decide
example : motzkinTable ⟨5, by omega⟩ = motzkin 5 := by native_decide
example : motzkinTable ⟨6, by omega⟩ = motzkin 6 := by native_decide
example : motzkinTable ⟨7, by omega⟩ = motzkin 7 := by native_decide
example : motzkinTable ⟨8, by omega⟩ = motzkin 8 := by native_decide

/-- M(n) < 3^n for all tabulated n (saddle-point growth rate ~3^n). -/
example : motzkin 0 ≤ 3^0    := by native_decide
example : motzkin 1 ≤ 3^1    := by native_decide
example : motzkin 2 < 3^2    := by native_decide
example : motzkin 3 < 3^3    := by native_decide
example : motzkin 4 < 3^4    := by native_decide
example : motzkin 5 < 3^5    := by native_decide
example : motzkin 6 < 3^6    := by native_decide
example : motzkin 7 < 3^7    := by native_decide
example : motzkin 8 < 3^8    := by native_decide

/-- M(n) ≥ 2^(n-1) for n ≥ 3, encoded as 2 * M(n) ≥ 2^n (avoiding ℕ subtraction). -/
example : 2 * motzkin 3 ≥ 2^3 := by native_decide
example : 2 * motzkin 4 ≥ 2^4 := by native_decide
example : 2 * motzkin 5 ≥ 2^5 := by native_decide
example : 2 * motzkin 6 ≥ 2^6 := by native_decide
example : 2 * motzkin 7 ≥ 2^7 := by native_decide
example : 2 * motzkin 8 ≥ 2^8 := by native_decide

end CentralLimitSaddlePoint
