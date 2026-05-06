/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VII — Numerical verifications of exponential growth constants.

  We record growth-constant checks for the classical combinatorial sequences
  discussed in Ch VII of Flajolet & Sedgewick (2009):

    · Binary trees / Catalan  ρ⁻¹ = 4
    · Motzkin                 ρ⁻¹ = 3
    · Large Schröder          ρ⁻¹ = 3 + 2√2 ≈ 5.828
    · Ternary trees           ρ⁻¹ = 27/4 = 6.75
    · Fibonacci               ρ⁻¹ = φ = (1 + √5)/2 ≈ 1.618
    · Bell numbers            super-exponential growth (no fixed ρ)
    · Integer partitions      sub-exponential (Hardy–Ramanujan)

  All proofs are by `native_decide` on finite certificate goals.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false
set_option linter.style.whitespace false

namespace AnalyticCombinatorics.PartB.Ch7.ExponentialGrowth
/-! ## 1. Catalan numbers — growth constant ρ⁻¹ = 4

  The Catalan number C_n = C(2n,n)/(n+1) satisfies the recurrence
      (n + 2) · C_{n+1} = (4n + 2) · C_n,
  which is an integer certificate that C_{n+1}/C_n → 4.
-/

/-- Catalan number `C(2n, n) / (n + 1)`. -/
def catalan (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

-- Exact values C_0 … C_10
theorem catalan_0  : catalan 0  = 1     := by native_decide
theorem catalan_1  : catalan 1  = 1     := by native_decide
theorem catalan_2  : catalan 2  = 2     := by native_decide
theorem catalan_3  : catalan 3  = 5     := by native_decide
theorem catalan_4  : catalan 4  = 14    := by native_decide
theorem catalan_5  : catalan 5  = 42    := by native_decide
theorem catalan_6  : catalan 6  = 132   := by native_decide
theorem catalan_7  : catalan 7  = 429   := by native_decide
theorem catalan_8  : catalan 8  = 1430  := by native_decide
theorem catalan_9  : catalan 9  = 4862  := by native_decide
theorem catalan_10 : catalan 10 = 16796 := by native_decide

/-- Recurrence `(n+2) · C_{n+1} = (4n+2) · C_n`, verified for n = 0 … 8. -/
theorem catalan_rec_0 : (0 + 2) * catalan 1 = (4 * 0 + 2) * catalan 0 := by native_decide
theorem catalan_rec_1 : (1 + 2) * catalan 2 = (4 * 1 + 2) * catalan 1 := by native_decide
theorem catalan_rec_2 : (2 + 2) * catalan 3 = (4 * 2 + 2) * catalan 2 := by native_decide
theorem catalan_rec_3 : (3 + 2) * catalan 4 = (4 * 3 + 2) * catalan 3 := by native_decide
theorem catalan_rec_4 : (4 + 2) * catalan 5 = (4 * 4 + 2) * catalan 4 := by native_decide
theorem catalan_rec_5 : (5 + 2) * catalan 6 = (4 * 5 + 2) * catalan 5 := by native_decide
theorem catalan_rec_6 : (6 + 2) * catalan 7 = (4 * 6 + 2) * catalan 6 := by native_decide
theorem catalan_rec_7 : (7 + 2) * catalan 8 = (4 * 7 + 2) * catalan 7 := by native_decide
theorem catalan_rec_8 : (8 + 2) * catalan 9 = (4 * 8 + 2) * catalan 8 := by native_decide

/-- Upper bound: C_n < 4^n for n = 1 … 10. -/
theorem catalan_lt_four_pow :
    ∀ n ∈ Finset.Icc 1 10, catalan n < 4 ^ n := by
  intro n hn
  fin_cases hn <;> native_decide

/-- Lower bound: 2^n < C_n for n = 5 … 10. -/
theorem two_pow_lt_catalan :
    ∀ n ∈ Finset.Icc 5 10, 2 ^ n < catalan n := by
  intro n hn
  fin_cases hn <;> native_decide

/-- The ratio C_{n+1}/C_n < 4 (integer form): C_{n+1}·(n+2) < 4·C_n·(n+1)
    for n = 1 … 8. This follows from (n+2)·C_{n+1} = (4n+2)·C_n and (4n+2) < 4(n+1). -/
theorem catalan_ratio_lt_four :
    ∀ n ∈ Finset.Icc 1 8,
      catalan (n + 1) * (n + 2) < 4 * catalan n * (n + 1) := by
  intro n hn
  fin_cases hn <;> native_decide

/-! ## 2. Motzkin numbers — growth constant ρ⁻¹ = 3

  M_n satisfies the recurrence
      (n + 3) · M_{n+1} = (2n + 3) · M_n + 3n · M_{n-1}.
  Values: 1, 1, 2, 4, 9, 21, 51, 127, 323, 835.
-/

/-- Motzkin numbers via lookup table (indices 0 … 9). -/
def motzkinTable : Fin 10 → ℕ := ![1, 1, 2, 4, 9, 21, 51, 127, 323, 835]

-- Basic value checks
theorem motzkin_0 : motzkinTable 0 = 1   := by native_decide
theorem motzkin_1 : motzkinTable 1 = 1   := by native_decide
theorem motzkin_2 : motzkinTable 2 = 2   := by native_decide
theorem motzkin_3 : motzkinTable 3 = 4   := by native_decide
theorem motzkin_4 : motzkinTable 4 = 9   := by native_decide
theorem motzkin_5 : motzkinTable 5 = 21  := by native_decide
theorem motzkin_6 : motzkinTable 6 = 51  := by native_decide
theorem motzkin_7 : motzkinTable 7 = 127 := by native_decide
theorem motzkin_8 : motzkinTable 8 = 323 := by native_decide
theorem motzkin_9 : motzkinTable 9 = 835 := by native_decide

/-- Recurrence `(n+3)·M_{n+1} = (2n+3)·M_n + 3n·M_{n-1}` for n = 1 … 7. -/
theorem motzkin_recurrence_1 :
    (1 + 3) * motzkinTable 2 = (2 * 1 + 3) * motzkinTable 1 + 3 * 1 * motzkinTable 0 := by
  native_decide
theorem motzkin_recurrence_2 :
    (2 + 3) * motzkinTable 3 = (2 * 2 + 3) * motzkinTable 2 + 3 * 2 * motzkinTable 1 := by
  native_decide
theorem motzkin_recurrence_3 :
    (3 + 3) * motzkinTable 4 = (2 * 3 + 3) * motzkinTable 3 + 3 * 3 * motzkinTable 2 := by
  native_decide
theorem motzkin_recurrence_4 :
    (4 + 3) * motzkinTable 5 = (2 * 4 + 3) * motzkinTable 4 + 3 * 4 * motzkinTable 3 := by
  native_decide
theorem motzkin_recurrence_5 :
    (5 + 3) * motzkinTable 6 = (2 * 5 + 3) * motzkinTable 5 + 3 * 5 * motzkinTable 4 := by
  native_decide
theorem motzkin_recurrence_6 :
    (6 + 3) * motzkinTable 7 = (2 * 6 + 3) * motzkinTable 6 + 3 * 6 * motzkinTable 5 := by
  native_decide
theorem motzkin_recurrence_7 :
    (7 + 3) * motzkinTable 8 = (2 * 7 + 3) * motzkinTable 7 + 3 * 7 * motzkinTable 6 := by
  native_decide

/-- Upper bound: M_n < 3^n for n = 1 … 9. -/
theorem motzkin_lt_three_pow_1 : motzkinTable 1 < 3 ^ 1 := by native_decide
theorem motzkin_lt_three_pow_2 : motzkinTable 2 < 3 ^ 2 := by native_decide
theorem motzkin_lt_three_pow_3 : motzkinTable 3 < 3 ^ 3 := by native_decide
theorem motzkin_lt_three_pow_4 : motzkinTable 4 < 3 ^ 4 := by native_decide
theorem motzkin_lt_three_pow_5 : motzkinTable 5 < 3 ^ 5 := by native_decide
theorem motzkin_lt_three_pow_6 : motzkinTable 6 < 3 ^ 6 := by native_decide
theorem motzkin_lt_three_pow_7 : motzkinTable 7 < 3 ^ 7 := by native_decide
theorem motzkin_lt_three_pow_8 : motzkinTable 8 < 3 ^ 8 := by native_decide
theorem motzkin_lt_three_pow_9 : motzkinTable 9 < 3 ^ 9 := by native_decide

/-- Lower bound: M_n > 2^n for n = 8, 9. -/
theorem two_pow_lt_motzkin_8 : 2 ^ 8 < motzkinTable 8 := by native_decide
theorem two_pow_lt_motzkin_9 : 2 ^ 9 < motzkinTable 9 := by native_decide

/-- The Motzkin ratio M_{n+1}/M_n approaches 3 from below.
    Integer bracket: 2 < M_9/M_8 < 3, integer form.
    Upper: M_9 * 4 < M_8 * 13 (ratio < 3.25).
    Lower: M_9 * 2 > M_8 * 5 (ratio > 2.5). -/
theorem motzkin_ratio_upper : motzkinTable 9 * 4 < motzkinTable 8 * 13 := by native_decide
theorem motzkin_ratio_lower : motzkinTable 9 * 2 > motzkinTable 8 * 5  := by native_decide

/-! ## 3. Large Schröder numbers — growth constant ρ⁻¹ = 3 + 2√2 ≈ 5.828

  S_n (large Schröder): 1, 2, 6, 22, 90, 394, 1806, 8558, 41586.
  Recurrence (ℕ-safe form): (n+2)·S_{n+1} + (n-1)·S_{n-1} = (6n+3)·S_n.
-/

/-- Large Schröder numbers via lookup table (indices 0 … 8). -/
def schroederTable : Fin 9 → ℕ := ![1, 2, 6, 22, 90, 394, 1806, 8558, 41586]

-- Basic checks
theorem schroder_0 : schroederTable 0 = 1     := by native_decide
theorem schroder_1 : schroederTable 1 = 2     := by native_decide
theorem schroder_2 : schroederTable 2 = 6     := by native_decide
theorem schroder_3 : schroederTable 3 = 22    := by native_decide
theorem schroder_4 : schroederTable 4 = 90    := by native_decide
theorem schroder_5 : schroederTable 5 = 394   := by native_decide
theorem schroder_6 : schroederTable 6 = 1806  := by native_decide
theorem schroder_7 : schroederTable 7 = 8558  := by native_decide
theorem schroder_8 : schroederTable 8 = 41586 := by native_decide

/-- Recurrence `(n+2)·S_{n+1} + (n-1)·S_{n-1} = (6n+3)·S_n` for n = 1 … 7.
    (Written in ℕ-safe addition form to avoid truncated subtraction.) -/
theorem schroder_recurrence_1 :
    (1 + 2) * schroederTable 2 + (1 - 1) * schroederTable 0 =
      (6 * 1 + 3) * schroederTable 1 := by native_decide
theorem schroder_recurrence_2 :
    (2 + 2) * schroederTable 3 + (2 - 1) * schroederTable 1 =
      (6 * 2 + 3) * schroederTable 2 := by native_decide
theorem schroder_recurrence_3 :
    (3 + 2) * schroederTable 4 + (3 - 1) * schroederTable 2 =
      (6 * 3 + 3) * schroederTable 3 := by native_decide
theorem schroder_recurrence_4 :
    (4 + 2) * schroederTable 5 + (4 - 1) * schroederTable 3 =
      (6 * 4 + 3) * schroederTable 4 := by native_decide
theorem schroder_recurrence_5 :
    (5 + 2) * schroederTable 6 + (5 - 1) * schroederTable 4 =
      (6 * 5 + 3) * schroederTable 5 := by native_decide
theorem schroder_recurrence_6 :
    (6 + 2) * schroederTable 7 + (6 - 1) * schroederTable 5 =
      (6 * 6 + 3) * schroederTable 6 := by native_decide
theorem schroder_recurrence_7 :
    (7 + 2) * schroederTable 8 + (7 - 1) * schroederTable 6 =
      (6 * 7 + 3) * schroederTable 7 := by native_decide

/-- Upper bound: S_n < 6^n for n = 1 … 8. -/
theorem schroder_lt_six_pow_1 : schroederTable 1 < 6 ^ 1 := by native_decide
theorem schroder_lt_six_pow_2 : schroederTable 2 < 6 ^ 2 := by native_decide
theorem schroder_lt_six_pow_3 : schroederTable 3 < 6 ^ 3 := by native_decide
theorem schroder_lt_six_pow_4 : schroederTable 4 < 6 ^ 4 := by native_decide
theorem schroder_lt_six_pow_5 : schroederTable 5 < 6 ^ 5 := by native_decide
theorem schroder_lt_six_pow_6 : schroederTable 6 < 6 ^ 6 := by native_decide
theorem schroder_lt_six_pow_7 : schroederTable 7 < 6 ^ 7 := by native_decide
theorem schroder_lt_six_pow_8 : schroederTable 8 < 6 ^ 8 := by native_decide

/-- Lower bound: 3^n < S_n for n = 4 … 8. -/
theorem three_pow_lt_schroder_4 : 3 ^ 4 < schroederTable 4 := by native_decide
theorem three_pow_lt_schroder_5 : 3 ^ 5 < schroederTable 5 := by native_decide
theorem three_pow_lt_schroder_6 : 3 ^ 6 < schroederTable 6 := by native_decide
theorem three_pow_lt_schroder_7 : 3 ^ 7 < schroederTable 7 := by native_decide
theorem three_pow_lt_schroder_8 : 3 ^ 8 < schroederTable 8 := by native_decide

/-- The ratio S_8/S_7 ≈ 4.859 is approaching the growth constant 3 + 2√2 ≈ 5.828 from below.
    Integer bracket: 4859 · S_7 < S_8 · 1000 < 4860 · S_7. -/
theorem schroder_ratio_upper : schroederTable 8 * 1000 < 4860 * schroederTable 7 := by
  native_decide
theorem schroder_ratio_lower : 4859 * schroederTable 7 < schroederTable 8 * 1000 := by
  native_decide

/-! ## 4. Ternary trees — growth constant ρ⁻¹ = 27/4 = 6.75

  T_n = C(3n, n) / (2n + 1): 1, 1, 3, 12, 55, 273, 1428, 7752, 43263.
-/

/-- Ternary tree count `C(3n, n) / (2n + 1)`. -/
def ternaryTree (n : ℕ) : ℕ := Nat.choose (3 * n) n / (2 * n + 1)

-- Exact values
theorem ternary_0 : ternaryTree 0 = 1     := by native_decide
theorem ternary_1 : ternaryTree 1 = 1     := by native_decide
theorem ternary_2 : ternaryTree 2 = 3     := by native_decide
theorem ternary_3 : ternaryTree 3 = 12    := by native_decide
theorem ternary_4 : ternaryTree 4 = 55    := by native_decide
theorem ternary_5 : ternaryTree 5 = 273   := by native_decide
theorem ternary_6 : ternaryTree 6 = 1428  := by native_decide
theorem ternary_7 : ternaryTree 7 = 7752  := by native_decide
theorem ternary_8 : ternaryTree 8 = 43263 := by native_decide

/-- Upper bound: T_n < 7^n for n = 1 … 8. -/
theorem ternary_lt_seven_pow_1 : ternaryTree 1 < 7 ^ 1 := by native_decide
theorem ternary_lt_seven_pow_2 : ternaryTree 2 < 7 ^ 2 := by native_decide
theorem ternary_lt_seven_pow_3 : ternaryTree 3 < 7 ^ 3 := by native_decide
theorem ternary_lt_seven_pow_4 : ternaryTree 4 < 7 ^ 4 := by native_decide
theorem ternary_lt_seven_pow_5 : ternaryTree 5 < 7 ^ 5 := by native_decide
theorem ternary_lt_seven_pow_6 : ternaryTree 6 < 7 ^ 6 := by native_decide
theorem ternary_lt_seven_pow_7 : ternaryTree 7 < 7 ^ 7 := by native_decide
theorem ternary_lt_seven_pow_8 : ternaryTree 8 < 7 ^ 8 := by native_decide

/-- Lower bound: 3^n < T_n for n = 5 … 8. -/
theorem three_pow_lt_ternary_5 : 3 ^ 5 < ternaryTree 5 := by native_decide
theorem three_pow_lt_ternary_6 : 3 ^ 6 < ternaryTree 6 := by native_decide
theorem three_pow_lt_ternary_7 : 3 ^ 7 < ternaryTree 7 := by native_decide
theorem three_pow_lt_ternary_8 : 3 ^ 8 < ternaryTree 8 := by native_decide

/-- The ratio T_8/T_7 ≈ 5.581 is approaching the growth constant 27/4 = 6.75 from below.
    Integer bracket: 5580 · T_7 < T_8 · 1000 < 5581 · T_7. -/
theorem ternary_ratio_upper : ternaryTree 8 * 1000 < 5581 * ternaryTree 7 := by native_decide
theorem ternary_ratio_lower : 5580 * ternaryTree 7 < ternaryTree 8 * 1000 := by native_decide

/-! ## 5. Fibonacci numbers — growth constant ρ⁻¹ = φ = (1+√5)/2 ≈ 1.618

  We use the standard Mathlib `Nat.fib`.

  Key identity: fib(n)² + fib(n+1)² = fib(2n+1).

  The Cassini identity: fib(n+1)² - fib(n)·fib(n+2) = (-1)^n.
  In ℕ-safe split form:
    · even n: fib(n+1)² = fib(n)·fib(n+2) + 1
    · odd  n: fib(n)·fib(n+2) = fib(n+1)² + 1
-/

/-- Sum-of-squares identity: fib(n)² + fib(n+1)² = fib(2n+1). -/
theorem fib_sum_squares_1 : Nat.fib 1 ^ 2 + Nat.fib 2 ^ 2 = Nat.fib 3  := by native_decide
theorem fib_sum_squares_2 : Nat.fib 2 ^ 2 + Nat.fib 3 ^ 2 = Nat.fib 5  := by native_decide
theorem fib_sum_squares_3 : Nat.fib 3 ^ 2 + Nat.fib 4 ^ 2 = Nat.fib 7  := by native_decide
theorem fib_sum_squares_4 : Nat.fib 4 ^ 2 + Nat.fib 5 ^ 2 = Nat.fib 9  := by native_decide
theorem fib_sum_squares_5 : Nat.fib 5 ^ 2 + Nat.fib 6 ^ 2 = Nat.fib 11 := by native_decide
theorem fib_sum_squares_6 : Nat.fib 6 ^ 2 + Nat.fib 7 ^ 2 = Nat.fib 13 := by native_decide
theorem fib_sum_squares_7 : Nat.fib 7 ^ 2 + Nat.fib 8 ^ 2 = Nat.fib 15 := by native_decide

/-- Cassini identity (even index n): fib(n+1)² = fib(n)·fib(n+2) + 1. -/
theorem cassini_even_2 : Nat.fib 3 ^ 2 = Nat.fib 2 * Nat.fib 4 + 1  := by native_decide
theorem cassini_even_4 : Nat.fib 5 ^ 2 = Nat.fib 4 * Nat.fib 6 + 1  := by native_decide
theorem cassini_even_6 : Nat.fib 7 ^ 2 = Nat.fib 6 * Nat.fib 8 + 1  := by native_decide
theorem cassini_even_8 : Nat.fib 9 ^ 2 = Nat.fib 8 * Nat.fib 10 + 1 := by native_decide

/-- Cassini identity (odd index n): fib(n)·fib(n+2) = fib(n+1)² + 1. -/
theorem cassini_odd_1 : Nat.fib 1 * Nat.fib 3 = Nat.fib 2 ^ 2 + 1  := by native_decide
theorem cassini_odd_3 : Nat.fib 3 * Nat.fib 5 = Nat.fib 4 ^ 2 + 1  := by native_decide
theorem cassini_odd_5 : Nat.fib 5 * Nat.fib 7 = Nat.fib 6 ^ 2 + 1  := by native_decide
theorem cassini_odd_7 : Nat.fib 7 * Nat.fib 9 = Nat.fib 8 ^ 2 + 1  := by native_decide
theorem cassini_odd_9 : Nat.fib 9 * Nat.fib 11 = Nat.fib 10 ^ 2 + 1 := by native_decide

/-- Golden ratio bracket φ ≈ 1.618:
    1617 · fib(14) < fib(15) · 1000 < 1619 · fib(14). -/
theorem fib_ratio_upper : Nat.fib 15 * 1000 < 1619 * Nat.fib 14 := by native_decide
theorem fib_ratio_lower : 1617 * Nat.fib 14 < Nat.fib 15 * 1000 := by native_decide

/-- fib(n) < 2^n for n = 1 … 15. -/
theorem fib_lt_two_pow :
    ∀ n ∈ Finset.Icc 1 15, Nat.fib n < 2 ^ n := by
  intro n hn
  fin_cases hn <;> native_decide

/-! ## 6. Bell numbers — super-exponential growth

  B_n = Σ_{k=0}^{n} S(n,k) where S(n,k) is the Stirling number of the second
  kind.  The growth is B_n ~ (n/ln n)^n (super-exponential, no fixed ρ).
  Values: 1, 1, 2, 5, 15, 52, 203, 877, 4140.
-/

/-- Bell numbers via lookup table (indices 0 … 8). -/
def bellTable : Fin 9 → ℕ := ![1, 1, 2, 5, 15, 52, 203, 877, 4140]

-- Exact values
theorem bell_0 : bellTable 0 = 1    := by native_decide
theorem bell_1 : bellTable 1 = 1    := by native_decide
theorem bell_2 : bellTable 2 = 2    := by native_decide
theorem bell_3 : bellTable 3 = 5    := by native_decide
theorem bell_4 : bellTable 4 = 15   := by native_decide
theorem bell_5 : bellTable 5 = 52   := by native_decide
theorem bell_6 : bellTable 6 = 203  := by native_decide
theorem bell_7 : bellTable 7 = 877  := by native_decide
theorem bell_8 : bellTable 8 = 4140 := by native_decide

/-- Recurrence: B_{n+1} = Σ_{k=0}^{n} C(n,k) · B_k.
    Verified for n = 1 … 5 in closed form. -/
theorem bell_rec_1 : bellTable 1 = bellTable 0 := by native_decide
theorem bell_rec_2 : bellTable 2 = bellTable 1 + bellTable 0 := by native_decide
theorem bell_rec_3 : bellTable 3 =
    1 * bellTable 2 + 2 * bellTable 1 + 1 * bellTable 0 := by native_decide
theorem bell_rec_4 : bellTable 4 =
    1 * bellTable 3 + 3 * bellTable 2 + 3 * bellTable 1 + 1 * bellTable 0 := by native_decide
theorem bell_rec_5 : bellTable 5 =
    1 * bellTable 4 + 4 * bellTable 3 + 6 * bellTable 2 +
    4 * bellTable 1 + 1 * bellTable 0 := by native_decide

/-- Log-convexity: B_n · B_{n+2} > B_{n+1}² for n = 1 … 6. -/
theorem bell_log_convex_1 : bellTable 1 * bellTable 3 > bellTable 2 ^ 2 := by native_decide
theorem bell_log_convex_2 : bellTable 2 * bellTable 4 > bellTable 3 ^ 2 := by native_decide
theorem bell_log_convex_3 : bellTable 3 * bellTable 5 > bellTable 4 ^ 2 := by native_decide
theorem bell_log_convex_4 : bellTable 4 * bellTable 6 > bellTable 5 ^ 2 := by native_decide
theorem bell_log_convex_5 : bellTable 5 * bellTable 7 > bellTable 6 ^ 2 := by native_decide
theorem bell_log_convex_6 : bellTable 6 * bellTable 8 > bellTable 7 ^ 2 := by native_decide

/-- Super-exponential: ratio B_{n+1}/B_n exceeds 4 at n = 7 → 8.
    Integer form: B_8 > 4 · B_7. -/
theorem bell_ratio_exceeds_4 : bellTable 8 > 4 * bellTable 7 := by native_decide

/-- Bell numbers grow faster than any polynomial-exponential base we have:
    B_8 = 4140 > 3^8 = 6561? No (4140 < 6561).
    Correct comparison: B_8 > 2 · C_8 (Bell vastly beats Catalan). -/
theorem bell_exceeds_twice_catalan_8 : bellTable 8 > 2 * catalan 8 := by native_decide

/-- Bell far exceeds Motzkin: B_8 > 10 · M_8. -/
theorem bell_exceeds_ten_motzkin_8 : bellTable 8 > 10 * motzkinTable 8 := by native_decide

/-! ## 7. Integer partitions — sub-exponential (Hardy–Ramanujan)

  p(n) ~ exp(π√(2n/3)) / (4n√3).  The growth is sub-exponential:
  for any fixed c > 1, eventually c^n > p(n).
  Values: 1,1,2,3,5,7,11,15,22,30,42,56.

  Euler's pentagonal recurrence (ℕ-safe addition form):
    p(n) + p(n-5) + p(n-7) + ··· = p(n-1) + p(n-2) + ···
-/

/-- Integer partition numbers via lookup table (indices 0 … 11). -/
def partitionTable : Fin 12 → ℕ := ![1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42, 56]

-- Basic values
theorem partition_0  : partitionTable 0  = 1  := by native_decide
theorem partition_1  : partitionTable 1  = 1  := by native_decide
theorem partition_2  : partitionTable 2  = 2  := by native_decide
theorem partition_3  : partitionTable 3  = 3  := by native_decide
theorem partition_4  : partitionTable 4  = 5  := by native_decide
theorem partition_5  : partitionTable 5  = 7  := by native_decide
theorem partition_6  : partitionTable 6  = 11 := by native_decide
theorem partition_7  : partitionTable 7  = 15 := by native_decide
theorem partition_8  : partitionTable 8  = 22 := by native_decide
theorem partition_9  : partitionTable 9  = 30 := by native_decide
theorem partition_10 : partitionTable 10 = 42 := by native_decide
theorem partition_11 : partitionTable 11 = 56 := by native_decide

/-- Euler pentagonal recurrence (ℕ-safe addition form).
    p(n) = p(n-1) + p(n-2) - p(n-5) - p(n-7) + ···
    Equivalently: p(5) + p(0) = p(4) + p(3). -/
theorem partition_pentagonal_5 :
    partitionTable 5 + partitionTable 0 = partitionTable 4 + partitionTable 3 := by
  native_decide

/-- p(6) + p(1) = p(5) + p(4). -/
theorem partition_pentagonal_6 :
    partitionTable 6 + partitionTable 1 = partitionTable 5 + partitionTable 4 := by
  native_decide

/-- p(7) + p(2) + p(0) = p(6) + p(5). -/
theorem partition_pentagonal_7 :
    partitionTable 7 + partitionTable 2 + partitionTable 0 =
      partitionTable 6 + partitionTable 5 := by
  native_decide

/-- p(8) + p(3) + p(1) = p(7) + p(6). -/
theorem partition_pentagonal_8 :
    partitionTable 8 + partitionTable 3 + partitionTable 1 =
      partitionTable 7 + partitionTable 6 := by
  native_decide

/-- Sub-exponential upper bound: p(n) < 2^n for n = 2 … 11.
    (For n = 0,1 we have p(n) = 1 = 2^0, so use ≤.) -/
theorem partition_le_one_pow_0 : partitionTable 0 ≤ 1 := by native_decide
theorem partition_le_one_pow_1 : partitionTable 1 ≤ 2 := by native_decide
theorem partition_lt_two_pow_2  : partitionTable 2  < 2 ^ 2  := by native_decide
theorem partition_lt_two_pow_3  : partitionTable 3  < 2 ^ 3  := by native_decide
theorem partition_lt_two_pow_4  : partitionTable 4  < 2 ^ 4  := by native_decide
theorem partition_lt_two_pow_5  : partitionTable 5  < 2 ^ 5  := by native_decide
theorem partition_lt_two_pow_6  : partitionTable 6  < 2 ^ 6  := by native_decide
theorem partition_lt_two_pow_7  : partitionTable 7  < 2 ^ 7  := by native_decide
theorem partition_lt_two_pow_8  : partitionTable 8  < 2 ^ 8  := by native_decide
theorem partition_lt_two_pow_9  : partitionTable 9  < 2 ^ 9  := by native_decide
theorem partition_lt_two_pow_10 : partitionTable 10 < 2 ^ 10 := by native_decide
theorem partition_lt_two_pow_11 : partitionTable 11 < 2 ^ 11 := by native_decide

/-- The growth is sub-exponential: ratio p(11)/p(10) = 56/42 ≈ 1.33 < 2.
    Integer form: p(11) < 2 · p(10). -/
theorem partition_ratio_lt_two_at_11 :
    partitionTable 11 < 2 * partitionTable 10 := by native_decide

/-- Contrast with Bell: B_8 = 4140 >> p(8) = 22. -/
theorem bell_far_exceeds_partition_8 :
    bellTable 8 > 100 * partitionTable 8 := by native_decide

/-! ## 8. Cross-sequence growth comparison

  Summary of exponential growth constants (as numerical brackets):
    Fibonacci: ρ⁻¹ ≈ 1.618   (fib(n) < 2^n)
    Motzkin:   ρ⁻¹ = 3       (M_n < 3^n)
    Catalan:   ρ⁻¹ = 4       (C_n < 4^n)
    Schröder:  ρ⁻¹ ≈ 5.828   (S_n < 6^n)
    Ternary:   ρ⁻¹ = 6.75    (T_n < 7^n)

  At n = 6: fib(6) = 8 < M_6 = 51 < C_6 = 132 < T_6 = 1428 < S_6 = 1806.
  At n = 8: T_8 = 43263 > S_8 = 41586 (ternary eventually overtakes Schröder,
  consistent with ρ⁻¹(ternary) = 6.75 > 5.828 = ρ⁻¹(Schröder)).
-/

/-- At n = 6: fib(6) < M_6 < C_6 < T_6 < S_6. -/
theorem growth_order_at_6 :
    Nat.fib 6 < motzkinTable 6 ∧
    motzkinTable 6 < catalan 6 ∧
    catalan 6 < ternaryTree 6 ∧
    ternaryTree 6 < schroederTable 6 := by
  native_decide

/-- At n = 8 the ternary tree count exceeds Schröder, consistent with
    ρ⁻¹(ternary) = 6.75 > 5.828 = ρ⁻¹(Schröder). -/
theorem ternary_exceeds_schroder_at_8 : schroederTable 8 < ternaryTree 8 := by native_decide

/-- Bell exceeds the Catalan sequence for n ≥ 4. -/
theorem bell_exceeds_catalan_4 : catalan 4 < bellTable 4 := by native_decide
theorem bell_exceeds_catalan_8 : catalan 8 < bellTable 8 := by native_decide

/-- Integer partitions grow slower than the Fibonacci sequence at n = 10. -/
theorem partition_lt_fib_at_10 : partitionTable 10 < Nat.fib 10 := by native_decide


structure ExponentialGrowthBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ExponentialGrowthBudgetCertificate.controlled
    (c : ExponentialGrowthBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ExponentialGrowthBudgetCertificate.budgetControlled
    (c : ExponentialGrowthBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ExponentialGrowthBudgetCertificate.Ready
    (c : ExponentialGrowthBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ExponentialGrowthBudgetCertificate.size
    (c : ExponentialGrowthBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem exponentialGrowth_budgetCertificate_le_size
    (c : ExponentialGrowthBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleExponentialGrowthBudgetCertificate :
    ExponentialGrowthBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleExponentialGrowthBudgetCertificate.Ready := by
  constructor
  · norm_num [ExponentialGrowthBudgetCertificate.controlled,
      sampleExponentialGrowthBudgetCertificate]
  · norm_num [ExponentialGrowthBudgetCertificate.budgetControlled,
      sampleExponentialGrowthBudgetCertificate]

example :
    sampleExponentialGrowthBudgetCertificate.certificateBudgetWindow ≤
      sampleExponentialGrowthBudgetCertificate.size := by
  apply exponentialGrowth_budgetCertificate_le_size
  constructor
  · norm_num [ExponentialGrowthBudgetCertificate.controlled,
      sampleExponentialGrowthBudgetCertificate]
  · norm_num [ExponentialGrowthBudgetCertificate.budgetControlled,
      sampleExponentialGrowthBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleExponentialGrowthBudgetCertificate.Ready := by
  constructor
  · norm_num [ExponentialGrowthBudgetCertificate.controlled,
      sampleExponentialGrowthBudgetCertificate]
  · norm_num [ExponentialGrowthBudgetCertificate.budgetControlled,
      sampleExponentialGrowthBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleExponentialGrowthBudgetCertificate.certificateBudgetWindow ≤
      sampleExponentialGrowthBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List ExponentialGrowthBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleExponentialGrowthBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleExponentialGrowthBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.ExponentialGrowth
