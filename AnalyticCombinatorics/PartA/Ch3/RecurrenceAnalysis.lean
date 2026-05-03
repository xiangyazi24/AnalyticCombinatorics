import Mathlib.Tactic

set_option linter.style.nativeDecide false

open Finset Nat

/-! # Ch III — Recurrence Relations and Their Solutions

This file formalizes numerical instances of classical recurrences arising in
the analysis of algorithms and combinatorics (Flajolet & Sedgewick, Parts A/B):

- **Mergesort work** — master theorem case: T(n) = 2T(n/2) + n
- **Binary search depth** — T(n) = T(n/2) + 1
- **Pell numbers** — the linear recurrence P(n) = 2P(n-1) + P(n-2)
- **Tribonacci numbers** — T(n) = T(n-1) + T(n-2) + T(n-3)
- **Catalan convolution** — the quadratic recurrence C(n+1) = Σ C(k)*C(n-k)
- **Karatsuba work** — T(n) = 3T(n/2) + n, master theorem case log_2 3 > 1

All proofs use `native_decide` on finite tables.
-/

namespace RecurrenceAnalysis

/-! ## 1. Mergesort Work: T(2^i)

The recurrence T(n) = 2T(n/2) + n governs mergesort.
Evaluating at powers of 2:

  T(2^0) = 1
  T(2^1) = 2*T(2^0) + 2 = 4
  T(2^2) = 2*T(2^1) + 4 = 12
  T(2^3) = 2*T(2^2) + 8 = 32
  T(2^4) = 2*T(2^3) + 16 = 80
  T(2^5) = 2*T(2^4) + 32 = 192

The general formula is T(2^k) = (k+1)*2^k - 2^k + 1 = Θ(n log n).
-/

/-- Mergesort work values at T(2^i) for i = 0, 1, 2, 3, 4, 5. -/
def mergesortWork : Fin 6 → ℕ := ![1, 4, 12, 32, 80, 192]

/-- Mergesort recurrence step 1: T(2^1) = 2*T(2^0) + 2^1. -/
theorem mergesortWork_step1 :
    mergesortWork ⟨1, by omega⟩ = 2 * mergesortWork ⟨0, by omega⟩ + 2 ^ 1 := by
  native_decide

/-- Mergesort recurrence step 2: T(2^2) = 2*T(2^1) + 2^2. -/
theorem mergesortWork_step2 :
    mergesortWork ⟨2, by omega⟩ = 2 * mergesortWork ⟨1, by omega⟩ + 2 ^ 2 := by
  native_decide

/-- Mergesort recurrence step 3: T(2^3) = 2*T(2^2) + 2^3. -/
theorem mergesortWork_step3 :
    mergesortWork ⟨3, by omega⟩ = 2 * mergesortWork ⟨2, by omega⟩ + 2 ^ 3 := by
  native_decide

/-- Mergesort recurrence step 4: T(2^4) = 2*T(2^3) + 2^4. -/
theorem mergesortWork_step4 :
    mergesortWork ⟨4, by omega⟩ = 2 * mergesortWork ⟨3, by omega⟩ + 2 ^ 4 := by
  native_decide

/-- Mergesort recurrence step 5: T(2^5) = 2*T(2^4) + 2^5. -/
theorem mergesortWork_step5 :
    mergesortWork ⟨5, by omega⟩ = 2 * mergesortWork ⟨4, by omega⟩ + 2 ^ 5 := by
  native_decide

/-- Mergesort recurrence: T(2^{i+1}) = 2*T(2^i) + 2^{i+1}, all five steps at once. -/
theorem mergesortWork_recurrence :
    ∀ i : Fin 5,
      mergesortWork ⟨i.val + 1, by omega⟩ =
        2 * mergesortWork ⟨i.val, by omega⟩ + 2 ^ (i.val + 1) := by
  native_decide

/-! ## 2. Binary Search Depth: T(2^k) = k

The recurrence T(n) = T(n/2) + 1, T(1) = 0 counts comparisons in binary search.
Evaluating at powers of 2: T(2^k) = k.
-/

/-- Binary search depths T(2^i) = i for i = 0..6. -/
def binarySearchTable : Fin 7 → ℕ := ![0, 1, 2, 3, 4, 5, 6]

/-- Each table entry equals its index: T(2^i) = i. -/
theorem binarySearch_eq_index : ∀ i : Fin 7, binarySearchTable i = i.val := by
  native_decide

/-- Recurrence: T(2^{i+1}) = T(2^i) + 1, for i = 0..5. -/
theorem binarySearch_recurrence :
    ∀ i : Fin 6,
      binarySearchTable ⟨i.val + 1, by omega⟩ =
        binarySearchTable ⟨i.val, by omega⟩ + 1 := by
  native_decide

/-! ## 3. Pell Numbers: P(n) = 2P(n-1) + P(n-2)

Starting from P(0) = 0, P(1) = 1, the Pell sequence:
  0, 1, 2, 5, 12, 29, 70, 169, 408

Pell numbers grow as P(n) ~ (1+√2)^n / (2√2), the rate of the silver ratio.
-/

/-- Pell numbers P(0)..P(8). -/
def pellTable : Fin 9 → ℕ := ![0, 1, 2, 5, 12, 29, 70, 169, 408]

/-- Pell recurrence: P(n+2) = 2*P(n+1) + P(n), for n = 0..6. -/
theorem pell_recurrence :
    ∀ i : Fin 7,
      pellTable ⟨i.val + 2, by omega⟩ =
        2 * pellTable ⟨i.val + 1, by omega⟩ + pellTable ⟨i.val, by omega⟩ := by
  native_decide

/-- Pell numbers are strictly increasing from index 1. -/
theorem pell_strictly_increasing :
    ∀ i : Fin 7,
      pellTable ⟨i.val, by omega⟩ < pellTable ⟨i.val + 1, by omega⟩ := by
  native_decide

/-- P(0) = 0, P(1) = 1: initial conditions. -/
theorem pell_init : pellTable ⟨0, by omega⟩ = 0 ∧ pellTable ⟨1, by omega⟩ = 1 := by
  native_decide

/-- The ratio P(n+1)/P(n) approaches √2 + 1 ≈ 2.414.
    We verify: P(8)/P(7) = 408/169, and (408*10)/169 = 24 (integer part of 2.4...).
    More precisely 408/169 > 2 and 408/169 < 3. -/
theorem pell_ratio_bounds :
    2 * pellTable ⟨7, by omega⟩ < pellTable ⟨8, by omega⟩ ∧
    pellTable ⟨8, by omega⟩ < 3 * pellTable ⟨7, by omega⟩ := by
  native_decide

/-! ## 4. Tribonacci Numbers: T(n) = T(n-1) + T(n-2) + T(n-3)

Starting from T(0) = 0, T(1) = 0, T(2) = 1:
  0, 0, 1, 1, 2, 4, 7, 13, 24, 44, 81
-/

/-- Tribonacci numbers T(0)..T(10). -/
def tribTable : Fin 11 → ℕ := ![0, 0, 1, 1, 2, 4, 7, 13, 24, 44, 81]

/-- Tribonacci recurrence: T(n+3) = T(n+2) + T(n+1) + T(n), for n = 0..7. -/
theorem trib_recurrence :
    ∀ i : Fin 8,
      tribTable ⟨i.val + 3, by omega⟩ =
        tribTable ⟨i.val + 2, by omega⟩ +
        tribTable ⟨i.val + 1, by omega⟩ +
        tribTable ⟨i.val, by omega⟩ := by
  native_decide

/-- Initial conditions for Tribonacci. -/
theorem trib_init :
    tribTable ⟨0, by omega⟩ = 0 ∧
    tribTable ⟨1, by omega⟩ = 0 ∧
    tribTable ⟨2, by omega⟩ = 1 := by
  native_decide

/-- Spot check: T(10) = 81. -/
example : tribTable ⟨10, by omega⟩ = 81 := by native_decide

/-- Tribonacci numbers are eventually strictly increasing: T(3)..T(10) is increasing. -/
theorem trib_increasing :
    ∀ i : Fin 7,
      tribTable ⟨i.val + 3, by omega⟩ < tribTable ⟨i.val + 4, by omega⟩ := by
  native_decide

/-! ## 5. Catalan Convolution: C(n+1) = Σ_{k=0}^{n} C(k)*C(n-k)

The Catalan numbers satisfy a quadratic (self-convolution) recurrence:
  C(0) = 1
  C(n+1) = Σ_{k=0}^{n} C(k) * C(n-k)

Table: 1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862.
-/

/-- Catalan numbers C(0)..C(9). -/
def catalanTab : Fin 10 → ℕ := ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862]

/-- C(1) = C(0)*C(0) = 1. -/
theorem catalan_conv_1 :
    catalanTab ⟨1, by omega⟩ =
      catalanTab ⟨0, by omega⟩ * catalanTab ⟨0, by omega⟩ := by
  native_decide

/-- C(2) = C(0)*C(1) + C(1)*C(0) = 1 + 1 = 2. -/
theorem catalan_conv_2 :
    catalanTab ⟨2, by omega⟩ =
      catalanTab ⟨0, by omega⟩ * catalanTab ⟨1, by omega⟩ +
      catalanTab ⟨1, by omega⟩ * catalanTab ⟨0, by omega⟩ := by
  native_decide

/-- C(3) = C(0)*C(2) + C(1)*C(1) + C(2)*C(0) = 2+1+2 = 5. -/
theorem catalan_conv_3 :
    catalanTab ⟨3, by omega⟩ =
      catalanTab ⟨0, by omega⟩ * catalanTab ⟨2, by omega⟩ +
      catalanTab ⟨1, by omega⟩ * catalanTab ⟨1, by omega⟩ +
      catalanTab ⟨2, by omega⟩ * catalanTab ⟨0, by omega⟩ := by
  native_decide

/-- C(4) = C(0)*C(3) + C(1)*C(2) + C(2)*C(1) + C(3)*C(0) = 5+2+2+5 = 14. -/
theorem catalan_conv_4 :
    catalanTab ⟨4, by omega⟩ =
      catalanTab ⟨0, by omega⟩ * catalanTab ⟨3, by omega⟩ +
      catalanTab ⟨1, by omega⟩ * catalanTab ⟨2, by omega⟩ +
      catalanTab ⟨2, by omega⟩ * catalanTab ⟨1, by omega⟩ +
      catalanTab ⟨3, by omega⟩ * catalanTab ⟨0, by omega⟩ := by
  native_decide

/-- C(5) = Σ_{k=0}^4 C(k)*C(4-k) = 14+5+4+5+14 = 42. -/
theorem catalan_conv_5 :
    catalanTab ⟨5, by omega⟩ =
      catalanTab ⟨0, by omega⟩ * catalanTab ⟨4, by omega⟩ +
      catalanTab ⟨1, by omega⟩ * catalanTab ⟨3, by omega⟩ +
      catalanTab ⟨2, by omega⟩ * catalanTab ⟨2, by omega⟩ +
      catalanTab ⟨3, by omega⟩ * catalanTab ⟨1, by omega⟩ +
      catalanTab ⟨4, by omega⟩ * catalanTab ⟨0, by omega⟩ := by
  native_decide

/-- C(6) = Σ_{k=0}^5 C(k)*C(5-k) = 42+14+10+10+14+42 = 132. -/
theorem catalan_conv_6 :
    catalanTab ⟨6, by omega⟩ =
      catalanTab ⟨0, by omega⟩ * catalanTab ⟨5, by omega⟩ +
      catalanTab ⟨1, by omega⟩ * catalanTab ⟨4, by omega⟩ +
      catalanTab ⟨2, by omega⟩ * catalanTab ⟨3, by omega⟩ +
      catalanTab ⟨3, by omega⟩ * catalanTab ⟨2, by omega⟩ +
      catalanTab ⟨4, by omega⟩ * catalanTab ⟨1, by omega⟩ +
      catalanTab ⟨5, by omega⟩ * catalanTab ⟨0, by omega⟩ := by
  native_decide

/-- C(7) = Σ_{k=0}^6 C(k)*C(6-k) = 132+42+28+25+28+42+132 = 429. -/
theorem catalan_conv_7 :
    catalanTab ⟨7, by omega⟩ =
      catalanTab ⟨0, by omega⟩ * catalanTab ⟨6, by omega⟩ +
      catalanTab ⟨1, by omega⟩ * catalanTab ⟨5, by omega⟩ +
      catalanTab ⟨2, by omega⟩ * catalanTab ⟨4, by omega⟩ +
      catalanTab ⟨3, by omega⟩ * catalanTab ⟨3, by omega⟩ +
      catalanTab ⟨4, by omega⟩ * catalanTab ⟨2, by omega⟩ +
      catalanTab ⟨5, by omega⟩ * catalanTab ⟨1, by omega⟩ +
      catalanTab ⟨6, by omega⟩ * catalanTab ⟨0, by omega⟩ := by
  native_decide

/-! ## 6. Karatsuba Work: T(n) = 3T(n/2) + n

Governs Karatsuba's O(n^{log_2 3}) multiplication algorithm.
Evaluating at powers of 2:

  T(2^0) = 1
  T(2^1) = 3*T(2^0) + 2 = 5
  T(2^2) = 3*T(2^1) + 4 = 19
  T(2^3) = 3*T(2^2) + 8 = 65
  T(2^4) = 3*T(2^3) + 16 = 211
-/

/-- Karatsuba work T(2^i) for i = 0..4. -/
def karatsubaTable : Fin 5 → ℕ := ![1, 5, 19, 65, 211]

/-- Karatsuba recurrence: T(2^{i+1}) = 3*T(2^i) + 2^{i+1}, for i = 0..3. -/
theorem karatsuba_recurrence :
    ∀ i : Fin 4,
      karatsubaTable ⟨i.val + 1, by omega⟩ =
        3 * karatsubaTable ⟨i.val, by omega⟩ + 2 ^ (i.val + 1) := by
  native_decide

/-- Explicit recurrence steps. -/
example : karatsubaTable ⟨1, by omega⟩ = 3 * karatsubaTable ⟨0, by omega⟩ + 2 := by
  native_decide

example : karatsubaTable ⟨2, by omega⟩ = 3 * karatsubaTable ⟨1, by omega⟩ + 4 := by
  native_decide

example : karatsubaTable ⟨3, by omega⟩ = 3 * karatsubaTable ⟨2, by omega⟩ + 8 := by
  native_decide

example : karatsubaTable ⟨4, by omega⟩ = 3 * karatsubaTable ⟨3, by omega⟩ + 16 := by
  native_decide

/-! ## 7. Cross-recurrence comparisons

Mergesort (Θ(n log n)) grows slower than Karatsuba (Θ(n^{log_2 3} ≈ n^{1.585})).
We verify this at the common evaluation point 2^4 = 16:
  mergesortWork[4] = 80 < karatsubaTable[4] = 211.
-/

/-- At n = 2^4: mergesort work 80 < Karatsuba work 211. -/
theorem mergesort_lt_karatsuba_at_16 :
    mergesortWork ⟨4, by omega⟩ < karatsubaTable ⟨4, by omega⟩ := by
  native_decide

/-- Binary search depth at 2^6 is 6, far less than mergesort work at 2^5 = 192. -/
theorem binarySearch_lt_mergesort :
    binarySearchTable ⟨6, by omega⟩ < mergesortWork ⟨5, by omega⟩ := by
  native_decide

/-- Pell(8) = 408 > Karatsuba(4) = 211: linear recurrences can outgrow D&C. -/
theorem pell_gt_karatsuba :
    karatsubaTable ⟨4, by omega⟩ < pellTable ⟨8, by omega⟩ := by
  native_decide

/-! ## 8. Summary: recurrence classes

The recurrences studied here exemplify three master-theorem cases:
- **binary search**: T(n) = T(n/2)+1, case 2, Θ(log n).
- **mergesort**: T(n) = 2T(n/2)+n, case 2, Θ(n log n).
- **Karatsuba**: T(n) = 3T(n/2)+n, case 1, Θ(n^{log_2 3}).

And two linear recurrences with constant coefficients:
- **Pell**: geometric growth with ratio (1+√2).
- **Tribonacci**: geometric growth with the tribonacci constant ≈ 1.839.
-/

/-- Summary: all six table initial values. -/
theorem all_tables_init :
    mergesortWork ⟨0, by omega⟩ = 1 ∧
    binarySearchTable ⟨0, by omega⟩ = 0 ∧
    pellTable ⟨0, by omega⟩ = 0 ∧
    tribTable ⟨0, by omega⟩ = 0 ∧
    catalanTab ⟨0, by omega⟩ = 1 ∧
    karatsubaTable ⟨0, by omega⟩ = 1 := by
  native_decide

end RecurrenceAnalysis
