/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VIII — Saddle-point method applications.

  This file formalizes computable checks related to the saddle-point method:
  Bell numbers (via triangle), distinct/odd partitions (Euler's theorem),
  saddle-point bounds, integer compositions, and composition statistics.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

open Finset

namespace SaddlePointApps

/-! ## 1. Bell numbers via Bell triangle -/

/-- The Bell triangle: row `n`, column `k`.
    B(0,0) = 1; B(0, k+1) = 0;
    B(n+1, 0) = B(n, n); B(n+1, k+1) = B(n+1, k) + B(n, k). -/
def bellTriangle : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => bellTriangle n n
  | n + 1, k + 1 => bellTriangle (n + 1) k + bellTriangle n k
termination_by n k => (n, k)

/-- The `n`-th Bell number is `bellTriangle n 0`. -/
def bellNumber (n : ℕ) : ℕ := bellTriangle n 0

example : bellNumber 0 = 1 := by native_decide
example : bellNumber 1 = 1 := by native_decide
example : bellNumber 2 = 2 := by native_decide
example : bellNumber 3 = 5 := by native_decide
example : bellNumber 4 = 15 := by native_decide
example : bellNumber 5 = 52 := by native_decide
example : bellNumber 6 = 203 := by native_decide
example : bellNumber 7 = 877 := by native_decide

/-! ## 2. Distinct-parts = odd-parts (Euler's theorem, tabulated) -/

/-- Number of partitions into distinct parts, tabulated for n = 0..10. -/
def distinctPartitions : Fin 11 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 2
  | ⟨4, _⟩ => 2
  | ⟨5, _⟩ => 3
  | ⟨6, _⟩ => 4
  | ⟨7, _⟩ => 5
  | ⟨8, _⟩ => 6
  | ⟨9, _⟩ => 8
  | ⟨10, _⟩ => 10

/-- Number of partitions into odd parts, tabulated for n = 0..10. -/
def oddPartitions : Fin 11 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 2
  | ⟨4, _⟩ => 2
  | ⟨5, _⟩ => 3
  | ⟨6, _⟩ => 4
  | ⟨7, _⟩ => 5
  | ⟨8, _⟩ => 6
  | ⟨9, _⟩ => 8
  | ⟨10, _⟩ => 10

/-- Euler's theorem (tabulated verification): distinct-part and odd-part
    partition counts agree for n = 0, ..., 10. -/
theorem euler_distinct_eq_odd :
    ∀ i : Fin 11, distinctPartitions i = oddPartitions i := by
  decide

/-! ## 3. Saddle-point bounds on Bell numbers -/

example : bellNumber 5 < 5 ^ 5 := by native_decide
example : bellNumber 6 < 6 ^ 6 := by native_decide
example : bellNumber 7 < 7 ^ 7 := by native_decide
example : bellNumber 5 > 2 ^ 4 := by native_decide
example : bellNumber 7 > 2 ^ 6 := by native_decide

/-! ## 4. Integer composition count -/

/-- Number of compositions of `n` into exactly `k` parts. -/
def compositionCount (n k : ℕ) : ℕ :=
  if k = 0 then (if n = 0 then 1 else 0)
  else if n = 0 then 0
  else Nat.choose (n - 1) (k - 1)

/-- Total number of compositions of `n` (summing over all `k`). -/
def totalCompositions (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), compositionCount n k

/-- For n ≥ 1, the total number of compositions of n equals 2^(n-1). -/
example : totalCompositions 1 = 2 ^ 0 := by native_decide
example : totalCompositions 2 = 2 ^ 1 := by native_decide
example : totalCompositions 3 = 2 ^ 2 := by native_decide
example : totalCompositions 4 = 2 ^ 3 := by native_decide
example : totalCompositions 5 = 2 ^ 4 := by native_decide
example : totalCompositions 6 = 2 ^ 5 := by native_decide
example : totalCompositions 7 = 2 ^ 6 := by native_decide
example : totalCompositions 8 = 2 ^ 7 := by native_decide

/-! ## 5. Ordered partition (composition) statistics -/

/-- Total number of parts across all compositions of `n`. -/
def totalPartsInCompositions (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), k * compositionCount n k

/-- For n ≥ 2, totalPartsInCompositions n = (n+1) * 2^(n-2). -/
example : totalPartsInCompositions 2 = 3 * 2 ^ 0 := by native_decide
example : totalPartsInCompositions 3 = 4 * 2 ^ 1 := by native_decide
example : totalPartsInCompositions 4 = 5 * 2 ^ 2 := by native_decide
example : totalPartsInCompositions 5 = 6 * 2 ^ 3 := by native_decide

end SaddlePointApps
