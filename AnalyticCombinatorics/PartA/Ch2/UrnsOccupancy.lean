import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace UrnsOccupancy

/-- Total number of arrangements of `n` distinguishable balls into `m` distinguishable urns. -/
def occupancyTotal (m n : ℕ) : ℕ := m ^ n

theorem occupancyTotal_3_4 : occupancyTotal 3 4 = 81 := by native_decide
theorem occupancyTotal_4_3 : occupancyTotal 4 3 = 64 := by native_decide
theorem occupancyTotal_2_10 : occupancyTotal 2 10 = 1024 := by native_decide

/-- Stirling numbers of the second kind: number of partitions of an `n`-set into `k` blocks. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * stirling2 n (k + 1) + stirling2 n k

/-- Number of surjections from an `n`-set onto an `m`-set. -/
def surjectionCount (n m : ℕ) : ℕ := Nat.factorial m * stirling2 n m

theorem surjectionCount_4_2 : surjectionCount 4 2 = 14 := by native_decide
theorem surjectionCount_4_3 : surjectionCount 4 3 = 36 := by native_decide
theorem surjectionCount_5_3 : surjectionCount 5 3 = 150 := by native_decide

/-- Expected number of coupons to collect all `m` types: m * H_m. -/
def couponCollectorExpected (m : ℕ) : ℚ :=
  (m : ℚ) * ∑ k ∈ Finset.range m, 1 / ((k + 1 : ℕ) : ℚ)

theorem couponCollector_1 : couponCollectorExpected 1 = 1 := by native_decide
theorem couponCollector_2 : couponCollectorExpected 2 = 3 := by native_decide
theorem couponCollector_3 : couponCollectorExpected 3 = 11 / 2 := by native_decide
theorem couponCollector_4 : couponCollectorExpected 4 = 25 / 3 := by native_decide

/-- Multinomial coefficient: n! / (n₁! · n₂! · … · nₖ!) where n = Σ nᵢ. -/
def multinomialCoeff (ns : List ℕ) : ℕ :=
  Nat.factorial ns.sum / (ns.map Nat.factorial).prod

theorem multinomial_222 : multinomialCoeff [2, 2, 2] = 90 := by native_decide
theorem multinomial_321 : multinomialCoeff [3, 2, 1] = 60 := by native_decide
theorem multinomial_44 : multinomialCoeff [4, 4] = 70 := by native_decide
theorem multinomial_1111 : multinomialCoeff [1, 1, 1, 1] = 24 := by native_decide

/-- Numerator of the expected number of empty urns: m · (m-1)^n. -/
def expectedEmptyNumer (m n : ℕ) : ℕ := m * (m - 1) ^ n

/-- Denominator (total arrangements): m^n. -/
def expectedEmptyDenom (m n : ℕ) : ℕ := m ^ n

theorem emptyNumer_4_3 : expectedEmptyNumer 4 3 = 108 := by native_decide
theorem emptyDenom_4_3 : expectedEmptyDenom 4 3 = 64 := by native_decide
theorem emptyNumer_10_5 : expectedEmptyNumer 10 5 = 590490 := by native_decide
theorem emptyDenom_10_5 : expectedEmptyDenom 10 5 = 100000 := by native_decide

end UrnsOccupancy
