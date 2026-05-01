import AnalyticCombinatorics.Examples.SetPartitions

open PowerSeries CombinatorialClass Finset
open scoped PowerSeries.WithPiTopology

/-- Surjections as labelled objects: ordered nonempty blocks on the label set. -/
noncomputable def surjectionClass : CombinatorialClass :=
  labelSeq posIntClass posIntClass.count_zero

/-- The count of labelled surjections is the Fubini / ordered-Bell number. -/
theorem surjectionClass_count_eq_fubini (n : ℕ) :
    surjectionClass.count n =
      ∑ k ∈ Finset.range (n + 1), k.factorial * Nat.stirlingSecond n k := by
  exact labelSeq_posIntClass_count_eq_fubini n

/-- The Fubini EGF satisfies `(2 - exp(z)) · F = 1`. -/
theorem surjectionClass_egf_mul_two_sub_exp :
    surjectionClass.egf * (2 - PowerSeries.exp ℚ) = 1 := by
  exact labelSeq_posIntClass_egf_mul_two_sub_exp

/-! Sanity checks: Fubini numbers are 1, 1, 3, 13, 75, 541, 4683, 47293,
545835, 7087261, 102247563, 1622632573, 28091567595, 526858348381,
10641342970443, 230283190977853, 5315654681981355,
130370767029135901. -/

example : surjectionClass.count 0 = 1 := by
  rw [surjectionClass_count_eq_fubini]
  decide

example : surjectionClass.count 1 = 1 := by
  rw [surjectionClass_count_eq_fubini]
  decide

example : surjectionClass.count 2 = 3 := by
  rw [surjectionClass_count_eq_fubini]
  decide

example : surjectionClass.count 3 = 13 := by
  rw [surjectionClass_count_eq_fubini]
  decide

example : surjectionClass.count 4 = 75 := by
  rw [surjectionClass_count_eq_fubini]
  decide

example : surjectionClass.count 5 = 541 := by
  rw [surjectionClass_count_eq_fubini]
  decide

example : surjectionClass.count 6 = 4683 := by
  rw [surjectionClass_count_eq_fubini]
  decide

example : surjectionClass.count 7 = 47293 := by
  rw [surjectionClass_count_eq_fubini]
  decide

example : surjectionClass.count 8 = 545835 := by
  rw [surjectionClass_count_eq_fubini]
  decide

example : surjectionClass.count 9 = 7087261 := by
  rw [surjectionClass_count_eq_fubini]
  decide

example : surjectionClass.count 10 = 102247563 := by
  rw [surjectionClass_count_eq_fubini]
  decide

set_option linter.style.nativeDecide false in
example : surjectionClass.count 11 = 1622632573 := by
  rw [surjectionClass_count_eq_fubini]
  native_decide

set_option linter.style.nativeDecide false in
example : surjectionClass.count 12 = 28091567595 := by
  rw [surjectionClass_count_eq_fubini]
  native_decide

set_option linter.style.nativeDecide false in
example : surjectionClass.count 13 = 526858348381 := by
  rw [surjectionClass_count_eq_fubini]
  native_decide

set_option linter.style.nativeDecide false in
example : surjectionClass.count 14 = 10641342970443 := by
  rw [surjectionClass_count_eq_fubini]
  native_decide

set_option linter.style.nativeDecide false in
example : surjectionClass.count 15 = 230283190977853 := by
  rw [surjectionClass_count_eq_fubini]
  native_decide

set_option linter.style.nativeDecide false in
example : surjectionClass.count 16 = 5315654681981355 := by
  rw [surjectionClass_count_eq_fubini]
  native_decide

set_option linter.style.nativeDecide false in
example : surjectionClass.count 17 = 130370767029135901 := by
  rw [surjectionClass_count_eq_fubini]
  native_decide
