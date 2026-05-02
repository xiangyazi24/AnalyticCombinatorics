import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass

open PowerSeries CombinatorialClass

/-! # Ch III — Combinatorial Parameters and Multivariate Generating Functions
    F&S Chapter III. -/

/-- A combinatorial parameter on `A` is a function `χ : A.Obj → ℕ`. -/
abbrev Parameter (A : CombinatorialClass) : Type _ := A.Obj → ℕ

namespace CombinatorialClass

/-- Joint count: number of objects of size `n` with parameter value `k`. -/
noncomputable def jointCount (A : CombinatorialClass) (χ : Parameter A) (n k : ℕ) : ℕ :=
  ((A.level n).filter (fun a => χ a = k)).card

/-- Each parameter fiber has cardinality at most the whole level. -/
theorem jointCount_le_count
    (A : CombinatorialClass) (χ : Parameter A) (n k : ℕ) :
    A.jointCount χ n k ≤ A.count n := by
  simpa [jointCount, count] using
    (Finset.card_filter_le (A.level n) (fun a => χ a = k))

/-- Sanity: summing over all parameter values present at size `n` recovers the size-only count. -/
theorem jointCount_sum_eq_count
    (A : CombinatorialClass) (χ : Parameter A) (n : ℕ) :
    ∑ k ∈ (A.level n).image χ, A.jointCount χ n k = A.count n := by
  simpa [jointCount, count] using
    (Finset.card_eq_sum_card_image χ (A.level n)).symm

/-- The bivariate generating function `A(z,u) = Σₙ Σₖ aₙ,ₖ zⁿ uᵏ`,
modeled as a power series in `z` whose coefficients are polynomials in `u`. -/
noncomputable def bgf (A : CombinatorialClass) (χ : Parameter A) :
    PowerSeries (Polynomial ℕ) :=
  PowerSeries.mk fun n =>
    ∑ k ∈ (A.level n).image χ, Polynomial.monomial k (A.jointCount χ n k)

@[simp]
theorem coeff_bgf (A : CombinatorialClass) (χ : Parameter A) (n : ℕ) :
    coeff n (A.bgf χ) =
      ∑ k ∈ (A.level n).image χ, Polynomial.monomial k (A.jointCount χ n k) := by
  rw [bgf, PowerSeries.coeff_mk]

/-- Evaluating the parameter marker at `u = 1` recovers the ordinary generating function. -/
theorem bgf_eval_one (A : CombinatorialClass) (χ : Parameter A) :
    (A.bgf χ).map (Polynomial.evalRingHom 1) =
      A.ogf.map (algebraMap ℕ ℕ) := by
  ext n
  rw [PowerSeries.coeff_map, coeff_bgf, PowerSeries.coeff_map, coeff_ogf]
  simp [Polynomial.eval_monomial, jointCount_sum_eq_count]

/-- Cumulated cost at size `n`: `Σₖ k · aₙ,ₖ`. -/
noncomputable def cumulatedCost (A : CombinatorialClass) (χ : Parameter A) (n : ℕ) : ℕ :=
  ∑ k ∈ (A.level n).image χ, k * A.jointCount χ n k

/-- The cumulated cost is equivalently the sum of the parameter over the whole level. -/
theorem cumulatedCost_eq_sum_param
    (A : CombinatorialClass) (χ : Parameter A) (n : ℕ) :
    A.cumulatedCost χ n = ∑ a ∈ A.level n, χ a := by
  rw [cumulatedCost]
  calc
    ∑ k ∈ (A.level n).image χ, k * A.jointCount χ n k
        = ∑ k ∈ (A.level n).image χ,
            ∑ a ∈ A.level n with χ a = k, k := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [jointCount]
          rw [Finset.sum_const_nat
            (s := (A.level n).filter (fun a => χ a = k))
            (m := k) (f := fun _ => k) (by intro a ha; rfl)]
          rw [Nat.mul_comm]
    _ = ∑ a ∈ A.level n, χ a := by
          rw [Finset.sum_fiberwise_of_maps_to']
          exact fun a ha => Finset.mem_image_of_mem χ ha

/-- Mean value of a parameter among objects of size `n`. Empty levels have mean `0`. -/
noncomputable def meanParam (A : CombinatorialClass) (χ : Parameter A) (n : ℕ) : ℚ :=
  if A.count n = 0 then 0
  else (∑ k ∈ (A.level n).image χ, (k * A.jointCount χ n k : ℚ)) / A.count n

theorem meanParam_eq_cumulatedCost_div
    (A : CombinatorialClass) (χ : Parameter A) (n : ℕ) :
    A.meanParam χ n =
      if A.count n = 0 then 0 else (A.cumulatedCost χ n : ℚ) / A.count n := by
  by_cases h : A.count n = 0
  · simp [meanParam, h]
  · simp [meanParam, cumulatedCost, h, Nat.cast_sum, Nat.cast_mul]

end CombinatorialClass
