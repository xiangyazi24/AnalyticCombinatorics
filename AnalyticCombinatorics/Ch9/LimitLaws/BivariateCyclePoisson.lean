import Mathlib
import AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoisson
import AnalyticCombinatorics.Ch9.LimitLaws.RCyclesFactorialMoment
import AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonComplete
import AnalyticCombinatorics.Ch9.LimitLaws.JointCycleMoments
import AnalyticCombinatorics.Ch9.LimitLaws.PMFToDistribution

/-!
# Bivariate Poisson limit for two cycle counts

This file proves the joint local limit and weak convergence of the pair of
cycle counts of two distinct positive lengths in a uniform random permutation.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS
namespace Bivariate

/-- Joint law of two fixed cycle counts under the uniform permutation measure. -/
def jointLaw (n r s : ℕ) : ProbabilityMeasure (ℕ × ℕ) :=
  ⟨Measure.map (fun σ : Equiv.Perm (Fin n) =>
      (rCycleCount n r σ, rCycleCount n s σ)) (uniformPermMeasure n),
    Measure.isProbabilityMeasure_map (by
      exact (measurable_of_finite _).aemeasurable)⟩

/-- Product of two Poisson probability measures. -/
def poissonProductMeasure (ρ τ : ℝ≥0) : ProbabilityMeasure (ℕ × ℕ) :=
  (poissonProbabilityMeasure ρ).prod (poissonProbabilityMeasure τ)

/-- The genuine joint pmf of two cycle counts. -/
def jointRCyclePMF (n r s i j : ℕ) : ℝ :=
  (Fintype.card {σ : Equiv.Perm (Fin n) //
    rCycleCount n r σ = i ∧ rCycleCount n s σ = j} : ℝ) / n.factorial

/-- One factor in the finite inclusion-exclusion series for `P(C_r=i)`. -/
def oneDimTerm (r i a : ℕ) : ℝ :=
  (((-1 : ℝ) ^ a) / (a.factorial * (i.factorial : ℝ))) *
    ((r : ℝ) ^ (-(i + a : ℤ)))

/-- The finite triangular index set where the exact mixed factorial moment is nonzero. -/
def jointIndexFinset (n r s i j : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (n / r - i + 1)).product
      (Finset.range (n / s - j + 1))).filter
    (fun p : ℕ × ℕ => r * (i + p.1) + s * (j + p.2) ≤ n)

/-- The finite bivariate inclusion-exclusion expression. -/
def jointRCyclePMFFormula (n r s i j : ℕ) : ℝ :=
  ∑ p ∈ jointIndexFinset n r s i j,
    oneDimTerm r i p.1 * oneDimTerm s j p.2

lemma mem_jointIndexFinset_of_weight_le {n r s i j : ℕ} (hr : 0 < r) (hs : 0 < s)
    {p : ℕ × ℕ} (hpw : r * (i + p.1) + s * (j + p.2) ≤ n) :
    p ∈ jointIndexFinset n r s i j := by
  have hri : i + p.1 ≤ n / r := by
    have hpart : r * (i + p.1) ≤ n := (Nat.le_add_right _ _).trans hpw
    exact (Nat.le_div_iff_mul_le hr).2 (by simpa [Nat.mul_comm] using hpart)
  have hsj : j + p.2 ≤ n / s := by
    have hpart : s * (j + p.2) ≤ n := (Nat.le_add_left _ _).trans hpw
    exact (Nat.le_div_iff_mul_le hs).2 (by simpa [Nat.mul_comm] using hpart)
  change p ∈ (((Finset.range (n / r - i + 1)).product
    (Finset.range (n / s - j + 1))).filter
      (fun q : ℕ × ℕ => r * (i + q.1) + s * (j + q.2) ≤ n))
  exact Finset.mem_filter.2 ⟨Finset.mem_product.2
    ⟨Finset.mem_range.2 (Nat.lt_succ_of_le
        (Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hri))),
      Finset.mem_range.2 (Nat.lt_succ_of_le
        (Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hsj)))⟩,
    hpw⟩

lemma card_subtype_eq_sum_joint_indicator {α : Type*} [Fintype α]
    (X Y : α → ℕ) (i j : ℕ) :
    (Fintype.card {a : α // X a = i ∧ Y a = j} : ℝ) =
      ∑ a : α, if X a = i ∧ Y a = j then (1 : ℝ) else 0 := by
  classical
  rw [Fintype.card_subtype]
  rw [Finset.sum_boole]

lemma joint_indicator_eq_kernel_sum {α : Type*} [Fintype α]
    (X Y : α → ℕ) {M N i j : ℕ} (hX : ∀ a : α, X a ≤ M)
    (hY : ∀ a : α, Y a ≤ N) (a : α) :
    (if X a = i ∧ Y a = j then (1 : ℝ) else 0) =
      ∑ u ∈ Finset.range (M - i + 1),
        ∑ v ∈ Finset.range (N - j + 1),
          (((-1 : ℝ) ^ u) *
              (((X a).descFactorial (i + u) : ℝ) /
                (u.factorial * (i.factorial : ℝ)))) *
            (((-1 : ℝ) ^ v) *
              (((Y a).descFactorial (j + v) : ℝ) /
                (v.factorial * (j.factorial : ℝ)))) := by
  classical
  have hx := Complete.factorial_kernel_sum_eq_indicator
    (M := M) (x := X a) (j := i) (hX a)
  have hy := Complete.factorial_kernel_sum_eq_indicator
    (M := N) (x := Y a) (j := j) (hY a)
  calc
    (if X a = i ∧ Y a = j then (1 : ℝ) else 0)
        = (if X a = i then (1 : ℝ) else 0) *
            (if Y a = j then (1 : ℝ) else 0) := by
          by_cases hxi : X a = i <;> by_cases hyj : Y a = j <;> simp [hxi, hyj]
    _ = (∑ u ∈ Finset.range (M - i + 1),
            ((-1 : ℝ) ^ u) *
              (((X a).descFactorial (i + u) : ℝ) /
                (u.factorial * (i.factorial : ℝ)))) *
          (∑ v ∈ Finset.range (N - j + 1),
            ((-1 : ℝ) ^ v) *
              (((Y a).descFactorial (j + v) : ℝ) /
                (v.factorial * (j.factorial : ℝ)))) := by
          rw [hx, hy]
    _ = ∑ u ∈ Finset.range (M - i + 1),
        ∑ v ∈ Finset.range (N - j + 1),
          (((-1 : ℝ) ^ u) *
              (((X a).descFactorial (i + u) : ℝ) /
                (u.factorial * (i.factorial : ℝ)))) *
            (((-1 : ℝ) ^ v) *
              (((Y a).descFactorial (j + v) : ℝ) /
                (v.factorial * (j.factorial : ℝ)))) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro u _hu
          rw [Finset.mul_sum]

/-- Bivariate finite pmf inversion in terms of mixed factorial moments. -/
lemma finite_joint_pmf_eq_factorial_moment_sum {α : Type*} [Fintype α]
    (X Y : α → ℕ) {M N i j : ℕ} (hX : ∀ a : α, X a ≤ M)
    (hY : ∀ a : α, Y a ≤ N) :
    (Fintype.card {a : α // X a = i ∧ Y a = j} : ℝ) /
        (Fintype.card α : ℝ) =
      ∑ u ∈ Finset.range (M - i + 1),
        ∑ v ∈ Finset.range (N - j + 1),
          ((((-1 : ℝ) ^ u) / (u.factorial * (i.factorial : ℝ))) *
              (((-1 : ℝ) ^ v) / (v.factorial * (j.factorial : ℝ)))) *
            ((∑ a : α,
              ((X a).descFactorial (i + u) : ℝ) *
                ((Y a).descFactorial (j + v) : ℝ)) /
              (Fintype.card α : ℝ)) := by
  classical
  let U := Finset.range (M - i + 1)
  let V := Finset.range (N - j + 1)
  let T : α → ℕ → ℕ → ℝ := fun a u v =>
    (((-1 : ℝ) ^ u) *
        (((X a).descFactorial (i + u) : ℝ) /
          (u.factorial * (i.factorial : ℝ)))) *
      (((-1 : ℝ) ^ v) *
        (((Y a).descFactorial (j + v) : ℝ) /
          (v.factorial * (j.factorial : ℝ))))
  have hpoint :
      ∀ a : α,
        (if X a = i ∧ Y a = j then (1 : ℝ) else 0) =
          ∑ u ∈ U, ∑ v ∈ V, T a u v := by
    intro a
    simpa [U, V, T] using
      joint_indicator_eq_kernel_sum (X := X) (Y := Y) hX hY a
  calc
    (Fintype.card {a : α // X a = i ∧ Y a = j} : ℝ) /
        (Fintype.card α : ℝ)
        = (∑ a : α, if X a = i ∧ Y a = j then (1 : ℝ) else 0) /
            (Fintype.card α : ℝ) := by
          rw [card_subtype_eq_sum_joint_indicator X Y i j]
    _ = (∑ a : α, ∑ u ∈ U, ∑ v ∈ V, T a u v) /
            (Fintype.card α : ℝ) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro a _ha
          exact hpoint a
    _ = (∑ u ∈ U, ∑ v ∈ V, ∑ a : α, T a u v) /
            (Fintype.card α : ℝ) := by
          congr 1
          calc
            (∑ a : α, ∑ u ∈ U, ∑ v ∈ V, T a u v)
                = ∑ u ∈ U, ∑ a : α, ∑ v ∈ V, T a u v := by
                  exact Finset.sum_comm
            _ = ∑ u ∈ U, ∑ v ∈ V, ∑ a : α, T a u v := by
                  refine Finset.sum_congr rfl ?_
                  intro u _hu
                  exact Finset.sum_comm
    _ = ∑ u ∈ U, ∑ v ∈ V,
          (∑ a : α, T a u v) / (Fintype.card α : ℝ) := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl (fun (u : ℕ) _hu => ?_)
          rw [Finset.sum_div]
    _ = ∑ u ∈ U, ∑ v ∈ V,
          ((((-1 : ℝ) ^ u) / (u.factorial * (i.factorial : ℝ))) *
              (((-1 : ℝ) ^ v) / (v.factorial * (j.factorial : ℝ)))) *
            ((∑ a : α,
              ((X a).descFactorial (i + u) : ℝ) *
                ((Y a).descFactorial (j + v) : ℝ)) /
              (Fintype.card α : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro u _hu
          refine Finset.sum_congr rfl ?_
          intro v _hv
          calc
            (∑ a : α, T a u v) / (Fintype.card α : ℝ)
                =
              ((((-1 : ℝ) ^ u) / (u.factorial * (i.factorial : ℝ))) *
                  (((-1 : ℝ) ^ v) / (v.factorial * (j.factorial : ℝ))) *
                (∑ a : α,
                  ((X a).descFactorial (i + u) : ℝ) *
                    ((Y a).descFactorial (j + v) : ℝ))) /
                  (Fintype.card α : ℝ) := by
              congr 1
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro a _ha
              simp [T]
              ring
            _ =
              ((((-1 : ℝ) ^ u) / (u.factorial * (i.factorial : ℝ))) *
                  (((-1 : ℝ) ^ v) / (v.factorial * (j.factorial : ℝ)))) *
                ((∑ a : α,
                  ((X a).descFactorial (i + u) : ℝ) *
                    ((Y a).descFactorial (j + v) : ℝ)) /
                  (Fintype.card α : ℝ)) := by
              ring
    _ = ∑ u ∈ Finset.range (M - i + 1),
        ∑ v ∈ Finset.range (N - j + 1),
          ((((-1 : ℝ) ^ u) / (u.factorial * (i.factorial : ℝ))) *
              (((-1 : ℝ) ^ v) / (v.factorial * (j.factorial : ℝ)))) *
            ((∑ a : α,
              ((X a).descFactorial (i + u) : ℝ) *
                ((Y a).descFactorial (j + v) : ℝ)) /
              (Fintype.card α : ℝ)) := by
          rfl

lemma Multiset.count_two_mul_le_sum (r s : ℕ) (hrs : r ≠ s) :
    ∀ m : Multiset ℕ, m.count r * r + m.count s * s ≤ m.sum := by
  intro m
  induction m using Multiset.induction_on with
  | empty =>
      simp
  | cons a m ih =>
      by_cases har : a = r
      · subst a
        have hsr : s ≠ r := Ne.symm hrs
        simp [hsr, Multiset.sum_cons, Nat.succ_mul]
        omega
      · by_cases has : a = s
        · subst a
          simp [hrs, Multiset.sum_cons, Nat.succ_mul]
          omega
        · have hle : m.count r * r + m.count s * s ≤ a + m.sum :=
            Nat.le_trans ih (Nat.le_add_left _ _)
          have hra : r ≠ a := fun h => har h.symm
          have hsa : s ≠ a := fun h => has h.symm
          simpa [Multiset.count_cons, hra, hsa, Multiset.sum_cons] using hle

lemma rCycleCount_one_eq_card_sub_cycleType_sum (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    rCycleCount n 1 σ = n - σ.cycleType.sum := by
  rw [rCycleCount_one]
  rw [← JointCycleMomentsNS.fixedPointCountIn_fin n σ]
  rw [JointCycleMomentsNS.fixedPointCountIn]
  rw [Equiv.Perm.card_fixedPoints]
  simp [Fintype.card_fin]

/-- Joint support bound: cycles of two distinct positive lengths use at most `n` labels. -/
lemma joint_rCycleCount_weight_le_card {n r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (hrs : r ≠ s) (σ : Equiv.Perm (Fin n)) :
    r * rCycleCount n r σ + s * rCycleCount n s σ ≤ n := by
  classical
  rcases eq_or_ne r 1 with rfl | hrne
  · have hsne : s ≠ 1 := by
      intro hs1
      exact hrs hs1.symm
    have hs_count :
        s * rCycleCount n s σ ≤ σ.cycleType.sum := by
      rw [rCycleCount_eq_cycleType_count_of_ne_one hsne σ]
      simpa [Nat.mul_comm] using
        Complete.Multiset.count_mul_le_sum s σ.cycleType
    have hfixed := rCycleCount_one_eq_card_sub_cycleType_sum n σ
    calc
      1 * rCycleCount n 1 σ + s * rCycleCount n s σ
          = (n - σ.cycleType.sum) + s * rCycleCount n s σ := by
            rw [hfixed]
            simp
      _ ≤ (n - σ.cycleType.sum) + σ.cycleType.sum := by
            exact Nat.add_le_add_left hs_count _
      _ = n := by
            exact Nat.sub_add_cancel (by
              simpa [Fintype.card_fin] using Equiv.Perm.sum_cycleType_le σ)
  · rcases eq_or_ne s 1 with rfl | hsne
    · have hr_count :
          r * rCycleCount n r σ ≤ σ.cycleType.sum := by
        rw [rCycleCount_eq_cycleType_count_of_ne_one hrne σ]
        simpa [Nat.mul_comm] using
          Complete.Multiset.count_mul_le_sum r σ.cycleType
      have hfixed := rCycleCount_one_eq_card_sub_cycleType_sum n σ
      calc
        r * rCycleCount n r σ + 1 * rCycleCount n 1 σ
            = r * rCycleCount n r σ + (n - σ.cycleType.sum) := by
              rw [hfixed]
              simp
        _ ≤ σ.cycleType.sum + (n - σ.cycleType.sum) := by
              exact Nat.add_le_add_right hr_count _
        _ = n := by
              rw [Nat.add_comm]
              exact Nat.sub_add_cancel (by
                simpa [Fintype.card_fin] using Equiv.Perm.sum_cycleType_le σ)
    · have htwo :
          r * rCycleCount n r σ + s * rCycleCount n s σ ≤ σ.cycleType.sum := by
        rw [rCycleCount_eq_cycleType_count_of_ne_one hrne σ]
        rw [rCycleCount_eq_cycleType_count_of_ne_one hsne σ]
        simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Multiset.count_two_mul_le_sum r s hrs σ.cycleType
      exact htwo.trans (by
        simpa [Fintype.card_fin] using Equiv.Perm.sum_cycleType_le σ)

lemma joint_factorial_moment_zero_of_lt {n r s a b : ℕ} (hr : 0 < r) (hs : 0 < s)
    (hrs : r ≠ s) (h : n < r * a + s * b) :
    (∑ σ : Equiv.Perm (Fin n),
        ((rCycleCount n r σ).descFactorial a : ℝ) *
          ((rCycleCount n s σ).descFactorial b : ℝ)) /
      (n.factorial : ℝ) = 0 := by
  classical
  suffices
      (∑ σ : Equiv.Perm (Fin n),
        ((rCycleCount n r σ).descFactorial a : ℝ) *
          ((rCycleCount n s σ).descFactorial b : ℝ)) = 0 by
    rw [this]
    simp
  refine Finset.sum_eq_zero ?_
  intro σ _hσ
  by_cases ha : a ≤ rCycleCount n r σ
  · by_cases hb : b ≤ rCycleCount n s σ
    · have huse :
          r * a + s * b ≤
            r * rCycleCount n r σ + s * rCycleCount n s σ := by
        exact Nat.add_le_add
          (Nat.mul_le_mul_left r ha) (Nat.mul_le_mul_left s hb)
      have hcard := joint_rCycleCount_weight_le_card (n := n) (r := r) (s := s)
        hr hs hrs σ
      have : r * a + s * b ≤ n := huse.trans hcard
      omega
    · have hbzero : (rCycleCount n s σ).descFactorial b = 0 :=
        (Nat.descFactorial_eq_zero_iff_lt).2 (Nat.lt_of_not_ge hb)
      simp [hbzero]
  · have hazero : (rCycleCount n r σ).descFactorial a = 0 :=
      (Nat.descFactorial_eq_zero_iff_lt).2 (Nat.lt_of_not_ge ha)
    simp [hazero]

lemma joint_factorial_moment_eval {n r s a b : ℕ} (hr : 0 < r) (hs : 0 < s)
    (hrs : r ≠ s) :
    (∑ σ : Equiv.Perm (Fin n),
        ((rCycleCount n r σ).descFactorial a : ℝ) *
          ((rCycleCount n s σ).descFactorial b : ℝ)) /
      (n.factorial : ℝ) =
      if r * a + s * b ≤ n then
        (r : ℝ) ^ (-(a : ℤ)) * (s : ℝ) ^ (-(b : ℤ))
      else 0 := by
  classical
  by_cases hle : r * a + s * b ≤ n
  · simp [hle]
    simpa [FixedPointsPoissonNS.uniformPermExpectation] using
      JointCycleMomentsNS.factorialMoment_two_rCycle_of_pos
        (n := n) (r := r) (s := s) (a := a) (b := b) hr hs hrs hle
  · have hlt : n < r * a + s * b := Nat.lt_of_not_ge hle
    simp [hle, joint_factorial_moment_zero_of_lt (n := n) (r := r) (s := s)
      (a := a) (b := b) hr hs hrs hlt]

/-- If two distinct cycle lengths fit together, their product moment is the product
of the two means. -/
theorem joint_product_expectation_eq_inv_mul_inv_of_le {n r s : ℕ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≠ s) (h : r + s ≤ n) :
    FixedPointsPoissonNS.uniformPermExpectation n
      (fun σ => (rCycleCount n r σ : ℝ) * (rCycleCount n s σ : ℝ)) =
        (r : ℝ)⁻¹ * (s : ℝ)⁻¹ := by
  have hmom := JointCycleMomentsNS.factorialMoment_two_rCycle_of_pos
    (n := n) (r := r) (s := s) (a := 1) (b := 1) hr hs hrs (by simpa using h)
  simpa [FixedPointsPoissonNS.uniformPermExpectation, Nat.descFactorial_one, zpow_neg_one]
    using hmom

/-- If the two requested cycle lengths do not both fit, then the product moment is zero. -/
theorem joint_product_expectation_eq_zero_of_lt {n r s : ℕ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≠ s) (h : n < r + s) :
    FixedPointsPoissonNS.uniformPermExpectation n
      (fun σ => (rCycleCount n r σ : ℝ) * (rCycleCount n s σ : ℝ)) = 0 := by
  have hzero := joint_factorial_moment_zero_of_lt
    (n := n) (r := r) (s := s) (a := 1) (b := 1) hr hs hrs (by simpa using h)
  simpa [FixedPointsPoissonNS.uniformPermExpectation, Nat.descFactorial_one] using hzero

/-- Tail covariance for two distinct cycle lengths that separately fit but cannot coexist. -/
theorem joint_covariance_eq_neg_inv_mul_inv_of_lt {n r s : ℕ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≠ s) (hrn : r ≤ n) (hsn : s ≤ n)
    (h : n < r + s) :
    FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (rCycleCount n r σ : ℝ) * (rCycleCount n s σ : ℝ)) -
      FixedPointsPoissonNS.uniformPermExpectation n (fun σ => (rCycleCount n r σ : ℝ)) *
        FixedPointsPoissonNS.uniformPermExpectation n (fun σ => (rCycleCount n s σ : ℝ)) =
        -((r : ℝ)⁻¹ * (s : ℝ)⁻¹) := by
  rw [joint_product_expectation_eq_zero_of_lt hr hs hrs h,
    rCycle_mean_eq_inv hr hrn, rCycle_mean_eq_inv hs hsn]
  simp

theorem jointRCyclePMF_eq_formula {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (hrs : r ≠ s) :
    ∀ i j n : ℕ, jointRCyclePMF n r s i j = jointRCyclePMFFormula n r s i j := by
  classical
  intro i j n
  have hinv := finite_joint_pmf_eq_factorial_moment_sum
    (α := Equiv.Perm (Fin n))
    (X := fun σ : Equiv.Perm (Fin n) => rCycleCount n r σ)
    (Y := fun σ : Equiv.Perm (Fin n) => rCycleCount n s σ)
    (M := n / r) (N := n / s) (i := i) (j := j)
    (fun σ => Complete.rCycleCount_le_div (n := n) (r := r) hr σ)
    (fun σ => Complete.rCycleCount_le_div (n := n) (r := s) hs σ)
  have hpmf :
      jointRCyclePMF n r s i j =
        ∑ u ∈ Finset.range (n / r - i + 1),
          ∑ v ∈ Finset.range (n / s - j + 1),
            ((((-1 : ℝ) ^ u) / (u.factorial * (i.factorial : ℝ))) *
                (((-1 : ℝ) ^ v) / (v.factorial * (j.factorial : ℝ)))) *
              ((∑ σ : Equiv.Perm (Fin n),
                ((rCycleCount n r σ).descFactorial (i + u) : ℝ) *
                  ((rCycleCount n s σ).descFactorial (j + v) : ℝ)) /
                (n.factorial : ℝ)) := by
    unfold jointRCyclePMF
    simpa [Fintype.card_perm, Fintype.card_fin] using hinv
  rw [hpmf]
  unfold jointRCyclePMFFormula jointIndexFinset
  rw [Finset.sum_filter]
  calc
    (∑ u ∈ Finset.range (n / r - i + 1),
      ∑ v ∈ Finset.range (n / s - j + 1),
        ((((-1 : ℝ) ^ u) / (u.factorial * (i.factorial : ℝ))) *
            (((-1 : ℝ) ^ v) / (v.factorial * (j.factorial : ℝ)))) *
          ((∑ σ : Equiv.Perm (Fin n),
            ((rCycleCount n r σ).descFactorial (i + u) : ℝ) *
              ((rCycleCount n s σ).descFactorial (j + v) : ℝ)) /
            (n.factorial : ℝ)))
        =
      ∑ u ∈ Finset.range (n / r - i + 1),
        ∑ v ∈ Finset.range (n / s - j + 1),
          if r * (i + u) + s * (j + v) ≤ n then
            oneDimTerm r i u * oneDimTerm s j v
          else 0 := by
          refine Finset.sum_congr rfl ?_
          intro u hu
          refine Finset.sum_congr rfl ?_
          intro v hv
          by_cases hle : r * (i + u) + s * (j + v) ≤ n
          · rw [joint_factorial_moment_eval (n := n) (r := r) (s := s)
              (a := i + u) (b := j + v) hr hs hrs]
            simp [hle, oneDimTerm]
            ring
          · rw [joint_factorial_moment_eval (n := n) (r := r) (s := s)
              (a := i + u) (b := j + v) hr hs hrs]
            simp [hle]
    _ = ∑ a ∈ (Finset.range (n / r - i + 1)).product
          (Finset.range (n / s - j + 1)),
        if r * (i + a.1) + s * (j + a.2) ≤ n then
          oneDimTerm r i a.1 * oneDimTerm s j a.2
        else 0 := by
          exact (Finset.sum_product'
            (s := Finset.range (n / r - i + 1))
            (t := Finset.range (n / s - j + 1))
            (f := fun u v =>
              if r * (i + u) + s * (j + v) ≤ n then
                oneDimTerm r i u * oneDimTerm s j v
              else 0)).symm

lemma oneDimTerm_hasSum {r : ℕ} (hr : 0 < r) (i : ℕ) :
    HasSum (fun a : ℕ => oneDimTerm r i a)
      (ProbabilityTheory.poissonPMFReal (poissonRate r) i) := by
  have hexp :
      HasSum (fun a : ℕ => ((-(r : ℝ)⁻¹) ^ a) / (a.factorial : ℝ))
        (Real.exp (-(r : ℝ)⁻¹)) := by
    simpa [← Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (-(r : ℝ)⁻¹))
  have hmain := hexp.mul_left (((r : ℝ) ^ i * (i.factorial : ℝ))⁻¹)
  convert hmain using 1
  · ext a
    rw [oneDimTerm]
    exact Complete.factorial_moment_term_eq_expPartial_term r i a hr
  · rw [ProbabilityTheory.poissonPMFReal]
    simp [poissonRate]
    have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
    have hifac : (i.factorial : ℝ) ≠ 0 := by positivity
    field_simp [hrR, pow_ne_zero i hrR, hifac]

set_option maxHeartbeats 1000000 in
lemma jointIndexFinset_tendsto_atTop {r s i j : ℕ} (hr : 0 < r) (hs : 0 < s) :
    Tendsto (fun n : ℕ => jointIndexFinset n r s i j) atTop atTop := by
  classical
  refine Filter.tendsto_atTop_finset_of_monotone ?_ ?_
  · intro n m hnm p hp
    change p ∈ (((Finset.range (n / r - i + 1)).product
      (Finset.range (n / s - j + 1))).filter
        (fun q : ℕ × ℕ => r * (i + q.1) + s * (j + q.2) ≤ n)) at hp
    exact mem_jointIndexFinset_of_weight_le (n := m) (r := r) (s := s)
      (i := i) (j := j) hr hs ((Finset.mem_filter.mp hp).2.trans hnm)
  · intro p
    exact ⟨r * (i + p.1) + s * (j + p.2),
      mem_jointIndexFinset_of_weight_le (n := r * (i + p.1) + s * (j + p.2))
        (r := r) (s := s) (i := i) (j := j) hr hs le_rfl⟩

set_option maxHeartbeats 1000000 in
theorem jointRCyclePMFFormula_tendsto_poisson_product {r s : ℕ}
    (hr : 0 < r) (hs : 0 < s) (i j : ℕ) :
    Tendsto (fun n : ℕ => jointRCyclePMFFormula n r s i j) atTop
      (𝓝 (ProbabilityTheory.poissonPMFReal (poissonRate r) i *
        ProbabilityTheory.poissonPMFReal (poissonRate s) j)) := by
  have hrsum := oneDimTerm_hasSum (r := r) hr i
  have hssum := oneDimTerm_hasSum (r := s) hs j
  have hprod_abs' :
      Summable fun p : ℕ × ℕ =>
        |oneDimTerm r i p.1| * |oneDimTerm s j p.2| :=
    hrsum.summable.abs.mul_of_nonneg hssum.summable.abs
      (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)
  have hprod_abs :
      Summable fun p : ℕ × ℕ =>
        ‖oneDimTerm r i p.1 * oneDimTerm s j p.2‖ := by
    simpa [Real.norm_eq_abs, abs_mul] using hprod_abs'
  have hprod_summable :
      Summable fun p : ℕ × ℕ => oneDimTerm r i p.1 * oneDimTerm s j p.2 :=
    Summable.of_norm hprod_abs
  have hprod_hasSum :
      HasSum (fun p : ℕ × ℕ => oneDimTerm r i p.1 * oneDimTerm s j p.2)
        (ProbabilityTheory.poissonPMFReal (poissonRate r) i *
          ProbabilityTheory.poissonPMFReal (poissonRate s) j) :=
    hrsum.mul hssum hprod_summable
  change Tendsto
    (fun n : ℕ => ∑ p ∈ jointIndexFinset n r s i j,
      oneDimTerm r i p.1 * oneDimTerm s j p.2)
    atTop
    (𝓝 (ProbabilityTheory.poissonPMFReal (poissonRate r) i *
      ProbabilityTheory.poissonPMFReal (poissonRate s) j))
  change Tendsto
    (fun t : Finset (ℕ × ℕ) => ∑ p ∈ t,
      oneDimTerm r i p.1 * oneDimTerm s j p.2)
    atTop
    (𝓝 (ProbabilityTheory.poissonPMFReal (poissonRate r) i *
      ProbabilityTheory.poissonPMFReal (poissonRate s) j)) at hprod_hasSum
  exact hprod_hasSum.comp (jointIndexFinset_tendsto_atTop (r := r) (s := s)
    (i := i) (j := j) hr hs)

theorem jointRCyclePMF_tendsto_poisson_product {r s : ℕ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≠ s) (i j : ℕ) :
    Tendsto (fun n : ℕ => jointRCyclePMF n r s i j) atTop
      (𝓝 (ProbabilityTheory.poissonPMFReal (poissonRate r) i *
        ProbabilityTheory.poissonPMFReal (poissonRate s) j)) := by
  exact Tendsto.congr' (Eventually.of_forall fun n =>
    (jointRCyclePMF_eq_formula (r := r) (s := s) hr hs hrs i j n).symm)
    (jointRCyclePMFFormula_tendsto_poisson_product (r := r) (s := s) hr hs i j)

lemma joint_law_singleton (n r s i j : ℕ) :
    (Measure.map (fun σ : Equiv.Perm (Fin n) =>
        (rCycleCount n r σ, rCycleCount n s σ)) (uniformPermMeasure n))
      ({(i, j)} : Set (ℕ × ℕ)) =
        ENNReal.ofReal (jointRCyclePMF n r s i j) := by
  classical
  have hpre :
      (fun σ : Equiv.Perm (Fin n) =>
        (rCycleCount n r σ, rCycleCount n s σ)) ⁻¹' ({(i, j)} : Set (ℕ × ℕ)) =
        {σ : Equiv.Perm (Fin n) |
          rCycleCount n r σ = i ∧ rCycleCount n s σ = j} := by
    ext σ
    simp
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton (i, j)), hpre]
  unfold uniformPermMeasure
  rw [PMF.toMeasure_uniformOfFintype_apply]
  · rw [Fintype.card_perm, Fintype.card_fin]
    change
      (Fintype.card {σ : Equiv.Perm (Fin n) //
        rCycleCount n r σ = i ∧ rCycleCount n s σ = j} : ℝ≥0∞) /
          (n.factorial : ℝ≥0∞) =
        ENNReal.ofReal (jointRCyclePMF n r s i j)
    unfold jointRCyclePMF
    rw [ENNReal.ofReal_div_of_pos]
    · congr
      · exact_mod_cast rfl
      · exact_mod_cast rfl
    · positivity
  · simp

lemma poissonProductMeasure_singleton (ρ τ : ℝ≥0) (i j : ℕ) :
    (poissonProductMeasure ρ τ : Measure (ℕ × ℕ)) ({(i, j)} : Set (ℕ × ℕ)) =
      ENNReal.ofReal
        (ProbabilityTheory.poissonPMFReal ρ i *
          ProbabilityTheory.poissonPMFReal τ j) := by
  have hrect : ({(i, j)} : Set (ℕ × ℕ)) = ({i} : Set ℕ) ×ˢ ({j} : Set ℕ) := by
    ext p
    cases p
    simp
  rw [poissonProductMeasure, hrect]
  change
      ((ProbabilityTheory.poissonMeasure ρ).prod
        (ProbabilityTheory.poissonMeasure τ)) (({i} : Set ℕ) ×ˢ ({j} : Set ℕ)) =
      ENNReal.ofReal
        (ProbabilityTheory.poissonPMFReal ρ i *
          ProbabilityTheory.poissonPMFReal τ j)
  rw [Measure.prod_prod]
  rw [poisson_law_singleton ρ i, poisson_law_singleton τ j]
  rw [← ENNReal.ofReal_mul (ProbabilityTheory.poissonPMFReal_nonneg)]

/-- On `ℕ × ℕ`, pointwise singleton convergence implies weak convergence. -/
theorem probabilityMeasure_nat_prod_tendsto_of_tendsto_singleton
    {μs : ℕ → ProbabilityMeasure (ℕ × ℕ)} {μ : ProbabilityMeasure (ℕ × ℕ)}
    (h : ∀ p : ℕ × ℕ,
      Tendsto (fun n : ℕ => (μs n : Measure (ℕ × ℕ)) ({p} : Set (ℕ × ℕ))) atTop
        (𝓝 ((μ : Measure (ℕ × ℕ)) ({p} : Set (ℕ × ℕ))))) :
    Tendsto μs atTop (𝓝 μ) := by
  classical
  refine MeasureTheory.tendsto_of_forall_isOpen_le_liminf_nat' ?_
  intro G _hG
  have hfinite_le :
      ∀ t : Finset (ℕ × ℕ), (∀ p ∈ t, p ∈ G) →
        (∑ p ∈ t, (μ : Measure (ℕ × ℕ)) ({p} : Set (ℕ × ℕ))) ≤
          atTop.liminf (fun n : ℕ => (μs n : Measure (ℕ × ℕ)) G) := by
    intro t htG
    have hsum_tendsto :
        Tendsto
          (fun n : ℕ => ∑ p ∈ t, (μs n : Measure (ℕ × ℕ)) ({p} : Set (ℕ × ℕ)))
          atTop
          (𝓝 (∑ p ∈ t, (μ : Measure (ℕ × ℕ)) ({p} : Set (ℕ × ℕ)))) :=
      tendsto_finset_sum t (fun p _hp => h p)
    rw [← hsum_tendsto.liminf_eq]
    refine Filter.liminf_le_liminf (Eventually.of_forall ?_)
      (by isBoundedDefault)
      (by isBoundedDefault)
    intro n
    have hdisj : (t : Set (ℕ × ℕ)).PairwiseDisjoint
        (fun p => ({p} : Set (ℕ × ℕ))) := by
      intro a _ha b _hb hne
      change Disjoint ({a} : Set (ℕ × ℕ)) ({b} : Set (ℕ × ℕ))
      rw [Set.disjoint_singleton_left]
      simpa using hne
    calc
      (∑ p ∈ t, (μs n : Measure (ℕ × ℕ)) ({p} : Set (ℕ × ℕ)))
          = (μs n : Measure (ℕ × ℕ)) (⋃ p ∈ t, ({p} : Set (ℕ × ℕ))) := by
              exact (MeasureTheory.measure_biUnion_finset hdisj
                (fun p _hp => measurableSet_singleton p)).symm
      _ ≤ (μs n : Measure (ℕ × ℕ)) G := by
              refine measure_mono ?_
              intro x hx
              simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hx
              rcases hx with ⟨p, hp, hxp⟩
              subst hxp
              exact htG x hp
  have hμG :
      (μ : Measure (ℕ × ℕ)) G =
        ∑' p : ℕ × ℕ, G.indicator
          (fun p => (μ : Measure (ℕ × ℕ)) ({p} : Set (ℕ × ℕ))) p := by
    exact (Measure.tsum_indicator_apply_singleton (μ : Measure (ℕ × ℕ)) G
      G.to_countable.measurableSet).symm
  rw [hμG, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le ?_
  intro t
  calc
    (∑ p ∈ t, G.indicator
        (fun p => (μ : Measure (ℕ × ℕ)) ({p} : Set (ℕ × ℕ))) p)
        = ∑ p ∈ t.filter (fun p => p ∈ G),
            (μ : Measure (ℕ × ℕ)) ({p} : Set (ℕ × ℕ)) := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl ?_
            intro p _hp
            by_cases hpG : p ∈ G
            · simp [hpG]
            · simp [hpG]
    _ ≤ atTop.liminf (fun n : ℕ => (μs n : Measure (ℕ × ℕ)) G) :=
            hfinite_le (t.filter (fun p => p ∈ G))
              (fun p hp => (Finset.mem_filter.mp hp).2)

/-- A real-valued pmf version of the bivariate discrete bridge. -/
theorem probabilityMeasure_nat_prod_tendsto_of_tendsto_pmfReal
    {p : ℕ → ℕ × ℕ → ℝ} {q : ℕ × ℕ → ℝ}
    {μs : ℕ → ProbabilityMeasure (ℕ × ℕ)} {μ : ProbabilityMeasure (ℕ × ℕ)}
    (hp : ∀ n x, (μs n : Measure (ℕ × ℕ)) ({x} : Set (ℕ × ℕ)) =
      ENNReal.ofReal (p n x))
    (hq : ∀ x, (μ : Measure (ℕ × ℕ)) ({x} : Set (ℕ × ℕ)) =
      ENNReal.ofReal (q x))
    (hconv : ∀ x : ℕ × ℕ, Tendsto (fun n : ℕ => p n x) atTop (𝓝 (q x))) :
    Tendsto μs atTop (𝓝 μ) :=
  probabilityMeasure_nat_prod_tendsto_of_tendsto_singleton fun x => by
    simpa [hp, hq] using ENNReal.tendsto_ofReal (hconv x)

theorem jointLaw_tendsto_poissonProduct {r s : ℕ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≠ s) :
    Tendsto (fun n : ℕ => jointLaw n r s) atTop
      (𝓝 (poissonProductMeasure (poissonRate r) (poissonRate s))) := by
  refine probabilityMeasure_nat_prod_tendsto_of_tendsto_pmfReal
    (p := fun n x => jointRCyclePMF n r s x.1 x.2)
    (q := fun x =>
      ProbabilityTheory.poissonPMFReal (poissonRate r) x.1 *
        ProbabilityTheory.poissonPMFReal (poissonRate s) x.2) ?_ ?_ ?_
  · intro n x
    cases x with
    | mk i j =>
        exact joint_law_singleton n r s i j
  · intro x
    cases x with
    | mk i j =>
        exact poissonProductMeasure_singleton (poissonRate r) (poissonRate s) i j
  · intro x
    cases x with
    | mk i j =>
        exact jointRCyclePMF_tendsto_poisson_product
          (r := r) (s := s) hr hs hrs i j

#print axioms joint_product_expectation_eq_inv_mul_inv_of_le
#print axioms joint_product_expectation_eq_zero_of_lt
#print axioms joint_covariance_eq_neg_inv_mul_inv_of_lt

end Bivariate
end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
