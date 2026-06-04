import Mathlib
import AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoisson
import AnalyticCombinatorics.Ch9.LimitLaws.RCyclesFactorialMoment

/-!
# Completion of the fixed-length cycle Poisson limit

This file proves the finite Bonferroni/factorial-moment inversion needed to
identify the genuine `r`-cycle pmf with the closed inclusion-exclusion formula.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS
namespace Complete

lemma Multiset.count_mul_le_sum (r : ℕ) :
    ∀ s : Multiset ℕ, s.count r * r ≤ s.sum := by
  intro s
  induction s using Multiset.induction_on with
  | empty =>
      simp
  | cons a s ih =>
      by_cases h : a = r
      · subst a
        simp [Nat.succ_mul, Multiset.sum_cons, Nat.add_comm, ih]
      · have hle : s.count r * r ≤ a + s.sum :=
          Nat.le_trans ih (Nat.le_add_left _ _)
        have h' : r ≠ a := fun hra => h hra.symm
        simpa [Multiset.count_cons, h', Multiset.sum_cons] using hle

lemma cycleType_count_mul_le_card {α : Type*} [Fintype α] [DecidableEq α]
    (r : ℕ) (σ : Equiv.Perm α) :
    σ.cycleType.count r * r ≤ Fintype.card α := by
  calc
    σ.cycleType.count r * r ≤ σ.cycleType.sum :=
      Multiset.count_mul_le_sum r σ.cycleType
    _ = σ.support.card := Equiv.Perm.sum_cycleType σ
    _ ≤ Fintype.card α := by
      simpa using σ.support.card_le_univ

lemma rCycleCount_mul_le_card {n r : ℕ} (hr : 0 < r)
    (σ : Equiv.Perm (Fin n)) :
    rCycleCount n r σ * r ≤ n := by
  rcases eq_or_ne r 1 with rfl | hrne
  · simpa [rCycleCount, FixedPointsPoissonNS.fixedPointCount, Fintype.card_fin] using
      Fintype.card_subtype_le (fun i : Fin n => σ i = i)
  · rw [rCycleCount_eq_cycleType_count_of_ne_one hrne σ]
    simpa [Fintype.card_fin] using
      cycleType_count_mul_le_card (α := Fin n) r σ

lemma rCycleCount_le_div {n r : ℕ} (hr : 0 < r)
    (σ : Equiv.Perm (Fin n)) :
    rCycleCount n r σ ≤ n / r := by
  exact (Nat.le_div_iff_mul_le hr).2 (rCycleCount_mul_le_card (n := n) (r := r) hr σ)

lemma alternating_choose_sum_range (m : ℕ) :
    (∑ i ∈ Finset.range (m + 1), ((-1 : ℝ) ^ i * (m.choose i : ℝ))) =
      if m = 0 then 1 else 0 := by
  have h := Int.alternating_sum_range_choose (n := m)
  exact_mod_cast h

lemma alternating_choose_sum_range_of_le {m N : ℕ} (hmN : m ≤ N) :
    (∑ i ∈ Finset.range (N + 1), ((-1 : ℝ) ^ i * (m.choose i : ℝ))) =
      if m = 0 then 1 else 0 := by
  have hsubset : Finset.range (m + 1) ⊆ Finset.range (N + 1) := by
    intro i hi
    exact Finset.mem_range.mpr
      (Nat.lt_of_lt_of_le (Finset.mem_range.mp hi) (Nat.succ_le_succ hmN))
  rw [← alternating_choose_sum_range m]
  exact (Finset.sum_subset hsubset (by
    intro i hiN him
    have hmi : m < i := by
      exact Nat.lt_of_not_ge (fun hi_le_m => him (Finset.mem_range.mpr (Nat.lt_succ_of_le hi_le_m)))
    rw [Nat.choose_eq_zero_of_lt hmi]
    simp)).symm

lemma descFactorial_div_factorials_eq_choose_mul {x j k : ℕ} (hjk : j ≤ k) :
    (x.descFactorial k : ℝ) / ((k - j).factorial * (j.factorial : ℝ)) =
      (x.choose k : ℝ) * (k.choose j : ℝ) := by
  have hfacNat : k.choose j * j.factorial * (k - j).factorial = k.factorial :=
    Nat.choose_mul_factorial_mul_factorial hjk
  have hfacReal : (k.choose j : ℝ) * (j.factorial : ℝ) * ((k - j).factorial : ℝ) =
      (k.factorial : ℝ) := by
    exact_mod_cast hfacNat
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  norm_num
  have hjfac : (j.factorial : ℝ) ≠ 0 := by positivity
  have hkjfac : ((k - j).factorial : ℝ) ≠ 0 := by positivity
  have hkchoose : (k.choose j : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hjk))
  field_simp [hjfac, hkjfac, hkchoose]
  rw [← hfacReal]
  ring

lemma descFactorial_add_div_factorials_eq_choose_mul (x j i : ℕ) :
    (x.descFactorial (j + i) : ℝ) / (i.factorial * (j.factorial : ℝ)) =
      (x.choose j : ℝ) * ((x - j).choose i : ℝ) := by
  have hdesc := descFactorial_div_factorials_eq_choose_mul
    (x := x) (j := j) (k := j + i) (Nat.le_add_right j i)
  have hchoose := Nat.choose_mul
    (n := x) (k := j + i) (s := j) (Nat.le_add_right j i)
  have hchooseReal :
      (x.choose (j + i) : ℝ) * ((j + i).choose j : ℝ) =
        (x.choose j : ℝ) * ((x - j).choose i : ℝ) := by
    simpa [Nat.add_sub_cancel_left] using (show
      ((x.choose (j + i) * (j + i).choose j : ℕ) : ℝ) =
        (x.choose j * (x - j).choose ((j + i) - j) : ℕ) by
          exact_mod_cast hchoose)
  simpa [Nat.add_sub_cancel_left] using hdesc.trans hchooseReal

lemma factorial_kernel_sum_eq_indicator {M x j : ℕ} (hxM : x ≤ M) :
    (∑ i ∈ Finset.range (M - j + 1),
        ((-1 : ℝ) ^ i) *
          ((x.descFactorial (j + i) : ℝ) / (i.factorial * (j.factorial : ℝ)))) =
      if x = j then 1 else 0 := by
  by_cases hjx : j ≤ x
  · have hsub : x - j ≤ M - j := Nat.sub_le_sub_right hxM j
    calc
      (∑ i ∈ Finset.range (M - j + 1),
          ((-1 : ℝ) ^ i) *
            ((x.descFactorial (j + i) : ℝ) / (i.factorial * (j.factorial : ℝ))))
          = ∑ i ∈ Finset.range (M - j + 1),
              (x.choose j : ℝ) * (((-1 : ℝ) ^ i) * ((x - j).choose i : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [descFactorial_add_div_factorials_eq_choose_mul]
            ring
      _ = (x.choose j : ℝ) *
            (∑ i ∈ Finset.range (M - j + 1),
              ((-1 : ℝ) ^ i) * ((x - j).choose i : ℝ)) := by
            rw [Finset.mul_sum]
      _ = (x.choose j : ℝ) * (if x - j = 0 then 1 else 0) := by
            rw [alternating_choose_sum_range_of_le hsub]
      _ = if x = j then 1 else 0 := by
            by_cases hxj : x = j
            · subst x
              simp
            · have hxsub : x - j ≠ 0 := by omega
              simp [hxj, hxsub]
  · have hxlt : x < j := Nat.lt_of_not_ge hjx
    have hzero : ∀ i : ℕ, x.descFactorial (j + i) = 0 := by
      intro i
      exact (Nat.descFactorial_eq_zero_iff_lt).2 (Nat.lt_of_lt_of_le hxlt (Nat.le_add_right j i))
    have hxj : x ≠ j := by omega
    simp [hzero, hxj]

lemma card_subtype_eq_sum_indicator {α : Type*} [Fintype α]
    (X : α → ℕ) (j : ℕ) :
    (Fintype.card {a : α // X a = j} : ℝ) =
      ∑ a : α, if X a = j then (1 : ℝ) else 0 := by
  rw [Fintype.card_subtype]
  rw [Finset.sum_boole]

lemma finite_pmf_eq_factorial_moment_sum {α : Type*} [Fintype α]
    (X : α → ℕ) {M j : ℕ} (hX : ∀ a : α, X a ≤ M) :
    (Fintype.card {a : α // X a = j} : ℝ) / (Fintype.card α : ℝ) =
      ∑ i ∈ Finset.range (M - j + 1),
        (((-1 : ℝ) ^ i) / (i.factorial * (j.factorial : ℝ))) *
          ((∑ a : α, ((X a).descFactorial (j + i) : ℝ)) / (Fintype.card α : ℝ)) := by
  have hpoint :
      ∀ a : α,
        (if X a = j then (1 : ℝ) else 0) =
          ∑ i ∈ Finset.range (M - j + 1),
            ((-1 : ℝ) ^ i) *
              (((X a).descFactorial (j + i) : ℝ) /
                (i.factorial * (j.factorial : ℝ))) := by
    intro a
    exact (factorial_kernel_sum_eq_indicator (M := M) (x := X a) (j := j) (hX a)).symm
  calc
    (Fintype.card {a : α // X a = j} : ℝ) / (Fintype.card α : ℝ)
        = (∑ a : α, if X a = j then (1 : ℝ) else 0) /
            (Fintype.card α : ℝ) := by
          rw [card_subtype_eq_sum_indicator X j]
    _ = (∑ a : α, ∑ i ∈ Finset.range (M - j + 1),
            ((-1 : ℝ) ^ i) *
              (((X a).descFactorial (j + i) : ℝ) /
                (i.factorial * (j.factorial : ℝ)))) /
          (Fintype.card α : ℝ) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro a _ha
          exact hpoint a
    _ = (∑ i ∈ Finset.range (M - j + 1), ∑ a : α,
            ((-1 : ℝ) ^ i) *
              (((X a).descFactorial (j + i) : ℝ) /
                (i.factorial * (j.factorial : ℝ)))) /
          (Fintype.card α : ℝ) := by
          rw [Finset.sum_comm]
    _ = ∑ i ∈ Finset.range (M - j + 1),
        (∑ a : α,
            ((-1 : ℝ) ^ i) *
              (((X a).descFactorial (j + i) : ℝ) /
                (i.factorial * (j.factorial : ℝ)))) /
          (Fintype.card α : ℝ) := by
          rw [Finset.sum_div]
    _ = ∑ i ∈ Finset.range (M - j + 1),
        (((-1 : ℝ) ^ i) / (i.factorial * (j.factorial : ℝ))) *
          ((∑ a : α, ((X a).descFactorial (j + i) : ℝ)) / (Fintype.card α : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          calc
            (∑ a : α,
                ((-1 : ℝ) ^ i) *
                  (((X a).descFactorial (j + i) : ℝ) /
                    (i.factorial * (j.factorial : ℝ)))) /
                (Fintype.card α : ℝ)
                =
                (((( -1 : ℝ) ^ i) / (i.factorial * (j.factorial : ℝ))) *
                  (∑ a : α, ((X a).descFactorial (j + i) : ℝ))) /
                (Fintype.card α : ℝ) := by
                  congr 1
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl ?_
                  intro a _ha
                  ring
            _ = (((-1 : ℝ) ^ i) / (i.factorial * (j.factorial : ℝ))) *
                  ((∑ a : α, ((X a).descFactorial (j + i) : ℝ)) /
                    (Fintype.card α : ℝ)) := by
                  ring

lemma zpow_neg_nat_add_eq_inv_mul (r j i : ℕ) (hr : 0 < r) :
    ((r : ℝ) ^ (-(j + i : ℤ))) =
      (((r : ℝ) ^ j * (r : ℝ) ^ i)⁻¹) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  rw [zpow_neg]
  rw [zpow_add₀ hrR]
  rw [zpow_natCast, zpow_natCast]

lemma factorial_moment_term_eq_expPartial_term (r j i : ℕ) (hr : 0 < r) :
    (((-1 : ℝ) ^ i) / (i.factorial * (j.factorial : ℝ))) *
        ((r : ℝ) ^ (-(j + i : ℤ))) =
      (((r : ℝ) ^ j * (j.factorial : ℝ))⁻¹) *
        (((-(r : ℝ)⁻¹) ^ i) / (i.factorial : ℝ)) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hifac : (i.factorial : ℝ) ≠ 0 := by positivity
  have hjfac : (j.factorial : ℝ) ≠ 0 := by positivity
  rw [zpow_neg_nat_add_eq_inv_mul r j i hr]
  have hneg : (-(r : ℝ)⁻¹) = (-1 : ℝ) * (r : ℝ)⁻¹ := by ring
  rw [hneg, mul_pow, inv_pow]
  field_simp [hrR, hifac, hjfac, pow_ne_zero i hrR, pow_ne_zero j hrR]

lemma factorial_moment_sum_eq_formula_sum {n r j : ℕ} (hr : 0 < r) :
    (∑ i ∈ Finset.range (n / r - j + 1),
        (((-1 : ℝ) ^ i) / (i.factorial * (j.factorial : ℝ))) *
          ((r : ℝ) ^ (-(j + i : ℤ)))) =
      (((r : ℝ) ^ j * (j.factorial : ℝ))⁻¹) *
        expPartial (-(r : ℝ)⁻¹) (n / r - j + 1) := by
  rw [expPartial]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact factorial_moment_term_eq_expPartial_term r j i hr

theorem rCyclePMF_eq_formula {r : ℕ} (hr : 0 < r) :
    ∀ j n : ℕ, rCyclePMF n r j = rCyclePMFFormula n r j := by
  intro j n
  by_cases hjn : r * j ≤ n
  · have hjM : j ≤ n / r := by
      exact (Nat.le_div_iff_mul_le hr).2 (by simpa [Nat.mul_comm] using hjn)
    have hinv := finite_pmf_eq_factorial_moment_sum
      (α := Equiv.Perm (Fin n))
      (X := fun σ : Equiv.Perm (Fin n) => rCycleCount n r σ)
      (M := n / r) (j := j)
      (fun σ => rCycleCount_le_div (n := n) (r := r) hr σ)
    have hpmf_sum :
        rCyclePMF n r j =
          ∑ i ∈ Finset.range (n / r - j + 1),
            (((-1 : ℝ) ^ i) / (i.factorial * (j.factorial : ℝ))) *
              ((∑ σ : Equiv.Perm (Fin n),
                  ((rCycleCount n r σ).descFactorial (j + i) : ℝ)) /
                (n.factorial : ℝ)) := by
      unfold rCyclePMF rCycleFavourableCount
      simpa [Fintype.card_perm, Fintype.card_fin] using hinv
    have hmoment :
        ∀ i ∈ Finset.range (n / r - j + 1),
          ((∑ σ : Equiv.Perm (Fin n),
              ((rCycleCount n r σ).descFactorial (j + i) : ℝ)) /
            (n.factorial : ℝ)) =
              (r : ℝ) ^ (-(j + i : ℤ)) := by
      intro i hi
      have hi_le : i ≤ n / r - j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hik : j + i ≤ n / r := by omega
      have hmul' : (j + i) * r ≤ n := (Nat.le_div_iff_mul_le hr).1 hik
      have hmul : r * (j + i) ≤ n := by simpa [Nat.mul_comm] using hmul'
      simpa [FixedPointsPoissonNS.uniformPermExpectation] using
        factorialMoment_rCycle (n := n) (r := r) (k := j + i) hr hmul
    calc
      rCyclePMF n r j
          = ∑ i ∈ Finset.range (n / r - j + 1),
              (((-1 : ℝ) ^ i) / (i.factorial * (j.factorial : ℝ))) *
                ((∑ σ : Equiv.Perm (Fin n),
                    ((rCycleCount n r σ).descFactorial (j + i) : ℝ)) /
                  (n.factorial : ℝ)) := hpmf_sum
      _ = ∑ i ∈ Finset.range (n / r - j + 1),
              (((-1 : ℝ) ^ i) / (i.factorial * (j.factorial : ℝ))) *
                ((r : ℝ) ^ (-(j + i : ℤ))) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hmoment i hi]
      _ = (((r : ℝ) ^ j * (j.factorial : ℝ))⁻¹) *
            expPartial (-(r : ℝ)⁻¹) (n / r - j + 1) :=
            factorial_moment_sum_eq_formula_sum (n := n) (r := r) (j := j) hr
      _ = rCyclePMFFormula n r j := by
            simp [rCyclePMFFormula, Nat.ne_of_gt hr, hjn]
  · have hjgt : n / r < j := by
      have hnot : ¬ j * r ≤ n := by
        simpa [Nat.mul_comm] using hjn
      exact Nat.lt_of_not_ge (fun hjM => hnot ((Nat.le_div_iff_mul_le hr).1 hjM))
    have hempty :
        IsEmpty {σ : Equiv.Perm (Fin n) // rCycleCount n r σ = j} := by
      rw [isEmpty_subtype]
      intro σ hσ
      have hle := rCycleCount_le_div (n := n) (r := r) hr σ
      omega
    have hfav : rCycleFavourableCount n r j = 0 := by
      unfold rCycleFavourableCount
      haveI := hempty
      exact Fintype.card_eq_zero
    simp [rCyclePMF, rCyclePMFFormula, hfav, Nat.ne_of_gt hr, hjn]

theorem rCyclePMF_eventually_eq_formula {r : ℕ} (hr : 0 < r) :
    ∀ j : ℕ,
      (fun n : ℕ => rCyclePMF n r j) =ᶠ[atTop]
        fun n : ℕ => rCyclePMFFormula n r j := by
  intro j
  exact Filter.Eventually.of_forall fun n => rCyclePMF_eq_formula (r := r) hr j n

theorem rCycles_tendstoInDistribution_poisson {r : ℕ} (hr : 0 < r) :
    TendstoInDistribution
      (fun n (ω : Equiv.Perm (Fin n)) => rCycleCount n r ω)
      atTop
      (fun x : ℕ => x)
      uniformPermMeasure
      (ProbabilityTheory.poissonMeasure (poissonRate r)) :=
  rCycles_tendstoInDistribution_poisson_of_eventually_formula
    hr (rCyclePMF_eventually_eq_formula hr)

end Complete
end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
