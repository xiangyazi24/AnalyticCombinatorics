import Mathlib
import AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoisson
import AnalyticCombinatorics.Ch9.LimitLaws.RCyclesFactorialMoment
import AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonComplete
import AnalyticCombinatorics.Ch9.LimitLaws.JointCycleMoments
import AnalyticCombinatorics.Ch9.LimitLaws.JointCycleMomentsGeneral
import AnalyticCombinatorics.Ch9.LimitLaws.PMFToDistribution
import AnalyticCombinatorics.Ch9.LimitLaws.BivariateCyclePoisson

/-!
# Multivariate Poisson limits for finitely many cycle counts

This file contains the finite-product discrete bridge and the basic singleton
mass identities for vectors of cycle counts.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS
namespace Multivariate

/-- Joint law of finitely many fixed cycle counts under the uniform permutation measure. -/
def multivariateLaw {m : ℕ} (n : ℕ) (lengths : Fin m → ℕ) :
    ProbabilityMeasure (Fin m → ℕ) :=
  ⟨Measure.map
      (fun σ : Equiv.Perm (Fin n) => fun i : Fin m => rCycleCount n (lengths i) σ)
      (uniformPermMeasure n),
    Measure.isProbabilityMeasure_map (by
      exact (measurable_of_finite _).aemeasurable)⟩

/-- Product of the marginal Poisson probability measures. -/
def poissonPiMeasure {m : ℕ} (lengths : Fin m → ℕ) :
    ProbabilityMeasure (Fin m → ℕ) :=
  ProbabilityMeasure.pi
    (fun i : Fin m => poissonProbabilityMeasure (poissonRate (lengths i)))

/-- The genuine joint pmf of finitely many cycle counts. -/
def multivariatePMF {m : ℕ} (n : ℕ) (lengths : Fin m → ℕ) (v : Fin m → ℕ) : ℝ :=
  let p : Equiv.Perm (Fin n) → Prop := fun σ =>
    ∀ i : Fin m, rCycleCount n (lengths i) σ = v i
  let instDec : DecidablePred p := fun _ => Fintype.decidableForallFintype
  let instSub : Fintype {σ : Equiv.Perm (Fin n) // p σ} :=
    @Subtype.fintype (Equiv.Perm (Fin n)) p instDec _
  (@Fintype.card {σ : Equiv.Perm (Fin n) // p σ} instSub : ℝ) / n.factorial

/-- The limiting product Poisson pmf. -/
def poissonPiPMF {m : ℕ} (lengths : Fin m → ℕ) (v : Fin m → ℕ) : ℝ :=
  ∏ i : Fin m, ProbabilityTheory.poissonPMFReal (poissonRate (lengths i)) (v i)

/-- One factor in the finite inclusion-exclusion series for `P(C_r=i)`. -/
def oneDimTerm (r i a : ℕ) : ℝ := Bivariate.oneDimTerm r i a

/-- The finite triangular index set where the exact mixed factorial moment is nonzero. -/
def multivariateIndexFinset {m : ℕ} (n : ℕ) (lengths : Fin m → ℕ)
    (v : Fin m → ℕ) : Finset (Fin m → ℕ) :=
  (Fintype.piFinset
    (fun i : Fin m => Finset.range (n / lengths i - v i + 1))).filter
      (fun u : Fin m → ℕ => ∑ i : Fin m, lengths i * (v i + u i) ≤ n)

/-- The finite multivariate inclusion-exclusion expression. -/
def multivariatePMFFormula {m : ℕ} (n : ℕ) (lengths : Fin m → ℕ)
    (v : Fin m → ℕ) : ℝ :=
  ∑ u ∈ multivariateIndexFinset n lengths v,
    ∏ i : Fin m, oneDimTerm (lengths i) (v i) (u i)

lemma Multiset.sum_count_mul_le_sum (S : Finset ℕ) :
    ∀ m : Multiset ℕ, ∑ r ∈ S, m.count r * r ≤ m.sum := by
  classical
  intro m
  induction m using Multiset.induction_on with
  | empty =>
      simp
  | cons a m ih =>
      by_cases ha : a ∈ S
      · have hsum_cons_erase :
            (∑ r ∈ S.erase a, (a ::ₘ m).count r * r) =
              ∑ r ∈ S.erase a, m.count r * r := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          have hra : r ≠ a := (Finset.mem_erase.mp hr).1
          rw [Multiset.count_cons_of_ne hra]
        have hsum_m :
            (∑ r ∈ S.erase a, m.count r * r) + m.count a * a =
              ∑ r ∈ S, m.count r * r := by
          exact Finset.sum_erase_add S (fun r => m.count r * r) ha
        calc
          (∑ r ∈ S, (a ::ₘ m).count r * r)
              = (∑ r ∈ S.erase a, (a ::ₘ m).count r * r) +
                  (a ::ₘ m).count a * a := by
                    exact (Finset.sum_erase_add S
                      (fun r => (a ::ₘ m).count r * r) ha).symm
          _ = (∑ r ∈ S.erase a, m.count r * r) + (m.count a + 1) * a := by
                    rw [hsum_cons_erase, Multiset.count_cons_self]
          _ = (∑ r ∈ S.erase a, m.count r * r) + (m.count a * a + a) := by
                    rw [Nat.add_mul]
                    simp
          _ = ((∑ r ∈ S.erase a, m.count r * r) + m.count a * a) + a := by
                    rw [Nat.add_assoc]
          _ = (∑ r ∈ S, m.count r * r) + a := by
                    rw [hsum_m]
          _ ≤ m.sum + a := Nat.add_le_add_right ih a
          _ = (a ::ₘ m).sum := by
                    simp [Nat.add_comm]
      · have hsum_cons :
            (∑ r ∈ S, (a ::ₘ m).count r * r) =
              ∑ r ∈ S, m.count r * r := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          have hra : r ≠ a := by
            intro h
            exact ha (by simpa [h] using hr)
          rw [Multiset.count_cons_of_ne hra]
        calc
          (∑ r ∈ S, (a ::ₘ m).count r * r)
              = ∑ r ∈ S, m.count r * r := hsum_cons
          _ ≤ m.sum := ih
          _ ≤ (a ::ₘ m).sum := by
                simp

lemma rCycleCount_finset_weight_le_card {n : ℕ} (S : Finset ℕ)
    (σ : Equiv.Perm (Fin n)) :
    ∑ r ∈ S, r * rCycleCount n r σ ≤ n := by
  classical
  have hcycle_le : σ.cycleType.sum ≤ n := by
    simpa [Fintype.card_fin] using Equiv.Perm.sum_cycleType_le σ
  by_cases h1 : 1 ∈ S
  · let T : Finset ℕ := S.erase 1
    have hcountT :
        ∑ r ∈ T, r * rCycleCount n r σ ≤ σ.cycleType.sum := by
      calc
        (∑ r ∈ T, r * rCycleCount n r σ)
            = ∑ r ∈ T, σ.cycleType.count r * r := by
                refine Finset.sum_congr rfl ?_
                intro r hr
                have hrne : r ≠ 1 := (Finset.mem_erase.mp hr).1
                rw [rCycleCount_eq_cycleType_count_of_ne_one hrne σ]
                rw [Nat.mul_comm]
        _ ≤ σ.cycleType.sum := Multiset.sum_count_mul_le_sum T σ.cycleType
    have hfixed := Bivariate.rCycleCount_one_eq_card_sub_cycleType_sum n σ
    calc
      (∑ r ∈ S, r * rCycleCount n r σ)
          = (∑ r ∈ T, r * rCycleCount n r σ) + rCycleCount n 1 σ := by
              dsimp [T]
              rw [← Finset.sum_erase_add S (fun r => r * rCycleCount n r σ) h1]
              simp
      _ = (∑ r ∈ T, r * rCycleCount n r σ) + (n - σ.cycleType.sum) := by
              rw [hfixed]
      _ ≤ σ.cycleType.sum + (n - σ.cycleType.sum) := by
              exact Nat.add_le_add_right hcountT _
      _ = n := Nat.add_sub_of_le hcycle_le
  · calc
      (∑ r ∈ S, r * rCycleCount n r σ)
          = ∑ r ∈ S, σ.cycleType.count r * r := by
              refine Finset.sum_congr rfl ?_
              intro r hr
              have hrne : r ≠ 1 := by
                intro h
                exact h1 (by simpa [h] using hr)
              rw [rCycleCount_eq_cycleType_count_of_ne_one hrne σ]
              rw [Nat.mul_comm]
      _ ≤ σ.cycleType.sum := Multiset.sum_count_mul_le_sum S σ.cycleType
      _ ≤ n := hcycle_le

lemma multivariate_rCycleCount_weight_le_card {m n : ℕ} (lengths : Fin m → ℕ)
    (hinj : Function.Injective lengths) (σ : Equiv.Perm (Fin n)) :
    ∑ i : Fin m, lengths i * rCycleCount n (lengths i) σ ≤ n := by
  classical
  let S : Finset ℕ := Finset.image lengths Finset.univ
  have hinjOn : Set.InjOn lengths (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)) := by
    intro i _hi j _hj hij
    exact hinj hij
  have hsumS :
      (∑ r ∈ S, r * rCycleCount n r σ) =
        ∑ i : Fin m, lengths i * rCycleCount n (lengths i) σ := by
    dsimp [S]
    rw [Finset.sum_image hinjOn]
  simpa [hsumS] using rCycleCount_finset_weight_le_card (n := n) S σ

lemma multivariate_factorial_moment_eval {m n : ℕ} (lengths : Fin m → ℕ)
    (hpos : ∀ i : Fin m, 0 < lengths i) (hinj : Function.Injective lengths)
    (a : Fin m → ℕ) (hweight : ∑ i : Fin m, lengths i * a i ≤ n) :
    (∑ σ : Equiv.Perm (Fin n),
        ∏ i : Fin m, ((rCycleCount n (lengths i) σ).descFactorial (a i) : ℝ)) /
      (n.factorial : ℝ) =
      ∏ i : Fin m, (lengths i : ℝ) ^ (-(a i : ℤ)) := by
  classical
  let S : Finset ℕ := Finset.image lengths Finset.univ
  let k : ℕ → ℕ := fun r =>
    if h : ∃ i : Fin m, lengths i = r then a (Classical.choose h) else 0
  have hk : ∀ i : Fin m, k (lengths i) = a i := by
    intro i
    have h : ∃ j : Fin m, lengths j = lengths i := ⟨i, rfl⟩
    have hchoose : lengths (Classical.choose h) = lengths i := Classical.choose_spec h
    have hidx : Classical.choose h = i := hinj hchoose
    simp [k, h, hidx]
  have hinjOn : Set.InjOn lengths (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)) := by
    intro i _hi j _hj hij
    exact hinj hij
  have hposS : ∀ r ∈ S, 0 < r := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨i, _hi, rfl⟩
    exact hpos i
  have hsumS : (∑ r ∈ S, r * k r) = ∑ i : Fin m, lengths i * a i := by
    dsimp [S]
    rw [Finset.sum_image hinjOn]
    simp [hk]
  have hweightS : ∑ r ∈ S, r * k r ≤ n := by
    simpa [hsumS] using hweight
  have hprod_desc :
      ∀ σ : Equiv.Perm (Fin n),
        (∏ r ∈ S, ((rCycleCount n r σ).descFactorial (k r) : ℝ)) =
          ∏ i : Fin m,
            ((rCycleCount n (lengths i) σ).descFactorial (a i) : ℝ) := by
    intro σ
    dsimp [S]
    rw [Finset.prod_image hinjOn]
    simp [hk]
  have hprod_pow :
      (∏ r ∈ S, (r : ℝ) ^ (-(k r : ℤ))) =
        ∏ i : Fin m, (lengths i : ℝ) ^ (-(a i : ℤ)) := by
    dsimp [S]
    rw [Finset.prod_image hinjOn]
    simp [hk]
  have hfm :=
    JointCycleMomentsGeneralNS.factorialMoment_rCycle_finset
      (n := n) (S := S) (k := k) hposS hweightS
  unfold FixedPointsPoissonNS.uniformPermExpectation at hfm
  calc
    (∑ σ : Equiv.Perm (Fin n),
        ∏ i : Fin m, ((rCycleCount n (lengths i) σ).descFactorial (a i) : ℝ)) /
      (n.factorial : ℝ)
        =
      (∑ σ : Equiv.Perm (Fin n),
        ∏ r ∈ S, ((rCycleCount n r σ).descFactorial (k r) : ℝ)) /
      (n.factorial : ℝ) := by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro σ _hσ
        exact (hprod_desc σ).symm
    _ = ∏ r ∈ S, (r : ℝ) ^ (-(k r : ℤ)) := hfm
    _ = ∏ i : Fin m, (lengths i : ℝ) ^ (-(a i : ℤ)) := hprod_pow

lemma multivariate_factorial_moment_zero_of_lt {m n : ℕ} (lengths : Fin m → ℕ)
    (hinj : Function.Injective lengths) (a : Fin m → ℕ)
    (h : n < ∑ i : Fin m, lengths i * a i) :
    (∑ σ : Equiv.Perm (Fin n),
        ∏ i : Fin m, ((rCycleCount n (lengths i) σ).descFactorial (a i) : ℝ)) /
      (n.factorial : ℝ) = 0 := by
  classical
  suffices
      (∑ σ : Equiv.Perm (Fin n),
        ∏ i : Fin m, ((rCycleCount n (lengths i) σ).descFactorial (a i) : ℝ)) = 0 by
    rw [this]
    simp
  refine Finset.sum_eq_zero ?_
  intro σ _hσ
  by_cases hall : ∀ i : Fin m, a i ≤ rCycleCount n (lengths i) σ
  · have huse :
        (∑ i : Fin m, lengths i * a i) ≤
          ∑ i : Fin m, lengths i * rCycleCount n (lengths i) σ := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      exact Nat.mul_le_mul_left (lengths i) (hall i)
    have hcard := multivariate_rCycleCount_weight_le_card (n := n) lengths hinj σ
    omega
  · have hex : ∃ i : Fin m, ¬ a i ≤ rCycleCount n (lengths i) σ := by
      simpa [not_forall] using hall
    rcases hex with ⟨i, hi⟩
    have hzeroNat :
        (rCycleCount n (lengths i) σ).descFactorial (a i) = 0 :=
      (Nat.descFactorial_eq_zero_iff_lt).2 (Nat.lt_of_not_ge hi)
    have hzeroReal :
        ((rCycleCount n (lengths i) σ).descFactorial (a i) : ℝ) = 0 := by
      exact_mod_cast hzeroNat
    exact Finset.prod_eq_zero (Finset.mem_univ i) hzeroReal

lemma multivariate_factorial_moment_eval_if {m n : ℕ} (lengths : Fin m → ℕ)
    (hpos : ∀ i : Fin m, 0 < lengths i) (hinj : Function.Injective lengths)
    (a : Fin m → ℕ) :
    (∑ σ : Equiv.Perm (Fin n),
        ∏ i : Fin m, ((rCycleCount n (lengths i) σ).descFactorial (a i) : ℝ)) /
      (n.factorial : ℝ) =
      if ∑ i : Fin m, lengths i * a i ≤ n then
        ∏ i : Fin m, (lengths i : ℝ) ^ (-(a i : ℤ))
      else 0 := by
  by_cases hle : ∑ i : Fin m, lengths i * a i ≤ n
  · simp [hle, multivariate_factorial_moment_eval
      (n := n) lengths hpos hinj a hle]
  · have hlt : n < ∑ i : Fin m, lengths i * a i := Nat.lt_of_not_ge hle
    simp [hle, multivariate_factorial_moment_zero_of_lt
      (n := n) lengths hinj a hlt]

lemma card_subtype_eq_sum_pi_indicator {ι α : Type*} [Fintype ι] [Fintype α]
    (X : ι → α → ℕ) (j : ι → ℕ) :
    (Fintype.card {a : α // ∀ i : ι, X i a = j i} : ℝ) =
      ∑ a : α, if (∀ i : ι, X i a = j i) then (1 : ℝ) else 0 := by
  classical
  rw [Fintype.card_subtype]
  rw [Finset.sum_boole]

lemma pi_indicator_eq_kernel_sum {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → α → ℕ) {M j : ι → ℕ} (hX : ∀ a : α, ∀ i : ι, X i a ≤ M i)
    (a : α) :
    (if (∀ i : ι, X i a = j i) then (1 : ℝ) else 0) =
      ∑ u ∈ Fintype.piFinset (fun i : ι => Finset.range (M i - j i + 1)),
        ∏ i : ι,
          ((-1 : ℝ) ^ (u i)) *
            (((X i a).descFactorial (j i + u i) : ℝ) /
              ((u i).factorial * ((j i).factorial : ℝ))) := by
  classical
  let U : ι → Finset ℕ := fun i => Finset.range (M i - j i + 1)
  let K : ι → ℕ → ℝ := fun i u =>
    ((-1 : ℝ) ^ u) *
      (((X i a).descFactorial (j i + u) : ℝ) /
        (u.factorial * ((j i).factorial : ℝ)))
  have hcoord :
      ∀ i : ι, (∑ u ∈ U i, K i u) = if X i a = j i then (1 : ℝ) else 0 := by
    intro i
    simpa [U, K] using
      Complete.factorial_kernel_sum_eq_indicator
        (M := M i) (x := X i a) (j := j i) (hX a i)
  calc
    (if (∀ i : ι, X i a = j i) then (1 : ℝ) else 0)
        = ∏ i : ι, (if X i a = j i then (1 : ℝ) else 0) := by
          by_cases h : ∀ i : ι, X i a = j i
          · simp [h]
          · have hex : ∃ i : ι, X i a ≠ j i := by
              simpa [not_forall] using h
            rcases hex with ⟨i, hi⟩
            simp [h]
            exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm
    _ = ∏ i : ι, ∑ u ∈ U i, K i u := by
          refine Finset.prod_congr rfl ?_
          intro i _hi
          exact (hcoord i).symm
    _ = ∑ u ∈ Fintype.piFinset U, ∏ i : ι, K i (u i) := by
          exact Finset.prod_univ_sum U K
    _ = ∑ u ∈ Fintype.piFinset (fun i : ι => Finset.range (M i - j i + 1)),
        ∏ i : ι,
          ((-1 : ℝ) ^ (u i)) *
            (((X i a).descFactorial (j i + u i) : ℝ) /
              ((u i).factorial * ((j i).factorial : ℝ))) := by
          rfl

/-- Finite multivariate pmf inversion in terms of mixed factorial moments. -/
lemma finite_pi_pmf_eq_factorial_moment_sum {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] (X : ι → α → ℕ) {M j : ι → ℕ}
    (hX : ∀ a : α, ∀ i : ι, X i a ≤ M i) :
    (Fintype.card {a : α // ∀ i : ι, X i a = j i} : ℝ) /
        (Fintype.card α : ℝ) =
      ∑ u ∈ Fintype.piFinset (fun i : ι => Finset.range (M i - j i + 1)),
        (∏ i : ι, ((-1 : ℝ) ^ (u i)) /
          ((u i).factorial * ((j i).factorial : ℝ))) *
          ((∑ a : α,
            ∏ i : ι, ((X i a).descFactorial (j i + u i) : ℝ)) /
            (Fintype.card α : ℝ)) := by
  classical
  let U : ι → Finset ℕ := fun i => Finset.range (M i - j i + 1)
  let K : α → (ι → ℕ) → ℝ := fun a u =>
    ∏ i : ι,
      ((-1 : ℝ) ^ (u i)) *
        (((X i a).descFactorial (j i + u i) : ℝ) /
          ((u i).factorial * ((j i).factorial : ℝ)))
  let C : (ι → ℕ) → ℝ := fun u =>
    ∏ i : ι, ((-1 : ℝ) ^ (u i)) /
      ((u i).factorial * ((j i).factorial : ℝ))
  let D : α → (ι → ℕ) → ℝ := fun a u =>
    ∏ i : ι, ((X i a).descFactorial (j i + u i) : ℝ)
  have hpoint :
      ∀ a : α,
        (if (∀ i : ι, X i a = j i) then (1 : ℝ) else 0) =
          ∑ u ∈ Fintype.piFinset U, K a u := by
    intro a
    simpa [U, K] using pi_indicator_eq_kernel_sum (X := X) (M := M) (j := j) hX a
  have hK : ∀ a : α, ∀ u : ι → ℕ, K a u = C u * D a u := by
    intro a u
    simp [K, C, D, Finset.prod_mul_distrib]
    ring
  calc
    (Fintype.card {a : α // ∀ i : ι, X i a = j i} : ℝ) /
        (Fintype.card α : ℝ)
        =
      (∑ a : α, if (∀ i : ι, X i a = j i) then (1 : ℝ) else 0) /
        (Fintype.card α : ℝ) := by
          rw [card_subtype_eq_sum_pi_indicator X j]
    _ = (∑ a : α, ∑ u ∈ Fintype.piFinset U, K a u) /
        (Fintype.card α : ℝ) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro a _ha
          exact hpoint a
    _ = (∑ u ∈ Fintype.piFinset U, ∑ a : α, K a u) /
        (Fintype.card α : ℝ) := by
          congr 1
          exact Finset.sum_comm
    _ = ∑ u ∈ Fintype.piFinset U,
        (∑ a : α, K a u) / (Fintype.card α : ℝ) := by
          rw [Finset.sum_div]
    _ = ∑ u ∈ Fintype.piFinset U,
        C u * ((∑ a : α, D a u) / (Fintype.card α : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro u _hu
          calc
            (∑ a : α, K a u) / (Fintype.card α : ℝ)
                = (C u * ∑ a : α, D a u) / (Fintype.card α : ℝ) := by
                    congr 1
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl ?_
                    intro a _ha
                    exact hK a u
            _ = C u * ((∑ a : α, D a u) / (Fintype.card α : ℝ)) := by
                    ring
    _ = ∑ u ∈ Fintype.piFinset (fun i : ι => Finset.range (M i - j i + 1)),
        (∏ i : ι, ((-1 : ℝ) ^ (u i)) /
          ((u i).factorial * ((j i).factorial : ℝ))) *
          ((∑ a : α,
            ∏ i : ι, ((X i a).descFactorial (j i + u i) : ℝ)) /
            (Fintype.card α : ℝ)) := by
          rfl

lemma multivariate_formula_term_eq {m : ℕ} (lengths : Fin m → ℕ)
    (v u : Fin m → ℕ) :
    ((∏ i : Fin m, ((-1 : ℝ) ^ (u i))) /
      (∏ i : Fin m, ((u i).factorial * ((v i).factorial : ℝ)))) *
      (∏ i : Fin m, (lengths i : ℝ) ^ (-(u i : ℤ) + -(v i : ℤ))) =
      ∏ i : Fin m, oneDimTerm (lengths i) (v i) (u i) := by
  rw [← Finset.prod_div_distrib]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro i _hi
  simp [oneDimTerm, Bivariate.oneDimTerm]

theorem multivariatePMF_eq_formula {m : ℕ} (lengths : Fin m → ℕ)
    (hpos : ∀ i : Fin m, 0 < lengths i) (hinj : Function.Injective lengths) :
    ∀ n : ℕ, ∀ v : Fin m → ℕ,
      multivariatePMF n lengths v = multivariatePMFFormula n lengths v := by
  classical
  intro n v
  have hinv := finite_pi_pmf_eq_factorial_moment_sum
    (ι := Fin m) (α := Equiv.Perm (Fin n))
    (X := fun i σ => rCycleCount n (lengths i) σ)
    (M := fun i => n / lengths i) (j := v)
    (fun σ i => Complete.rCycleCount_le_div (n := n) (r := lengths i) (hpos i) σ)
  have hpmf :
      multivariatePMF n lengths v =
        ∑ u ∈ Fintype.piFinset
          (fun i : Fin m => Finset.range (n / lengths i - v i + 1)),
          ((∏ i : Fin m, ((-1 : ℝ) ^ (u i))) /
            (∏ i : Fin m, ((u i).factorial * ((v i).factorial : ℝ)))) *
            ((∑ σ : Equiv.Perm (Fin n),
              ∏ i : Fin m,
                ((rCycleCount n (lengths i) σ).descFactorial (v i + u i) : ℝ)) /
              (n.factorial : ℝ)) := by
    unfold multivariatePMF
    simpa [Fintype.card_perm, Fintype.card_fin] using hinv
  rw [hpmf]
  unfold multivariatePMFFormula multivariateIndexFinset
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro u hu
  by_cases hle : ∑ i : Fin m, lengths i * (v i + u i) ≤ n
  · rw [multivariate_factorial_moment_eval_if
      (n := n) lengths hpos hinj (fun i : Fin m => v i + u i)]
    simp [hle]
    exact multivariate_formula_term_eq lengths v u
  · rw [multivariate_factorial_moment_eval_if
      (n := n) lengths hpos hinj (fun i : Fin m => v i + u i)]
    simp [hle]

lemma mem_multivariateIndexFinset_of_weight_le {m n : ℕ} {lengths v u : Fin m → ℕ}
    (hpos : ∀ i : Fin m, 0 < lengths i)
    (hweight : ∑ i : Fin m, lengths i * (v i + u i) ≤ n) :
    u ∈ multivariateIndexFinset n lengths v := by
  classical
  unfold multivariateIndexFinset
  refine Finset.mem_filter.2 ⟨?_, hweight⟩
  rw [Fintype.mem_piFinset]
  intro i
  have hpart : lengths i * (v i + u i) ≤ n := by
    exact (Finset.single_le_sum (fun j _hj => Nat.zero_le _)
      (Finset.mem_univ i)).trans hweight
  have hle : v i + u i ≤ n / lengths i :=
    (Nat.le_div_iff_mul_le (hpos i)).2 (by simpa [Nat.mul_comm] using hpart)
  exact Finset.mem_range.2
    (Nat.lt_succ_of_le (Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hle)))

lemma multivariateIndexFinset_tendsto_atTop {m : ℕ} (lengths : Fin m → ℕ)
    (hpos : ∀ i : Fin m, 0 < lengths i) (v : Fin m → ℕ) :
    Tendsto (fun n : ℕ => multivariateIndexFinset n lengths v) atTop atTop := by
  classical
  refine Filter.tendsto_atTop_finset_of_monotone ?_ ?_
  · intro n n' hnn' u hu
    exact mem_multivariateIndexFinset_of_weight_le (n := n') (lengths := lengths)
      (v := v) hpos ((Finset.mem_filter.mp hu).2.trans hnn')
  · intro u
    exact ⟨∑ i : Fin m, lengths i * (v i + u i),
      mem_multivariateIndexFinset_of_weight_le (lengths := lengths) (v := v) hpos le_rfl⟩

lemma summable_norm_pi_oneDimTerm :
    ∀ {m : ℕ} (lengths : Fin m → ℕ), (∀ i : Fin m, 0 < lengths i) →
      (v : Fin m → ℕ) →
      Summable fun u : Fin m → ℕ =>
        ‖∏ i : Fin m, oneDimTerm (lengths i) (v i) (u i)‖ := by
  intro m
  induction m with
  | zero =>
      intro lengths hpos v
      exact (hasSum_fintype
        (fun u : Fin 0 → ℕ =>
          ‖∏ i : Fin 0, oneDimTerm (lengths i) (v i) (u i)‖)).summable
  | succ m ih =>
      intro lengths hpos v
      let tailLengths : Fin m → ℕ := fun i => lengths i.succ
      let tailV : Fin m → ℕ := fun i => v i.succ
      have h0 :
          Summable fun a : ℕ => ‖oneDimTerm (lengths 0) (v 0) a‖ := by
        simpa [oneDimTerm] using
          (Bivariate.oneDimTerm_hasSum (r := lengths 0) (hpos 0) (v 0)).summable.abs
      have htail :
          Summable fun u : Fin m → ℕ =>
            ‖∏ i : Fin m, oneDimTerm (tailLengths i) (tailV i) (u i)‖ :=
        ih tailLengths (fun i => hpos i.succ) tailV
      have hprod :
          Summable fun p : ℕ × (Fin m → ℕ) =>
            ‖oneDimTerm (lengths 0) (v 0) p.1‖ *
              ‖∏ i : Fin m, oneDimTerm (tailLengths i) (tailV i) (p.2 i)‖ :=
        h0.mul_of_nonneg htail (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      have hprod_norm :
          Summable fun p : ℕ × (Fin m → ℕ) =>
            ‖oneDimTerm (lengths 0) (v 0) p.1 *
              (∏ i : Fin m, oneDimTerm (tailLengths i) (tailV i) (p.2 i))‖ := by
        simpa [norm_mul] using hprod
      let e : ℕ × (Fin m → ℕ) ≃ (Fin (m + 1) → ℕ) :=
        Fin.consEquiv (fun _ : Fin (m + 1) => ℕ)
      have hcomp :
          Summable fun p : ℕ × (Fin m → ℕ) =>
            ‖∏ i : Fin (m + 1), oneDimTerm (lengths i) (v i) ((e p) i)‖ := by
        convert hprod_norm using 1
        ext p
        rw [Fin.prod_univ_succ]
        simp [e, tailLengths, tailV, Fin.consEquiv_apply]
      exact (e.summable_iff).1 hcomp

-- The finite-product `HasSum` induction combines a dependent tail series with
-- `HasSum.mul`; the local heartbeat bump prevents a deterministic timeout in
-- the summability witness elaboration.
set_option maxHeartbeats 800000 in
lemma hasSum_pi_oneDimTerm :
    ∀ {m : ℕ} (lengths : Fin m → ℕ), (∀ i : Fin m, 0 < lengths i) →
      (v : Fin m → ℕ) →
      HasSum
        (fun u : Fin m → ℕ =>
          ∏ i : Fin m, oneDimTerm (lengths i) (v i) (u i))
        (poissonPiPMF lengths v) := by
  intro m
  induction m with
  | zero =>
      intro lengths hpos v
      simp [poissonPiPMF]
  | succ m ih =>
      intro lengths hpos v
      let tailLengths : Fin m → ℕ := fun i => lengths i.succ
      let tailV : Fin m → ℕ := fun i => v i.succ
      have h0 :
          HasSum (fun a : ℕ => oneDimTerm (lengths 0) (v 0) a)
            (ProbabilityTheory.poissonPMFReal (poissonRate (lengths 0)) (v 0)) := by
        simpa [oneDimTerm] using
          Bivariate.oneDimTerm_hasSum (r := lengths 0) (hpos 0) (v 0)
      have htail :
          HasSum
            (fun u : Fin m → ℕ =>
              ∏ i : Fin m, oneDimTerm (tailLengths i) (tailV i) (u i))
            (poissonPiPMF tailLengths tailV) :=
        ih tailLengths (fun i => hpos i.succ) tailV
      have htail_abs :
          Summable fun u : Fin m → ℕ =>
            ‖∏ i : Fin m, oneDimTerm (tailLengths i) (tailV i) (u i)‖ :=
        summable_norm_pi_oneDimTerm tailLengths (fun i => hpos i.succ) tailV
      have hprod_abs :
          Summable fun p : ℕ × (Fin m → ℕ) =>
            ‖oneDimTerm (lengths 0) (v 0) p.1‖ *
              ‖∏ i : Fin m, oneDimTerm (tailLengths i) (tailV i) (p.2 i)‖ :=
        h0.summable.abs.mul_of_nonneg htail_abs
          (fun _ => abs_nonneg _) (fun _ => norm_nonneg _)
      have hprod_summable :
          Summable fun p : ℕ × (Fin m → ℕ) =>
            oneDimTerm (lengths 0) (v 0) p.1 *
              (∏ i : Fin m, oneDimTerm (tailLengths i) (tailV i) (p.2 i)) := by
        refine Summable.of_norm ?_
        simpa [norm_mul] using hprod_abs
      have hprod_hasSum :
          HasSum
            (fun p : ℕ × (Fin m → ℕ) =>
              oneDimTerm (lengths 0) (v 0) p.1 *
                (∏ i : Fin m, oneDimTerm (tailLengths i) (tailV i) (p.2 i)))
            (ProbabilityTheory.poissonPMFReal (poissonRate (lengths 0)) (v 0) *
              poissonPiPMF tailLengths tailV) :=
        h0.mul htail hprod_summable
      let e : ℕ × (Fin m → ℕ) ≃ (Fin (m + 1) → ℕ) :=
        Fin.consEquiv (fun _ : Fin (m + 1) => ℕ)
      have hcomp :
          HasSum
            (fun p : ℕ × (Fin m → ℕ) =>
              ∏ i : Fin (m + 1), oneDimTerm (lengths i) (v i) ((e p) i))
            (poissonPiPMF lengths v) := by
        convert hprod_hasSum using 1
        · ext p
          rw [Fin.prod_univ_succ]
          simp [e, tailLengths, tailV, Fin.consEquiv_apply]
        · simp [poissonPiPMF, tailLengths, tailV, Fin.prod_univ_succ]
      exact (e.hasSum_iff).1 hcomp

theorem multivariatePMFFormula_tendsto_poissonPiPMF {m : ℕ} (lengths : Fin m → ℕ)
    (hpos : ∀ i : Fin m, 0 < lengths i) (v : Fin m → ℕ) :
    Tendsto (fun n : ℕ => multivariatePMFFormula n lengths v) atTop
      (𝓝 (poissonPiPMF lengths v)) := by
  have hsum := hasSum_pi_oneDimTerm lengths hpos v
  change Tendsto
    (fun n : ℕ => ∑ u ∈ multivariateIndexFinset n lengths v,
      ∏ i : Fin m, oneDimTerm (lengths i) (v i) (u i))
    atTop (𝓝 (poissonPiPMF lengths v))
  change Tendsto
    (fun t : Finset (Fin m → ℕ) => ∑ u ∈ t,
      ∏ i : Fin m, oneDimTerm (lengths i) (v i) (u i))
    atTop (𝓝 (poissonPiPMF lengths v)) at hsum
  exact hsum.comp (multivariateIndexFinset_tendsto_atTop lengths hpos v)

theorem multivariatePMF_tendsto_poissonPiPMF {m : ℕ} (lengths : Fin m → ℕ)
    (hpos : ∀ i : Fin m, 0 < lengths i) (hinj : Function.Injective lengths)
    (v : Fin m → ℕ) :
    Tendsto (fun n : ℕ => multivariatePMF n lengths v) atTop
      (𝓝 (poissonPiPMF lengths v)) := by
  exact Tendsto.congr' (Eventually.of_forall fun n =>
    (multivariatePMF_eq_formula lengths hpos hinj n v).symm)
    (multivariatePMFFormula_tendsto_poissonPiPMF lengths hpos v)

/-- On `Fin m → ℕ`, pointwise singleton convergence implies weak convergence. -/
theorem probabilityMeasure_pi_nat_tendsto_of_tendsto_singleton {m : ℕ}
    {μs : ℕ → ProbabilityMeasure (Fin m → ℕ)} {μ : ProbabilityMeasure (Fin m → ℕ)}
    (h : ∀ v : Fin m → ℕ,
      Tendsto (fun n : ℕ => (μs n : Measure (Fin m → ℕ)) ({v} : Set (Fin m → ℕ)))
        atTop
        (𝓝 ((μ : Measure (Fin m → ℕ)) ({v} : Set (Fin m → ℕ))))) :
    Tendsto μs atTop (𝓝 μ) := by
  classical
  refine MeasureTheory.tendsto_of_forall_isOpen_le_liminf_nat' ?_
  intro G _hG
  have hfinite_le :
      ∀ t : Finset (Fin m → ℕ), (∀ v ∈ t, v ∈ G) →
        (∑ v ∈ t, (μ : Measure (Fin m → ℕ)) ({v} : Set (Fin m → ℕ))) ≤
          atTop.liminf (fun n : ℕ => (μs n : Measure (Fin m → ℕ)) G) := by
    intro t htG
    have hsum_tendsto :
        Tendsto
          (fun n : ℕ => ∑ v ∈ t,
            (μs n : Measure (Fin m → ℕ)) ({v} : Set (Fin m → ℕ)))
          atTop
          (𝓝 (∑ v ∈ t, (μ : Measure (Fin m → ℕ)) ({v} : Set (Fin m → ℕ)))) :=
      tendsto_finset_sum t (fun v _hv => h v)
    rw [← hsum_tendsto.liminf_eq]
    refine Filter.liminf_le_liminf (Eventually.of_forall ?_)
      (by isBoundedDefault)
      (by isBoundedDefault)
    intro n
    have hdisj : (t : Set (Fin m → ℕ)).PairwiseDisjoint
        (fun v => ({v} : Set (Fin m → ℕ))) := by
      intro a _ha b _hb hne
      change Disjoint ({a} : Set (Fin m → ℕ)) ({b} : Set (Fin m → ℕ))
      rw [Set.disjoint_singleton_left]
      simpa using hne
    calc
      (∑ v ∈ t, (μs n : Measure (Fin m → ℕ)) ({v} : Set (Fin m → ℕ)))
          = (μs n : Measure (Fin m → ℕ))
              (⋃ v ∈ t, ({v} : Set (Fin m → ℕ))) := by
              exact (MeasureTheory.measure_biUnion_finset hdisj
                (fun v _hv => measurableSet_singleton v)).symm
      _ ≤ (μs n : Measure (Fin m → ℕ)) G := by
              refine measure_mono ?_
              intro x hx
              simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hx
              rcases hx with ⟨v, hv, hxv⟩
              subst hxv
              exact htG x hv
  have hμG :
      (μ : Measure (Fin m → ℕ)) G =
        ∑' v : Fin m → ℕ, G.indicator
          (fun v => (μ : Measure (Fin m → ℕ)) ({v} : Set (Fin m → ℕ))) v := by
    exact (Measure.tsum_indicator_apply_singleton (μ : Measure (Fin m → ℕ)) G
      G.to_countable.measurableSet).symm
  rw [hμG, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le ?_
  intro t
  calc
    (∑ v ∈ t, G.indicator
        (fun v => (μ : Measure (Fin m → ℕ)) ({v} : Set (Fin m → ℕ))) v)
        = ∑ v ∈ t.filter (fun v => v ∈ G),
            (μ : Measure (Fin m → ℕ)) ({v} : Set (Fin m → ℕ)) := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl ?_
            intro v _hv
            by_cases hvG : v ∈ G
            · simp [hvG]
            · simp [hvG]
    _ ≤ atTop.liminf (fun n : ℕ => (μs n : Measure (Fin m → ℕ)) G) :=
            hfinite_le (t.filter (fun v => v ∈ G))
              (fun v hv => (Finset.mem_filter.mp hv).2)

/-- A real-valued pmf version of the finite-product discrete bridge. -/
theorem probabilityMeasure_pi_nat_tendsto_of_tendsto_pmfReal {m : ℕ}
    {p : ℕ → (Fin m → ℕ) → ℝ} {q : (Fin m → ℕ) → ℝ}
    {μs : ℕ → ProbabilityMeasure (Fin m → ℕ)} {μ : ProbabilityMeasure (Fin m → ℕ)}
    (hp : ∀ n v, (μs n : Measure (Fin m → ℕ)) ({v} : Set (Fin m → ℕ)) =
      ENNReal.ofReal (p n v))
    (hq : ∀ v, (μ : Measure (Fin m → ℕ)) ({v} : Set (Fin m → ℕ)) =
      ENNReal.ofReal (q v))
    (hconv : ∀ v : Fin m → ℕ, Tendsto (fun n : ℕ => p n v) atTop (𝓝 (q v))) :
    Tendsto μs atTop (𝓝 μ) :=
  probabilityMeasure_pi_nat_tendsto_of_tendsto_singleton fun v => by
    simpa [hp, hq] using ENNReal.tendsto_ofReal (hconv v)

lemma multivariate_law_singleton {m : ℕ} (n : ℕ) (lengths : Fin m → ℕ)
    (v : Fin m → ℕ) :
    (multivariateLaw n lengths : Measure (Fin m → ℕ)) ({v} : Set (Fin m → ℕ)) =
      ENNReal.ofReal (multivariatePMF n lengths v) := by
  classical
  have hpre :
      (fun σ : Equiv.Perm (Fin n) => fun i : Fin m => rCycleCount n (lengths i) σ) ⁻¹'
          ({v} : Set (Fin m → ℕ)) =
        {σ : Equiv.Perm (Fin n) |
          ∀ i : Fin m, rCycleCount n (lengths i) σ = v i} := by
    ext σ
    simp [funext_iff]
  change
    (Measure.map
      (fun σ : Equiv.Perm (Fin n) => fun i : Fin m => rCycleCount n (lengths i) σ)
      (uniformPermMeasure n)) ({v} : Set (Fin m → ℕ)) =
        ENNReal.ofReal (multivariatePMF n lengths v)
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton v), hpre]
  unfold uniformPermMeasure
  rw [PMF.toMeasure_uniformOfFintype_apply]
  · rw [Fintype.card_perm, Fintype.card_fin]
    change
      (Fintype.card {σ : Equiv.Perm (Fin n) //
        ∀ i : Fin m, rCycleCount n (lengths i) σ = v i} : ℝ≥0∞) /
          (n.factorial : ℝ≥0∞) =
        ENNReal.ofReal (multivariatePMF n lengths v)
    have hcard :
        Fintype.card {σ : Equiv.Perm (Fin n) //
          ∀ i : Fin m, rCycleCount n (lengths i) σ = v i} =
          @Fintype.card {σ : Equiv.Perm (Fin n) //
            (fun σ => ∀ i : Fin m, rCycleCount n (lengths i) σ = v i) σ}
            (@Subtype.fintype (Equiv.Perm (Fin n))
              (fun σ => ∀ i : Fin m, rCycleCount n (lengths i) σ = v i)
              (fun _ => Fintype.decidableForallFintype) Equiv.instFintype) := by
      exact @Fintype.card_congr
        {σ : Equiv.Perm (Fin n) // ∀ i : Fin m, rCycleCount n (lengths i) σ = v i}
        {σ : Equiv.Perm (Fin n) //
          (fun σ => ∀ i : Fin m, rCycleCount n (lengths i) σ = v i) σ}
        (@Subtype.fintype (Equiv.Perm (Fin n))
          (fun σ => ∀ i : Fin m, rCycleCount n (lengths i) σ = v i)
          (fun a => Nat.decidableForallFin
            (fun i => rCycleCount n (lengths i) a = v i)) Equiv.instFintype)
        (@Subtype.fintype (Equiv.Perm (Fin n))
          (fun σ => ∀ i : Fin m, rCycleCount n (lengths i) σ = v i)
          (fun _ => Fintype.decidableForallFintype) Equiv.instFintype)
        (Equiv.refl _)
    unfold multivariatePMF
    rw [ENNReal.ofReal_div_of_pos]
    · congr
      · exact_mod_cast hcard
      · exact_mod_cast rfl
    · positivity
  · simp

lemma poissonPiMeasure_singleton {m : ℕ} (lengths : Fin m → ℕ) (v : Fin m → ℕ) :
    (poissonPiMeasure lengths : Measure (Fin m → ℕ)) ({v} : Set (Fin m → ℕ)) =
      ENNReal.ofReal (poissonPiPMF lengths v) := by
  rw [poissonPiMeasure, poissonPiPMF]
  change Measure.pi
      (fun i : Fin m => ProbabilityTheory.poissonMeasure (poissonRate (lengths i))) {v} =
    ENNReal.ofReal
      (∏ i : Fin m, ProbabilityTheory.poissonPMFReal (poissonRate (lengths i)) (v i))
  rw [Measure.pi_singleton]
  rw [ENNReal.ofReal_prod_of_nonneg]
  · refine Finset.prod_congr rfl ?_
    intro i _hi
    exact poisson_law_singleton (poissonRate (lengths i)) (v i)
  · intro i _hi
    exact ProbabilityTheory.poissonPMFReal_nonneg

theorem multivariateLaw_tendsto_poissonPi {m : ℕ} (lengths : Fin m → ℕ)
    (hpos : ∀ i : Fin m, 0 < lengths i) (hinj : Function.Injective lengths) :
    Tendsto (fun n : ℕ => multivariateLaw n lengths) atTop
      (𝓝 (poissonPiMeasure lengths)) := by
  refine probabilityMeasure_pi_nat_tendsto_of_tendsto_pmfReal
    (p := fun n v => multivariatePMF n lengths v)
    (q := fun v => poissonPiPMF lengths v) ?_ ?_ ?_
  · intro n v
    exact multivariate_law_singleton n lengths v
  · intro v
    exact poissonPiMeasure_singleton lengths v
  · intro v
    exact multivariatePMF_tendsto_poissonPiPMF lengths hpos hinj v

end Multivariate
end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
