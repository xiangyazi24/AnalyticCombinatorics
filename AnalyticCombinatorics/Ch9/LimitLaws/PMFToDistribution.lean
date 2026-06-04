import Mathlib
import AnalyticCombinatorics.Ch9.LimitLaws.FixedPointsPoisson

/-!
# Pointwise pmf convergence on `ℕ` implies weak convergence

This file supplies a reusable discrete bridge from pointwise convergence of
singleton masses on `ℕ` to Mathlib's weak convergence topology on
`ProbabilityMeasure ℕ`, and applies it to the fixed-point count in a uniform
random permutation.
-/

noncomputable section

open Filter
open scoped Topology ENNReal NNReal

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace PMFToDistribution

open MeasureTheory

/-- On `ℕ`, convergence of all singleton masses implies weak convergence of
probability measures. This is the reusable discrete bridge used below.

The proof is the portmanteau finite-subset argument: finite sums of singleton
masses converge, finite unions are contained in the open set, and the limiting
measure of an arbitrary subset of `ℕ` is the supremum of its finite
approximations. -/
theorem probabilityMeasure_nat_tendsto_of_tendsto_singleton
    {μs : ℕ → ProbabilityMeasure ℕ} {μ : ProbabilityMeasure ℕ}
    (h : ∀ j : ℕ,
      Tendsto (fun n : ℕ => (μs n : Measure ℕ) ({j} : Set ℕ)) atTop
        (𝓝 ((μ : Measure ℕ) ({j} : Set ℕ)))) :
    Tendsto μs atTop (𝓝 μ) := by
  classical
  refine MeasureTheory.tendsto_of_forall_isOpen_le_liminf_nat' ?_
  intro G _hG
  have hfinite_le :
      ∀ s : Finset ℕ, (∀ j ∈ s, j ∈ G) →
        (∑ j ∈ s, (μ : Measure ℕ) ({j} : Set ℕ)) ≤
          atTop.liminf (fun n : ℕ => (μs n : Measure ℕ) G) := by
    intro s hsG
    have hsum_tendsto :
        Tendsto
          (fun n : ℕ => ∑ j ∈ s, (μs n : Measure ℕ) ({j} : Set ℕ))
          atTop
          (𝓝 (∑ j ∈ s, (μ : Measure ℕ) ({j} : Set ℕ))) :=
      tendsto_finset_sum s (fun j _hj => h j)
    rw [← hsum_tendsto.liminf_eq]
    refine Filter.liminf_le_liminf (Eventually.of_forall ?_)
      (by isBoundedDefault)
      (by isBoundedDefault)
    intro n
    have hdisj : (s : Set ℕ).PairwiseDisjoint (fun j => ({j} : Set ℕ)) := by
      intro a _ha b _hb hne
      change Disjoint ({a} : Set ℕ) ({b} : Set ℕ)
      rw [Set.disjoint_singleton_left]
      simpa using hne
    calc
      (∑ j ∈ s, (μs n : Measure ℕ) ({j} : Set ℕ))
          = (μs n : Measure ℕ) (⋃ j ∈ s, ({j} : Set ℕ)) := by
              exact (MeasureTheory.measure_biUnion_finset hdisj
                (fun j _hj => measurableSet_singleton j)).symm
      _ ≤ (μs n : Measure ℕ) G := by
              refine measure_mono ?_
              intro x hx
              simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hx
              rcases hx with ⟨j, hj, hxj⟩
              subst hxj
              exact hsG x hj
  have hμG :
      (μ : Measure ℕ) G =
        ∑' j : ℕ, G.indicator (fun j => (μ : Measure ℕ) ({j} : Set ℕ)) j := by
    exact (Measure.tsum_indicator_apply_singleton (μ : Measure ℕ) G (by simp)).symm
  rw [hμG, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le ?_
  intro s
  calc
    (∑ j ∈ s, G.indicator (fun j => (μ : Measure ℕ) ({j} : Set ℕ)) j)
        = ∑ j ∈ s.filter (fun j => j ∈ G), (μ : Measure ℕ) ({j} : Set ℕ) := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl ?_
            intro j _hj
            by_cases hjG : j ∈ G
            · simp [hjG]
            · simp [hjG]
    _ ≤ atTop.liminf (fun n : ℕ => (μs n : Measure ℕ) G) :=
            hfinite_le (s.filter (fun j => j ∈ G))
              (fun j hj => (Finset.mem_filter.mp hj).2)

/-- A real-valued pmf version of
`probabilityMeasure_nat_tendsto_of_tendsto_singleton`. -/
theorem probabilityMeasure_nat_tendsto_of_tendsto_pmfReal
    {p : ℕ → ℕ → ℝ} {q : ℕ → ℝ}
    {μs : ℕ → ProbabilityMeasure ℕ} {μ : ProbabilityMeasure ℕ}
    (hp : ∀ n j, (μs n : Measure ℕ) ({j} : Set ℕ) = ENNReal.ofReal (p n j))
    (hq : ∀ j, (μ : Measure ℕ) ({j} : Set ℕ) = ENNReal.ofReal (q j))
    (hconv : ∀ j : ℕ, Tendsto (fun n : ℕ => p n j) atTop (𝓝 (q j))) :
    Tendsto μs atTop (𝓝 μ) :=
  probabilityMeasure_nat_tendsto_of_tendsto_singleton fun j => by
    simpa [hp, hq] using ENNReal.tendsto_ofReal (hconv j)

namespace FixedPointsPoissonNS

open AnalyticCombinatorics.Ch9.LimitLaws.FixedPointsPoissonNS

instance instMeasurableSpacePermFin (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) :=
  ⊤

/-- Uniform probability measure on permutations of `Fin n`. -/
def uniformPermMeasure (n : ℕ) : Measure (Equiv.Perm (Fin n)) :=
  (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure

instance uniformPermMeasure_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (uniformPermMeasure n) := by
  unfold uniformPermMeasure
  infer_instance

lemma fixedPointCount_aemeasurable (n : ℕ) :
    AEMeasurable (FixedPointsPoissonNS.fixedPointCount n) (uniformPermMeasure n) :=
  (measurable_of_finite _).aemeasurable

/-- The law of the fixed-point count under the uniform permutation measure. -/
def fixedPointLaw (n : ℕ) : ProbabilityMeasure ℕ :=
  ⟨Measure.map (FixedPointsPoissonNS.fixedPointCount n) (uniformPermMeasure n),
    Measure.isProbabilityMeasure_map (fixedPointCount_aemeasurable n)⟩

/-- The Poisson law as a `ProbabilityMeasure`. -/
def poissonProbabilityMeasure (r : ℝ≥0) : ProbabilityMeasure ℕ :=
  ⟨ProbabilityTheory.poissonMeasure r, ProbabilityTheory.isProbabilityMeasurePoisson r⟩

/-- The fixed-point set as a finset. -/
def fixedPointFinset (n : ℕ) (σ : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => σ i = i)

@[simp]
lemma mem_fixedPointFinset {n : ℕ} {σ : Equiv.Perm (Fin n)} {i : Fin n} :
    i ∈ fixedPointFinset n σ ↔ σ i = i := by
  simp [fixedPointFinset]

lemma card_fixedPointFinset (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (fixedPointFinset n σ).card =
      FixedPointsPoissonNS.fixedPointCount n σ := by
  classical
  unfold fixedPointFinset FixedPointsPoissonNS.fixedPointCount
  exact (Fintype.card_ofFinset (Finset.univ.filter (fun i => σ i = i))
    (fun i => by
      change i ∈ Finset.univ.filter (fun i : Fin n => σ i = i) ↔ σ i = i
      simp)).symm

lemma fixedPointFinset_eq_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Finset (Fin n)) :
    fixedPointFinset n σ = s ↔
      ∀ i : Fin n, i ∈ s ↔ σ i = i := by
  constructor
  · intro h i
    rw [← h]
    exact mem_fixedPointFinset
  · intro h
    ext i
    simp [h i]

lemma derangements_subtype_fixedPointFinset_iff {n : ℕ} (s : Finset (Fin n))
    (σ : Equiv.Perm (Fin n)) :
    (∀ i : Fin n, ¬ i ∉ (s : Set (Fin n)) ↔ i ∈ Function.fixedPoints σ) ↔
      fixedPointFinset n σ = s := by
  constructor
  · intro h
    refine (fixedPointFinset_eq_iff σ s).2 ?_
    intro i
    have hi := h i
    simpa [Function.mem_fixedPoints_iff] using hi
  · intro h i
    have hi := (fixedPointFinset_eq_iff σ s).1 h i
    simpa [Function.mem_fixedPoints_iff] using hi

/-- Permutations with fixed-point set `s` are derangements on the complement of `s`. -/
def permsWithFixedPointFinsetEquivDerangements {n : ℕ} (s : Finset (Fin n)) :
    {σ : Equiv.Perm (Fin n) // fixedPointFinset n σ = s} ≃
      derangements ({i : Fin n // i ∉ (s : Set (Fin n))}) :=
  ((derangements.subtypeEquiv (fun i : Fin n => i ∉ (s : Set (Fin n)))).trans
    (Equiv.subtypeEquivRight
      (fun σ => derangements_subtype_fixedPointFinset_iff (n := n) s σ))).symm

lemma card_complement_finset (n : ℕ) (s : Finset (Fin n)) :
    Fintype.card {i : Fin n // i ∉ (s : Set (Fin n))} = n - s.card := by
  classical
  change Fintype.card (↥((s : Set (Fin n))ᶜ)) = n - s.card
  rw [Fintype.card_compl_set, Fintype.card_fin]
  congr
  exact Fintype.card_ofFinset s (fun i => by simp)

lemma card_permsWithFixedPointFinset {n : ℕ} (s : Finset (Fin n)) :
    Fintype.card {σ : Equiv.Perm (Fin n) // fixedPointFinset n σ = s} =
      numDerangements (n - s.card) := by
  classical
  rw [Fintype.card_congr (permsWithFixedPointFinsetEquivDerangements (n := n) s)]
  rw [card_derangements_eq_numDerangements]
  rw [card_complement_finset n s]

def permsByFixedPointFinsetEquiv (n j : ℕ) :
    {σ : Equiv.Perm (Fin n) //
      FixedPointsPoissonNS.fixedPointCount n σ = j} ≃
      Σ s : Set.powersetCard (Fin n) j,
        {σ : Equiv.Perm (Fin n) // fixedPointFinset n σ = (s : Finset (Fin n))} where
  toFun σ :=
    ⟨⟨fixedPointFinset n σ.1, by
        rw [Set.powersetCard.mem_iff]
        rw [card_fixedPointFinset n σ.1, σ.2]⟩,
      ⟨σ.1, rfl⟩⟩
  invFun x :=
    ⟨x.2.1, by
      rw [← card_fixedPointFinset n x.2.1, x.2.2]
      exact Set.powersetCard.card_eq x.1⟩
  left_inv σ := by
    ext
    rfl
  right_inv x := by
    cases x with
    | mk s σ =>
      cases σ with
      | mk σ hσ =>
        ext <;> simp [hσ]

lemma card_fixedPointCount_eq (n j : ℕ) :
    Fintype.card {σ : Equiv.Perm (Fin n) //
      FixedPointsPoissonNS.fixedPointCount n σ = j} =
        FixedPointsPoissonNS.fixedPointFavourableCount n j := by
  classical
  unfold FixedPointsPoissonNS.fixedPointFavourableCount
  rw [Fintype.card_congr (permsByFixedPointFinsetEquiv n j)]
  rw [Fintype.card_sigma]
  calc
    (∑ s : Set.powersetCard (Fin n) j,
        Fintype.card {σ : Equiv.Perm (Fin n) //
          fixedPointFinset n σ = (s : Finset (Fin n))})
        = ∑ _s : Set.powersetCard (Fin n) j, numDerangements (n - j) := by
            refine Finset.sum_congr rfl ?_
            intro s _hs
            rw [card_permsWithFixedPointFinset (n := n) (s : Finset (Fin n))]
            rw [Set.powersetCard.card_eq s]
    _ = Fintype.card (Set.powersetCard (Fin n) j) * numDerangements (n - j) := by
            rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
    _ = n.choose j * numDerangements (n - j) := by
            congr
            rw [← Nat.card_eq_fintype_card]
            rw [Set.powersetCard.card, Nat.card_fin]

lemma fixedPoint_law_singleton (n j : ℕ) :
    (Measure.map (FixedPointsPoissonNS.fixedPointCount n) (uniformPermMeasure n))
        ({j} : Set ℕ) =
      ENNReal.ofReal (FixedPointsPoissonNS.fixedPointPMF n j) := by
  classical
  have hpre :
      (FixedPointsPoissonNS.fixedPointCount n) ⁻¹' ({j} : Set ℕ) =
        {σ : Equiv.Perm (Fin n) | FixedPointsPoissonNS.fixedPointCount n σ = j} := by
    ext σ
    simp
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton j), hpre]
  unfold uniformPermMeasure
  rw [PMF.toMeasure_uniformOfFintype_apply]
  · rw [Fintype.card_perm, Fintype.card_fin]
    change (Fintype.card {σ : Equiv.Perm (Fin n) //
        FixedPointsPoissonNS.fixedPointCount n σ = j} : ℝ≥0∞) /
        (n.factorial : ℝ≥0∞) =
      ENNReal.ofReal (FixedPointsPoissonNS.fixedPointPMF n j)
    rw [card_fixedPointCount_eq n j]
    unfold FixedPointsPoissonNS.fixedPointPMF
    rw [ENNReal.ofReal_div_of_pos]
    · congr
      · exact_mod_cast rfl
      · exact_mod_cast rfl
    · positivity
  · simp

lemma poisson_law_singleton_one (j : ℕ) :
    (ProbabilityTheory.poissonMeasure (1 : ℝ≥0)) ({j} : Set ℕ) =
      ENNReal.ofReal (ProbabilityTheory.poissonPMFReal (1 : ℝ≥0) j) := by
  rw [ProbabilityTheory.poissonMeasure]
  exact PMF.toMeasure_apply_singleton _ j (measurableSet_singleton j)

/-- The laws of fixed-point counts in a uniform random permutation converge weakly to
`Poisson(1)`. -/
theorem fixedPoint_law_tendsto_poisson_one :
    Tendsto fixedPointLaw atTop (𝓝 (poissonProbabilityMeasure (1 : ℝ≥0))) := by
  refine probabilityMeasure_nat_tendsto_of_tendsto_pmfReal
    (p := fun n j => FixedPointsPoissonNS.fixedPointPMF n j)
    (q := fun j => ProbabilityTheory.poissonPMFReal (1 : ℝ≥0) j) ?_ ?_ ?_
  · intro n j
    exact fixedPoint_law_singleton n j
  · intro j
    exact poisson_law_singleton_one j
  · intro j
    exact FixedPointsPoissonNS.fixedPointPMF_tendsto_poissonPMFReal_one j

/-- Full convergence in distribution of the fixed-point count to `Poisson(1)`. -/
theorem fixedPoints_tendstoInDistribution_poisson_one :
    TendstoInDistribution
      (fun n (ω : Equiv.Perm (Fin n)) => FixedPointsPoissonNS.fixedPointCount n ω)
      atTop
      (fun x : ℕ => x)
      uniformPermMeasure
      (ProbabilityTheory.poissonMeasure (1 : ℝ≥0)) where
  forall_aemeasurable n := fixedPointCount_aemeasurable n
  aemeasurable_limit := by exact measurable_id.aemeasurable
  tendsto := by
    simpa [fixedPointLaw, poissonProbabilityMeasure] using fixedPoint_law_tendsto_poisson_one

end FixedPointsPoissonNS

end PMFToDistribution
end LimitLaws
end Ch9
end AnalyticCombinatorics
