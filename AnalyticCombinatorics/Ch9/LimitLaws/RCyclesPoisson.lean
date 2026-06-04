import Mathlib
import AnalyticCombinatorics.Ch9.LimitLaws.FixedPointsPoisson
import AnalyticCombinatorics.Ch9.LimitLaws.PMFToDistribution

/-!
# Cycles of a fixed length in a random permutation

This file sets up the genuine random variable counting cycles of length exactly
`r` in a uniform random permutation of `Fin n`.

For `r = 1` this is the fixed-point count.  For `r ≥ 2` it is the multiplicity
of `r` in Mathlib's `cycleType`, equivalently the number of nontrivial cycle
factors with support of cardinality `r`.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS

/-- The Poisson rate `1 / r`, as a nonnegative real. -/
def poissonRate (r : ℕ) : ℝ≥0 :=
  (r : ℝ≥0)⁻¹

/-- Uniform probability measure on permutations of `Fin n`. -/
def uniformPermMeasure (n : ℕ) : Measure (Equiv.Perm (Fin n)) :=
  (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure

instance uniformPermMeasure_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (uniformPermMeasure n) := by
  unfold uniformPermMeasure
  infer_instance

/-- The Poisson law as a `ProbabilityMeasure`. -/
def poissonProbabilityMeasure (r : ℝ≥0) : ProbabilityMeasure ℕ :=
  ⟨ProbabilityTheory.poissonMeasure r, ProbabilityTheory.isProbabilityMeasurePoisson r⟩

/-- The number of cycles of length exactly `r` in a permutation of `Fin n`.

Mathlib's `cycleType` records only nontrivial cycles, so `r = 1` is handled by
the fixed-point count. -/
def rCycleCount (n r : ℕ) (σ : Equiv.Perm (Fin n)) : ℕ :=
  if r = 1 then FixedPointsPoissonNS.fixedPointCount n σ else σ.cycleType.count r

@[simp]
lemma rCycleCount_one (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    rCycleCount n 1 σ = FixedPointsPoissonNS.fixedPointCount n σ := by
  simp [rCycleCount]

lemma rCycleCount_eq_cycleType_count_of_ne_one {n r : ℕ}
    (hr : r ≠ 1) (σ : Equiv.Perm (Fin n)) :
    rCycleCount n r σ = σ.cycleType.count r := by
  simp [rCycleCount, hr]

lemma rCycleCount_eq_card_cycleFactorsFinset_filter {n r : ℕ} (hr : 2 ≤ r)
    (σ : Equiv.Perm (Fin n)) :
    rCycleCount n r σ =
      (σ.cycleFactorsFinset.filter fun c : Equiv.Perm (Fin n) => c.support.card = r).card := by
  rw [rCycleCount_eq_cycleType_count_of_ne_one (by omega : r ≠ 1) σ]
  rw [Equiv.Perm.CycleType.count_def (σ := σ) r]
  rw [Fintype.subtype_card, Finset.univ_eq_attach, Finset.filter_attach']
  rw [Finset.card_map, Finset.card_attach]
  exact congrArg Finset.card (by
    refine Finset.filter_congr
      (s := σ.cycleFactorsFinset)
      (p := fun c : Equiv.Perm (Fin n) =>
        ∃ h : c ∈ σ.cycleFactorsFinset,
          ((⟨c, h⟩ : {x // x ∈ σ.cycleFactorsFinset}) : Equiv.Perm (Fin n)).support.card = r)
      (q := fun c : Equiv.Perm (Fin n) => c.support.card = r) ?_
    intro c hc
    constructor
    · rintro ⟨h, hcard⟩
      simpa using hcard
    · intro hcard
      exact ⟨hc, by simpa using hcard⟩)

lemma rCycleCount_aemeasurable (n r : ℕ) :
    AEMeasurable (rCycleCount n r) (uniformPermMeasure n) :=
  (measurable_of_finite _).aemeasurable

/-- The law of the `r`-cycle count under the uniform permutation measure. -/
def rCycleLaw (n r : ℕ) : ProbabilityMeasure ℕ :=
  ⟨Measure.map (rCycleCount n r) (uniformPermMeasure n),
    Measure.isProbabilityMeasure_map (rCycleCount_aemeasurable n r)⟩

/-- Number of permutations of `Fin n` with exactly `j` cycles of length `r`. -/
def rCycleFavourableCount (n r j : ℕ) : ℕ :=
  Fintype.card {σ : Equiv.Perm (Fin n) // rCycleCount n r σ = j}

/-- The genuine pmf of the `r`-cycle count under the uniform measure. -/
def rCyclePMF (n r j : ℕ) : ℝ :=
  (rCycleFavourableCount n r j : ℝ) / n.factorial

/-- Partial sums of the real exponential series, using `range m`. -/
def expPartial (x : ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range m, x ^ i / i.factorial

lemma expPartial_tendsto_exp (x : ℝ) :
    Tendsto (fun m : ℕ => expPartial x m) atTop (𝓝 (Real.exp x)) := by
  simpa [expPartial, ← Real.exp_eq_exp_ℝ] using
    (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) x).tendsto_sum_nat

lemma nat_div_tendsto_atTop {r : ℕ} (hr : 0 < r) :
    Tendsto (fun n : ℕ => n / r) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨b * r, fun n hn => ?_⟩
  exact (Nat.le_div_iff_mul_le hr).2 hn

lemma nat_div_sub_tendsto_atTop {r : ℕ} (hr : 0 < r) (j : ℕ) :
    Tendsto (fun n : ℕ => n / r - j) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨(b + j) * r, fun n hn => ?_⟩
  have hdiv : b + j ≤ n / r := (Nat.le_div_iff_mul_le hr).2 hn
  exact Nat.le_sub_of_add_le hdiv

lemma nat_div_sub_add_one_tendsto_atTop {r : ℕ} (hr : 0 < r) (j : ℕ) :
    Tendsto (fun n : ℕ => n / r - j + 1) atTop atTop :=
  (tendsto_add_atTop_nat 1).comp (nat_div_sub_tendsto_atTop hr j)

/-- The standard inclusion-exclusion pmf expression for the number of `r`-cycles.

The theorem `rCyclePMFFormula_tendsto_poisson` proves the analytic limit of this
formula.  The remaining combinatorial step is to identify the genuine pmf
`rCyclePMF` with this expression. -/
def rCyclePMFFormula (n r j : ℕ) : ℝ :=
  if r = 0 then 0
  else if r * j ≤ n then
    (((r : ℝ) ^ j * j.factorial)⁻¹) *
      expPartial (-(r : ℝ)⁻¹) (n / r - j + 1)
  else 0

theorem rCyclePMFFormula_tendsto_poisson {r : ℕ} (hr : 0 < r) (j : ℕ) :
    Tendsto (fun n : ℕ => rCyclePMFFormula n r j) atTop
      (𝓝 (ProbabilityTheory.poissonPMFReal (poissonRate r) j)) := by
  have hidx : Tendsto (fun n : ℕ => n / r - j + 1) atTop atTop :=
    nat_div_sub_add_one_tendsto_atTop hr j
  have hpartial :
      Tendsto
        (fun n : ℕ => expPartial (-(r : ℝ)⁻¹) (n / r - j + 1))
        atTop (𝓝 (Real.exp (-(r : ℝ)⁻¹))) :=
    (expPartial_tendsto_exp (-(r : ℝ)⁻¹)).comp hidx
  have hmain :
      Tendsto
        (fun n : ℕ =>
          (((r : ℝ) ^ j * j.factorial)⁻¹) *
            expPartial (-(r : ℝ)⁻¹) (n / r - j + 1))
        atTop
        (𝓝 ((((r : ℝ) ^ j * j.factorial)⁻¹) *
          Real.exp (-(r : ℝ)⁻¹))) :=
    tendsto_const_nhds.mul hpartial
  have heq :
      (fun n : ℕ => rCyclePMFFormula n r j) =ᶠ[atTop]
        fun n : ℕ =>
          (((r : ℝ) ^ j * j.factorial)⁻¹) *
            expPartial (-(r : ℝ)⁻¹) (n / r - j + 1) := by
    filter_upwards [eventually_ge_atTop (r * j)] with n hn
    simp [rCyclePMFFormula, Nat.ne_of_gt hr, hn]
  refine Tendsto.congr' heq.symm ?_
  convert hmain using 1
  rw [ProbabilityTheory.poissonPMFReal]
  simp [poissonRate]
  have hrℝ : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hjfac : (j.factorial : ℝ) ≠ 0 := by positivity
  field_simp [hrℝ, pow_ne_zero j hrℝ, hjfac]

theorem rCyclePMF_tendsto_poisson_of_eventually_formula {r : ℕ} (hr : 0 < r)
    (hformula : ∀ j : ℕ,
      (fun n : ℕ => rCyclePMF n r j) =ᶠ[atTop]
        fun n : ℕ => rCyclePMFFormula n r j) :
    ∀ j : ℕ,
      Tendsto (fun n : ℕ => rCyclePMF n r j) atTop
        (𝓝 (ProbabilityTheory.poissonPMFReal (poissonRate r) j)) := by
  intro j
  exact Tendsto.congr' (hformula j).symm (rCyclePMFFormula_tendsto_poisson hr j)

lemma rCycle_law_singleton (n r j : ℕ) :
    (Measure.map (rCycleCount n r) (uniformPermMeasure n)) ({j} : Set ℕ) =
      ENNReal.ofReal (rCyclePMF n r j) := by
  classical
  have hpre :
      (rCycleCount n r) ⁻¹' ({j} : Set ℕ) =
        {σ : Equiv.Perm (Fin n) | rCycleCount n r σ = j} := by
    ext σ
    simp
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton j), hpre]
  unfold uniformPermMeasure
  rw [PMF.toMeasure_uniformOfFintype_apply]
  · rw [Fintype.card_perm, Fintype.card_fin]
    change (Fintype.card {σ : Equiv.Perm (Fin n) //
        rCycleCount n r σ = j} : ℝ≥0∞) / (n.factorial : ℝ≥0∞) =
      ENNReal.ofReal (rCyclePMF n r j)
    unfold rCyclePMF rCycleFavourableCount
    rw [ENNReal.ofReal_div_of_pos]
    · congr
      · exact_mod_cast rfl
      · exact_mod_cast rfl
    · positivity
  · simp

lemma poisson_law_singleton (r : ℝ≥0) (j : ℕ) :
    (ProbabilityTheory.poissonMeasure r) ({j} : Set ℕ) =
      ENNReal.ofReal (ProbabilityTheory.poissonPMFReal r j) := by
  rw [ProbabilityTheory.poissonMeasure]
  exact PMF.toMeasure_apply_singleton _ j (measurableSet_singleton j)

/-- Pointwise pmf convergence implies weak convergence of the laws of `r`-cycle
counts.  The nontrivial combinatorial input is the supplied pmf limit. -/
theorem rCycle_law_tendsto_poisson_of_tendsto_pmf
    {r : ℕ}
    (hpmf : ∀ j : ℕ,
      Tendsto (fun n : ℕ => rCyclePMF n r j) atTop
        (𝓝 (ProbabilityTheory.poissonPMFReal (poissonRate r) j))) :
    Tendsto (fun n : ℕ => rCycleLaw n r) atTop
      (𝓝 (poissonProbabilityMeasure (poissonRate r))) := by
  refine PMFToDistribution.probabilityMeasure_nat_tendsto_of_tendsto_pmfReal
    (p := fun n j => rCyclePMF n r j)
    (q := fun j => ProbabilityTheory.poissonPMFReal (poissonRate r) j) ?_ ?_ ?_
  · intro n j
    exact rCycle_law_singleton n r j
  · intro j
    exact poisson_law_singleton (poissonRate r) j
  · intro j
    exact hpmf j

/-- Full convergence in distribution from pointwise pmf convergence. -/
theorem rCycles_tendstoInDistribution_poisson_of_tendsto_pmf
    {r : ℕ}
    (hpmf : ∀ j : ℕ,
      Tendsto (fun n : ℕ => rCyclePMF n r j) atTop
        (𝓝 (ProbabilityTheory.poissonPMFReal (poissonRate r) j))) :
    TendstoInDistribution
      (fun n (ω : Equiv.Perm (Fin n)) => rCycleCount n r ω)
      atTop
      (fun x : ℕ => x)
      uniformPermMeasure
      (ProbabilityTheory.poissonMeasure (poissonRate r)) where
  forall_aemeasurable n := rCycleCount_aemeasurable n r
  aemeasurable_limit := by exact measurable_id.aemeasurable
  tendsto := by
    simpa [rCycleLaw, poissonProbabilityMeasure] using
      rCycle_law_tendsto_poisson_of_tendsto_pmf (r := r) hpmf

theorem rCycle_law_tendsto_poisson_of_eventually_formula {r : ℕ} (hr : 0 < r)
    (hformula : ∀ j : ℕ,
      (fun n : ℕ => rCyclePMF n r j) =ᶠ[atTop]
        fun n : ℕ => rCyclePMFFormula n r j) :
    Tendsto (fun n : ℕ => rCycleLaw n r) atTop
      (𝓝 (poissonProbabilityMeasure (poissonRate r))) :=
  rCycle_law_tendsto_poisson_of_tendsto_pmf
    (rCyclePMF_tendsto_poisson_of_eventually_formula hr hformula)

theorem rCycles_tendstoInDistribution_poisson_of_eventually_formula {r : ℕ} (hr : 0 < r)
    (hformula : ∀ j : ℕ,
      (fun n : ℕ => rCyclePMF n r j) =ᶠ[atTop]
        fun n : ℕ => rCyclePMFFormula n r j) :
    TendstoInDistribution
      (fun n (ω : Equiv.Perm (Fin n)) => rCycleCount n r ω)
      atTop
      (fun x : ℕ => x)
      uniformPermMeasure
      (ProbabilityTheory.poissonMeasure (poissonRate r)) :=
  rCycles_tendstoInDistribution_poisson_of_tendsto_pmf
    (rCyclePMF_tendsto_poisson_of_eventually_formula hr hformula)

/-- The `r = 1` specialization is exactly the fixed-points Poisson limit. -/
theorem oneCycles_tendstoInDistribution_poisson :
    TendstoInDistribution
      (fun n (ω : Equiv.Perm (Fin n)) => rCycleCount n 1 ω)
      atTop
      (fun x : ℕ => x)
      uniformPermMeasure
      (ProbabilityTheory.poissonMeasure (poissonRate 1)) := by
  simpa [rCycleCount, poissonRate, uniformPermMeasure] using
    PMFToDistribution.FixedPointsPoissonNS.fixedPoints_tendstoInDistribution_poisson_one

end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
