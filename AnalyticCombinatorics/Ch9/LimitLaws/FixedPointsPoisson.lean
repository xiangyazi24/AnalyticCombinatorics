import Mathlib
import AnalyticCombinatorics.Ch4.Analytic.Derangements

/-!
# Fixed points in a random permutation

This file records the discrete Poisson(1) limit for fixed points of a uniform
random permutation at the level currently most directly supported by Mathlib:

* the exact factorial-moment identity
  `E[(F_n)_k] = 1` for `k <= n`;
* the pointwise probability mass limit
  `P(F_n = j) -> exp(-1) / j!`.

The probability mass is expressed by the genuine derangement count
`choose n j * D_{n-j} / n!`.
-/

noncomputable section

open Filter
open scoped Topology NNReal

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace FixedPointsPoissonNS

/-- The number of fixed points of a permutation of `Fin n`. -/
def fixedPointCount (n : ℕ) (σ : Equiv.Perm (Fin n)) : ℕ :=
  Fintype.card {i : Fin n // σ i = i}

/-- Uniform expectation over permutations of `Fin n`, as a finite average. -/
def uniformPermExpectation (n : ℕ) (X : Equiv.Perm (Fin n) → ℝ) : ℝ :=
  (∑ σ : Equiv.Perm (Fin n), X σ) / n.factorial

/-- Embeddings whose image is pointwise fixed by a given permutation. -/
def FixedEmbeddingsOfPerm (n k : ℕ) (σ : Equiv.Perm (Fin n)) : Type :=
  {e : Fin k ↪ Fin n // ∀ i, σ (e i) = e i}

/-- Permutations that pointwise fix the image of a given embedding. -/
def PermFixingEmbedding (n k : ℕ) (e : Fin k ↪ Fin n) : Type :=
  {σ : Equiv.Perm (Fin n) // ∀ i, σ (e i) = e i}

instance instFintypeFixedEmbeddingsOfPerm (n k : ℕ) (σ : Equiv.Perm (Fin n)) :
    Fintype (FixedEmbeddingsOfPerm n k σ) := by
  classical
  unfold FixedEmbeddingsOfPerm
  infer_instance

instance instFintypePermFixingEmbedding (n k : ℕ) (e : Fin k ↪ Fin n) :
    Fintype (PermFixingEmbedding n k e) := by
  classical
  unfold PermFixingEmbedding
  infer_instance

/-- Count the same incidence relation first by permutations. -/
abbrev FixedEmbeddingByPerm (n k : ℕ) : Type :=
  Σ σ : Equiv.Perm (Fin n), FixedEmbeddingsOfPerm n k σ

/-- Count the same incidence relation first by ordered fixed-point choices. -/
abbrev FixedEmbeddingByEmbedding (n k : ℕ) : Type :=
  Σ e : Fin k ↪ Fin n, PermFixingEmbedding n k e

/-- A fixed ordered `k`-tuple in the fixed-point set is the same as an embedding
into the fixed-point subtype. -/
def fixedEmbeddingsOfPermEquiv (n k : ℕ) (σ : Equiv.Perm (Fin n)) :
    (Fin k ↪ {i : Fin n // σ i = i}) ≃ FixedEmbeddingsOfPerm n k σ where
  toFun f :=
    ⟨f.trans (Function.Embedding.subtype _), fun i => (f i).2⟩
  invFun e :=
    { toFun := fun i => ⟨e.1 i, e.2 i⟩
      inj' := by
        intro a b h
        exact e.1.injective (Subtype.ext_iff.mp h) }
  left_inv f := by
    ext i
    rfl
  right_inv e := by
    cases e with
    | mk e h =>
      rfl

lemma card_fixedEmbeddingsOfPerm (n k : ℕ) (σ : Equiv.Perm (Fin n)) :
    Fintype.card (FixedEmbeddingsOfPerm n k σ) =
      (fixedPointCount n σ).descFactorial k := by
  classical
  rw [← Fintype.card_congr (fixedEmbeddingsOfPermEquiv n k σ)]
  rw [Fintype.card_embedding_eq]
  simp [fixedPointCount]

/-- A permutation of the complement of `range e` is the same as a permutation of
`Fin n` fixing `range e` pointwise. -/
def complementPermEquivFixingEmbedding (n k : ℕ) (e : Fin k ↪ Fin n) :
    Equiv.Perm {x : Fin n // x ∉ Set.range e} ≃ PermFixingEmbedding n k e :=
  (Equiv.Perm.subtypeEquivSubtypePerm (fun x : Fin n => x ∉ Set.range e)).trans
    { toFun := fun σ =>
        ⟨σ.1, by
          intro i
          exact σ.2 (e i) (by
            intro h
            exact h ⟨i, rfl⟩)⟩
      invFun := fun σ =>
        ⟨σ.1, by
          intro a ha
          have hmem : a ∈ Set.range e := by
            by_contra h
            exact ha h
          rcases hmem with ⟨i, rfl⟩
          exact σ.2 i⟩
      left_inv := by
        rintro ⟨σ, hσ⟩
        rfl
      right_inv := by
        rintro ⟨σ, hσ⟩
        rfl }

lemma card_complement_embedding_range (n k : ℕ) (e : Fin k ↪ Fin n) :
    Fintype.card {x : Fin n // x ∉ Set.range e} = n - k := by
  classical
  change Fintype.card (↥((Set.range (e : Fin k → Fin n))ᶜ : Set (Fin n))) = n - k
  rw [Fintype.card_compl_set (Set.range e), Fintype.card_fin, Fintype.card_range e,
    Fintype.card_fin]

lemma card_permFixingEmbedding (n k : ℕ) (e : Fin k ↪ Fin n) :
    Fintype.card (PermFixingEmbedding n k e) = (n - k).factorial := by
  classical
  rw [← Fintype.card_congr (complementPermEquivFixingEmbedding n k e)]
  rw [Fintype.card_perm, card_complement_embedding_range n k e]

/-- Swap the two ways of presenting the fixed-point incidence relation. -/
def fixedEmbeddingByPermEquivByEmbedding (n k : ℕ) :
    FixedEmbeddingByPerm n k ≃ FixedEmbeddingByEmbedding n k where
  toFun x := ⟨x.2.1, ⟨x.1, x.2.2⟩⟩
  invFun x := ⟨x.2.1, ⟨x.1, x.2.2⟩⟩
  left_inv := by
    rintro ⟨σ, e, h⟩
    rfl
  right_inv := by
    rintro ⟨e, σ, h⟩
    rfl

/-- Double-counting ordered fixed-point choices gives the unnormalized factorial moment. -/
theorem fixedPoint_factorialMoment_sum (n k : ℕ) :
    (∑ σ : Equiv.Perm (Fin n), (fixedPointCount n σ).descFactorial k) =
      n.descFactorial k * (n - k).factorial := by
  classical
  calc
    (∑ σ : Equiv.Perm (Fin n), (fixedPointCount n σ).descFactorial k)
        = ∑ σ : Equiv.Perm (Fin n),
            Fintype.card (FixedEmbeddingsOfPerm n k σ) := by
          refine Finset.sum_congr rfl ?_
          intro σ _hσ
          exact (card_fixedEmbeddingsOfPerm n k σ).symm
    _ = Fintype.card (FixedEmbeddingByPerm n k) := by
          rw [Fintype.card_sigma]
    _ = Fintype.card (FixedEmbeddingByEmbedding n k) := by
          exact Fintype.card_congr (fixedEmbeddingByPermEquivByEmbedding n k)
    _ = ∑ e : Fin k ↪ Fin n, Fintype.card (PermFixingEmbedding n k e) := by
          rw [Fintype.card_sigma]
    _ = ∑ _e : Fin k ↪ Fin n, (n - k).factorial := by
          refine Finset.sum_congr rfl ?_
          intro e _he
          exact card_permFixingEmbedding n k e
    _ = Fintype.card (Fin k ↪ Fin n) * (n - k).factorial := by
          rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
    _ = n.descFactorial k * (n - k).factorial := by
          rw [Fintype.card_embedding_eq]
          simp

/-- Exact factorial moment identity for fixed points of a uniform random permutation:
`E[(F_n)_k] = 1` for `k <= n`. -/
theorem fixedPoint_factorialMoment_eq_one {n k : ℕ} (hkn : k ≤ n) :
    uniformPermExpectation n
      (fun σ : Equiv.Perm (Fin n) => ((fixedPointCount n σ).descFactorial k : ℝ)) = 1 := by
  classical
  unfold uniformPermExpectation
  have hsumNat := fixedPoint_factorialMoment_sum n k
  have hsumReal :
      (∑ σ : Equiv.Perm (Fin n), ((fixedPointCount n σ).descFactorial k : ℝ)) =
        (n.descFactorial k * (n - k).factorial : ℕ) := by
    exact_mod_cast hsumNat
  have hfacNat : n.descFactorial k * (n - k).factorial = n.factorial := by
    rw [Nat.mul_comm]
    exact Nat.factorial_mul_descFactorial hkn
  have hfacReal : ((n.descFactorial k * (n - k).factorial : ℕ) : ℝ) =
      n.factorial := by
    exact_mod_cast hfacNat
  rw [hsumReal, hfacReal]
  field_simp [Nat.factorial_ne_zero]

/-- The derangement-count expression for the fixed-point probability mass. -/
def fixedPointFavourableCount (n j : ℕ) : ℕ :=
  n.choose j * numDerangements (n - j)

/-- Probability mass `P(F_n = j)` expressed by choosing the fixed points and
deranging the complement. For `j > n` this is zero because `n.choose j = 0`. -/
def fixedPointPMF (n j : ℕ) : ℝ :=
  (fixedPointFavourableCount n j : ℝ) / n.factorial

lemma fixedPointPMF_eq_derangements_div {n j : ℕ} (hjn : j ≤ n) :
    fixedPointPMF n j =
      ((numDerangements (n - j) : ℝ) / (n - j).factorial) / j.factorial := by
  unfold fixedPointPMF fixedPointFavourableCount
  have hfacNat : n.choose j * j.factorial * (n - j).factorial = n.factorial :=
    Nat.choose_mul_factorial_mul_factorial hjn
  have hfacReal :
      ((n.choose j : ℝ) * j.factorial * (n - j).factorial) = n.factorial := by
    exact_mod_cast hfacNat
  have hnf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hjf : (j.factorial : ℝ) ≠ 0 := by positivity
  have hnjf : ((n - j).factorial : ℝ) ≠ 0 := by positivity
  field_simp [hfacReal, hnf, hjf, hnjf]
  rw [Nat.cast_mul]
  calc
    (n.choose j : ℝ) * (numDerangements (n - j) : ℝ) *
          (n - j).factorial * j.factorial
        = ((n.choose j : ℝ) * j.factorial * (n - j).factorial) *
            (numDerangements (n - j) : ℝ) := by
          ring
    _ = n.factorial * (numDerangements (n - j) : ℝ) := by
          rw [hfacReal]

/-- Pointwise pmf convergence: `P(F_n = j) -> exp(-1) / j!`. -/
theorem fixedPointPMF_tendsto (j : ℕ) :
    Tendsto (fun n : ℕ => fixedPointPMF n j) atTop
      (𝓝 (Real.exp (-1) / j.factorial)) := by
  have hEq :
      (fun n : ℕ => fixedPointPMF n j) =ᶠ[atTop]
        fun n : ℕ => ((numDerangements (n - j) : ℝ) / (n - j).factorial) / j.factorial := by
    filter_upwards [eventually_ge_atTop j] with n hn
    exact fixedPointPMF_eq_derangements_div hn
  have hder :
      Tendsto (fun n : ℕ => (numDerangements (n - j) : ℝ) / (n - j).factorial) atTop
        (𝓝 (Real.exp (-1))) :=
    derangement_prob_tendsto.comp (tendsto_sub_atTop_nat j)
  exact Tendsto.congr' hEq.symm (hder.div_const j.factorial)

/-- The same pointwise limit stated using Mathlib's Poisson pmf API. -/
theorem fixedPointPMF_tendsto_poissonPMFReal_one (j : ℕ) :
    Tendsto (fun n : ℕ => fixedPointPMF n j) atTop
      (𝓝 (ProbabilityTheory.poissonPMFReal (1 : ℝ≥0) j)) := by
  convert fixedPointPMF_tendsto j using 1
  simp [ProbabilityTheory.poissonPMFReal, div_eq_mul_inv]

end FixedPointsPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
