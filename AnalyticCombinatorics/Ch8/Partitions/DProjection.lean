import AnalyticCombinatorics.Ch8.Partitions.SectorBound

/-!
# Weak `D`-projection of a pair walk onto an integer observable

The renewal sector route is a statement about the *pair* walk `KhatResPair` on states `α × α` with the
integer observable `D (x,y) = rnk x − rnk y`.  The pair walk is **not** lumpable w.r.t. `D` (it is not
a Markov function of `D`), so we cannot reduce it to a 1-D Markov chain.  But the *Dirichlet form*
pulls back: with the reference-weighted `D`-pushforward `πD` and the `D`-projected kernel `KD`, the
pair pullback form `pairAK` equals the 1-D form `aK πD KD`.  That lets the banked 1-D sector machinery
(`aK`, `aAnti`, `Jflow`, `divJ`, `Hcut`, `crossingTV`, `sector_bound_from_Hcut_on`,
`sector_bound_with_divergence_on`) apply verbatim, with no fragile pair-state Hardy reproof.

This file builds the projection **core** (generic over a state type `S` with observable `D : S → ℤ`):
the measures `πD`/`massD`/`KD`, the weighted identity `πD·KD = massD`, and the first fiber-regrouping
lemma `sum_over_D_fibers`.  (The full projection equality `pairAK = aK πD KD` builds on these.)

Reference: ChatGPT-Pro R18 chose this weak-projection route over a fresh pair-state reproof (Layer A of
the roadmap in `HANDOFF/DOCTRINE-walls.md`).
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos.DProject

variable {S : Type*}

/-- The pair window: states whose observable `D` lands in `Icc a b`. -/
def ΩD (Ω : Finset S) (D : S → ℤ) (a b : ℤ) : Finset S :=
  Ω.filter (fun s => D s ∈ Finset.Icc a b)

/-- `D`-pushforward of the reference measure: total `π`-mass on the fiber `{D = d}`. -/
def πD (Ω : Finset S) (π : S → ℝ) (D : S → ℤ) (d : ℤ) : ℝ :=
  ∑ s ∈ Ω, if D s = d then π s else 0

/-- Total reference-weighted transition mass from fiber `d` to fiber `d'`. -/
def massD (Ω : Finset S) (π : S → ℝ) (K : S → S → ℝ) (D : S → ℤ) (d d' : ℤ) : ℝ :=
  ∑ s ∈ Ω, ∑ t ∈ Ω, if D s = d ∧ D t = d' then π s * K s t else 0

/-- The `D`-projected kernel: `massD d d' / πD d` (zero when the fiber is empty/massless). -/
def KD (Ω : Finset S) (π : S → ℝ) (K : S → S → ℝ) (D : S → ℤ) (d d' : ℤ) : ℝ :=
  if πD Ω π D d = 0 then 0 else massD Ω π K D d d' / πD Ω π D d

/-- **Weighted identity** `πD d · KD d d' = massD d d'`.  On the empty fiber both sides are `0`
(using `π ≥ 0` to force `massD = 0` there). -/
lemma πD_mul_KD_eq_massD {Ω : Finset S} {π : S → ℝ} {K : S → S → ℝ} {D : S → ℤ} {d d' : ℤ}
    (hπnn : ∀ s ∈ Ω, 0 ≤ π s) :
    πD Ω π D d * KD Ω π K D d d' = massD Ω π K D d d' := by
  classical
  unfold KD
  by_cases h : πD Ω π D d = 0
  · rw [if_pos h, mul_zero]
    -- every fiber term of πD is 0, so π s = 0 whenever D s = d, hence massD = 0
    have hterm : ∀ s ∈ Ω, (if D s = d then π s else 0) = 0 := by
      have hnn : ∀ s ∈ Ω, 0 ≤ (if D s = d then π s else 0) := by
        intro s hs; split
        · exact hπnn s hs
        · exact le_refl 0
      exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h
    symm
    unfold massD
    apply Finset.sum_eq_zero
    intro s hs
    apply Finset.sum_eq_zero
    intro t _
    by_cases hc : D s = d ∧ D t = d'
    · rw [if_pos hc]
      have hzs : (if D s = d then π s else 0) = 0 := hterm s hs
      rw [if_pos hc.1] at hzs
      rw [hzs, zero_mul]
    · rw [if_neg hc]
  · rw [if_neg h, mul_div_cancel₀ _ h]

/-- **Fiber regrouping** for a single observable: `∑_{d∈I} πD d · φ d = ∑_{s∈Ω} π s · φ (D s)`,
provided every state's observable lands in `I`. -/
lemma sum_over_D_fibers {Ω : Finset S} {π : S → ℝ} {D : S → ℤ} {I : Finset ℤ}
    (hΩD : ∀ s ∈ Ω, D s ∈ I) (φ : ℤ → ℝ) :
    (∑ d ∈ I, πD Ω π D d * φ d) = ∑ s ∈ Ω, π s * φ (D s) := by
  classical
  simp_rw [πD, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  have hpush : ∀ d, (if D s = d then π s else 0) * φ d = if D s = d then π s * φ d else 0 := by
    intro d; split <;> simp
  simp_rw [hpush]
  rw [Finset.sum_ite_eq I (D s) (fun d => π s * φ d), if_pos (hΩD s hs)]

end AnalyticCombinatorics.Ch8.Partitions.Erdos.DProject
