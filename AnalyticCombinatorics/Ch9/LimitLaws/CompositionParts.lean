import Mathlib
import AnalyticCombinatorics.Ch9.LimitLaws.QuasiPowers
import AnalyticCombinatorics.Ch9.LimitLaws.BinaryWordCLT

/-!
# Number of parts in a random composition

For `n ≥ 1`, a composition of `n` with `k` parts is equivalently a choice of
`k - 1` of the `n - 1` interior gaps.  Thus the part count has the same law as
`1 + Binomial(n - 1, 1 / 2)`.

The central limit theorem is proved by reusing the local quasi-powers
instantiation for binary words from `BinaryWordCLT.lean`, shifted from `n` to
`n - 1` and then translated by the deterministic `+1`.
-/

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory

open scoped Topology

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws

/-- Compositions of `n` having exactly `k` parts. -/
def CompositionsWithParts (n k : ℕ) :=
  { c : Composition n // c.length = k }

instance instFintypeCompositionsWithParts (n k : ℕ) :
    Fintype (CompositionsWithParts n k) := by
  classical
  unfold CompositionsWithParts
  infer_instance

private lemma compositionAsSetEquiv_symm_length (n : ℕ) (h : 0 < n)
    (s : Finset (Fin (n - 1))) :
    (((compositionAsSetEquiv n).symm s).length) = s.card + 1 := by
  let e : Fin (n - 1) ↪ Fin (n + 1) :=
    ⟨fun j => ⟨(j : ℕ) + 1, by omega⟩, by
      intro a b hab
      ext
      have := congrArg (fun x : Fin (n + 1) => (x : ℕ)) hab
      simp at this
      omega⟩
  let p : Fin (n + 1) → Prop :=
    fun i => i = 0 ∨ i = Fin.last n ∨ ∃ j ∈ s, (i : ℕ) = (j : ℕ) + 1
  have hset : (Finset.univ.filter p) = insert 0 (insert (Fin.last n) (s.map e)) := by
    ext i
    constructor
    · intro hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, p] at hi
      rcases hi with h0 | hlast | ⟨j, hj, hval⟩
      · simp [h0]
      · simp [hlast]
      · rw [Finset.mem_insert, Finset.mem_insert]
        right
        right
        exact Finset.mem_map.mpr ⟨j, hj, by
          ext
          simp [e, hval]⟩
    · intro hi
      rw [Finset.mem_insert, Finset.mem_insert] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, p]
      rcases hi with h0 | hlast | himage
      · exact Or.inl h0
      · exact Or.inr (Or.inl hlast)
      · rcases Finset.mem_map.mp himage with ⟨j, hj, hji⟩
        exact Or.inr (Or.inr ⟨j, hj, by
          have := congrArg (fun x : Fin (n + 1) => (x : ℕ)) hji.symm
          simpa [e] using this⟩)
  have hlast_ne_zero : (Fin.last n : Fin (n + 1)) ≠ 0 := by
    intro hz
    have := congrArg (fun x : Fin (n + 1) => (x : ℕ)) hz
    simp at this
    omega
  have hzero_not_map : (0 : Fin (n + 1)) ∉ s.map e := by
    intro hi
    rcases Finset.mem_map.mp hi with ⟨j, _hj, hj_eq⟩
    have := congrArg (fun x : Fin (n + 1) => (x : ℕ)) hj_eq
    simp [e] at this
  have hlast_not_map : (Fin.last n : Fin (n + 1)) ∉ s.map e := by
    intro hi
    rcases Finset.mem_map.mp hi with ⟨j, _hj, hj_eq⟩
    have hjlt : (j : ℕ) < n - 1 := j.2
    have hv : (j : ℕ) + 1 = n := by
      have := congrArg (fun x : Fin (n + 1) => (x : ℕ)) hj_eq
      simpa [e] using this
    omega
  have hzero_not_insert : (0 : Fin (n + 1)) ∉ insert (Fin.last n) (s.map e) := by
    simp [Ne.symm hlast_ne_zero, hzero_not_map]
  simp [compositionAsSetEquiv, CompositionAsSet.length]
  change (Finset.univ.filter p).card = s.card + 2
  rw [hset]
  rw [Finset.card_insert_of_notMem hzero_not_insert]
  rw [Finset.card_insert_of_notMem hlast_not_map]
  simp

private lemma compositionEquiv_symm_length (n : ℕ) (h : 0 < n)
    (s : Finset (Fin (n - 1))) :
    (((compositionEquiv n).symm ((compositionAsSetEquiv n).symm s)).length) =
      s.card + 1 := by
  simpa [compositionEquiv] using compositionAsSetEquiv_symm_length n h s

/--
The genuine gap-counting bridge: compositions of `n ≥ 1` with `k ≥ 1` parts
are counted by choosing `k - 1` of the `n - 1` interior gaps.
-/
theorem card_compositionsWithParts_eq_choose (n k : ℕ) (hn : 0 < n) (hk : 1 ≤ k) :
    Fintype.card (CompositionsWithParts n k) = Nat.choose (n - 1) (k - 1) := by
  classical
  change Fintype.card { c : Composition n // c.length = k } =
    Nat.choose (n - 1) (k - 1)
  let eComp : Composition n ≃ Finset (Fin (n - 1)) :=
    (compositionEquiv n).trans (compositionAsSetEquiv n)
  have hiff :
      ∀ c : Composition n, c.length = k ↔ (eComp c).card = k - 1 := by
    intro c
    have hlen : c.length = (eComp c).card + 1 := by
      simpa [eComp] using compositionEquiv_symm_length n hn (eComp c)
    constructor
    · intro hc
      omega
    · intro hs
      omega
  calc
    Fintype.card { c : Composition n // c.length = k }
        = Fintype.card { s : Finset (Fin (n - 1)) // s.card = k - 1 } := by
          exact Fintype.card_congr (eComp.subtypeEquiv hiff)
    _ = Nat.choose (n - 1) (k - 1) := by
          simp

/-- The binomial `p = 1 / 2` probability mass function, written as a real number. -/
def binomialHalfPMF (m j : ℕ) : ℝ :=
  (Nat.choose m j : ℝ) / (2 : ℝ) ^ m

/--
Under the uniform distribution on all compositions of `n`, the mass of the
event "exactly `k` parts" is the corresponding binomial-half mass.
-/
theorem uniform_composition_part_mass_eq_binomialHalfPMF (n k : ℕ)
    (hn : 0 < n) (hk : 1 ≤ k) :
    (Fintype.card (CompositionsWithParts n k) : ℝ) /
        (Fintype.card (Composition n) : ℝ) =
      binomialHalfPMF (n - 1) (k - 1) := by
  rw [card_compositionsWithParts_eq_choose n k hn hk, composition_card]
  simp [binomialHalfPMF]

/-- Binary gap space for a composition of `n`, with `n - 1` interior gaps. -/
abbrev CompositionGapΩ (n : ℕ) := Ω (n - 1)

/-- Product measure for independent fair choices of the `n - 1` gaps. -/
def compositionGapP (n : ℕ) : Measure (CompositionGapΩ n) :=
  P (n - 1)

instance compositionGapP_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (compositionGapP n) := by
  unfold compositionGapP
  infer_instance

/-- The quasi-powers size parameter for compositions, namely `n - 1`. -/
def compositionBeta (n : ℕ) : ℝ :=
  ((n - 1 : ℕ) : ℝ)

/-- Sum of sign-coded selected gaps. -/
def compositionSignSum (n : ℕ) (ω : CompositionGapΩ n) : ℝ :=
  S (n - 1) ω

/-- Number of selected gaps in the sign-coded model. -/
def compositionGapCount (n : ℕ) (ω : CompositionGapΩ n) : ℝ :=
  X (n - 1) ω

/-- Number of parts: one plus the number of selected interior gaps. -/
def compositionParts (n : ℕ) (ω : CompositionGapΩ n) : ℝ :=
  1 + compositionGapCount n ω

/-- The shifted logarithmic remainder inherited from binary words. -/
def compositionSignR (n : ℕ) (z : ℂ) : ℂ :=
  signR (n - 1) z

lemma compositionBeta_tendsto_atTop :
    Tendsto compositionBeta atTop atTop := by
  simpa [compositionBeta] using
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_sub_atTop_nat 1)

lemma composition_sign_hChar : ∃ s₀ > 0, ∀ n s, |s| ≤ s₀ →
    charFun ((compositionGapP n).map (compositionSignSum n)) s =
      Complex.exp ((compositionBeta n : ℂ) * (((0 : ℝ) : ℂ) * (Complex.I * (s : ℂ)) +
        ((1 : ℝ) : ℂ) * (Complex.I * (s : ℂ)) ^ 2 / 2 +
        compositionSignR n (Complex.I * (s : ℂ))) + (0 : ℂ)) := by
  obtain ⟨s₀, hs₀, hlocal⟩ := sign_hChar
  refine ⟨s₀, hs₀, ?_⟩
  intro n s hs
  simpa [compositionGapP, compositionSignSum, compositionBeta, compositionSignR] using
    hlocal (n - 1) s hs

lemma compositionSignR_tendsto :
    ∀ t, Tendsto
      (fun n : ℕ =>
        (compositionBeta n : ℂ) *
          compositionSignR n (qpZ compositionBeta 1 n t))
      atTop (𝓝 0) := by
  intro t
  simpa [compositionBeta, compositionSignR, qpZ] using
    (signR_tendsto t).comp (tendsto_sub_atTop_nat 1)

theorem composition_signSum_tendstoInDistribution_gaussian :
    TendstoInDistribution
      (fun n ω =>
        (compositionSignSum n ω - compositionBeta n * 0) /
          Real.sqrt (compositionBeta n * 1)) atTop
      (fun x : ℝ => x) compositionGapP (gaussianReal 0 1) :=
  quasiPowers_tendstoInDistribution_of_continuousAt
    (P := compositionGapP) (X := compositionSignSum)
    (β := compositionBeta) (u₁ := 0) (u₂ := 1)
    (R := compositionSignR) (V := fun _ : ℂ => 0)
    (by
      intro n
      unfold compositionSignSum
      exact Finset.aemeasurable_fun_sum _ fun i _ => (measurable_pi_apply i).aemeasurable)
    compositionBeta_tendsto_atTop
    (by norm_num)
    continuousAt_const
    rfl
    composition_sign_hChar
    compositionSignR_tendsto

lemma normalized_compositionParts_eq_sign (n : ℕ) (ω : CompositionGapΩ n) :
    (compositionParts n ω - ((n : ℝ) + 1) / 2) /
        Real.sqrt (((n - 1 : ℕ) : ℝ) / 4) =
      (compositionSignSum n ω - compositionBeta n * 0) /
        Real.sqrt (compositionBeta n * 1) := by
  by_cases hn : n = 0
  · subst n
    simp [compositionParts, compositionGapCount, compositionSignSum, compositionBeta, X, S]
  · have hn_real : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
      have hn_nat : n = (n - 1) + 1 := by omega
      rw [hn_nat]
      norm_num
    have hcenter :
        ((n : ℝ) + 1) / 2 =
          1 + ((n - 1 : ℕ) : ℝ) * (1 / 2) := by
      rw [hn_real]
      ring
    rw [show compositionParts n ω - ((n : ℝ) + 1) / 2 =
        X (n - 1) ω - ((n - 1 : ℕ) : ℝ) * (1 / 2) by
      simp [compositionParts, compositionGapCount, hcenter]
      ]
    rw [show Real.sqrt (((n - 1 : ℕ) : ℝ) / 4) =
        Real.sqrt (((n - 1 : ℕ) : ℝ) * (1 / 4)) by ring_nf]
    simpa [compositionSignSum, compositionBeta] using normalized_count_eq_sign (n - 1) ω

/--
Among uniformly random compositions of `n ≥ 1`, the number of parts is
asymptotically Gaussian after centering by `(n + 1) / 2` and scaling by
`sqrt ((n - 1) / 4)`.
-/
theorem compositionParts_tendstoInDistribution_gaussian :
    TendstoInDistribution
      (fun n ω =>
        (compositionParts n ω - ((n : ℝ) + 1) / 2) /
          Real.sqrt (((n - 1 : ℕ) : ℝ) / 4)) atTop
      (fun x : ℝ => x) compositionGapP (gaussianReal 0 1) := by
  refine TendstoInDistribution.congr ?_ (ae_of_all _ fun _ => rfl)
    composition_signSum_tendstoInDistribution_gaussian
  intro n
  exact ae_of_all _ fun ω => (normalized_compositionParts_eq_sign n ω).symm

end LimitLaws
end Ch9
end AnalyticCombinatorics
