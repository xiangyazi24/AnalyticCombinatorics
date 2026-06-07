import Mathlib

/-!
# R7 Fact B via Doeblin: the tail band (sup/inf over a rank tail)

For a bounded `h` and a rank map `rank → atTop`, the *tail band* at level `R` is `[d R, D R]` where
`D R = sSup (h '' {k | rank k ≥ R})` and `d R = sInf (…)`.  Its width `V R = D R − d R` is the tail
oscillation: antitone in `R`, nonnegative, `≤ 2M`, and dominates every pairwise difference
`|h i − h j|` with `rank i, rank j ≥ R`.  Every `h k` with `rank k ≥ R` lies in `[d R, d R + V R]`.
This supplies the `lo = d`, `W = V` band and the oscillation dominator for the Doeblin escape
contraction.  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The rank tail `{k | R ≤ rank k}`. -/
def tailSet (rank : ℕ → ℕ) (R : ℕ) : Set ℕ := {k | R ≤ rank k}

/-- Tail supremum of `h` over `{rank ≥ R}`. -/
def tailSup (h : ℕ → ℝ) (rank : ℕ → ℕ) (R : ℕ) : ℝ := sSup (h '' tailSet rank R)

/-- Tail infimum of `h` over `{rank ≥ R}`. -/
def tailInf (h : ℕ → ℝ) (rank : ℕ → ℕ) (R : ℕ) : ℝ := sInf (h '' tailSet rank R)

/-- Tail oscillation (band width). -/
def tailOsc (h : ℕ → ℝ) (rank : ℕ → ℕ) (R : ℕ) : ℝ := tailSup h rank R - tailInf h rank R

variable {h : ℕ → ℝ} {rank : ℕ → ℕ} {M : ℝ}

lemma tailSet_nonempty (hrank : Tendsto rank atTop atTop) (R : ℕ) :
    (h '' tailSet rank R).Nonempty := by
  obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.1 hrank) R
  exact ⟨h N, N, hN N le_rfl, rfl⟩

lemma tail_bddAbove (hM : ∀ n, |h n| ≤ M) (R : ℕ) : BddAbove (h '' tailSet rank R) :=
  ⟨M, by rintro _ ⟨k, _, rfl⟩; exact le_trans (le_abs_self _) (hM k)⟩

lemma tail_bddBelow (hM : ∀ n, |h n| ≤ M) (R : ℕ) : BddBelow (h '' tailSet rank R) :=
  ⟨-M, by rintro _ ⟨k, _, rfl⟩; exact le_trans (neg_le_neg (hM k)) (neg_abs_le _)⟩

/-- Every tail value sits between `d R` and `D R`. -/
lemma tail_band (hM : ∀ n, |h n| ≤ M) {R k : ℕ} (hk : R ≤ rank k) :
    tailInf h rank R ≤ h k ∧ h k ≤ tailSup h rank R := by
  have hmem : h k ∈ h '' tailSet rank R := ⟨k, hk, rfl⟩
  exact ⟨csInf_le (tail_bddBelow hM R) hmem, le_csSup (tail_bddAbove hM R) hmem⟩

/-- `|h i − h j| ≤ V R` for both ranks `≥ R`. -/
lemma tailOsc_abs_le (hM : ∀ n, |h n| ≤ M) {R i j : ℕ}
    (hi : R ≤ rank i) (hj : R ≤ rank j) : |h i - h j| ≤ tailOsc h rank R := by
  rw [tailOsc, abs_le]
  obtain ⟨hil, hiu⟩ := tail_band (rank := rank) hM hi
  obtain ⟨hjl, hju⟩ := tail_band (rank := rank) hM hj
  constructor <;> linarith

lemma tailOsc_nonneg (hrank : Tendsto rank atTop atTop) (hM : ∀ n, |h n| ≤ M) (R : ℕ) :
    0 ≤ tailOsc h rank R := by
  obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.1 hrank) R
  have := tailOsc_abs_le (rank := rank) hM (i := N) (j := N) (hN N le_rfl) (hN N le_rfl)
  simpa using (abs_nonneg _).trans this

lemma tailOsc_le_two_M (hrank : Tendsto rank atTop atTop) (hM : ∀ n, |h n| ≤ M) (R : ℕ) :
    tailOsc h rank R ≤ 2 * M := by
  have hsup : tailSup h rank R ≤ M :=
    csSup_le (tailSet_nonempty (h := h) hrank R)
      (by rintro _ ⟨k, _, rfl⟩; exact le_trans (le_abs_self _) (hM k))
  have hinf : -M ≤ tailInf h rank R :=
    le_csInf (tailSet_nonempty (h := h) hrank R)
      (by rintro _ ⟨k, _, rfl⟩; exact le_trans (neg_le_neg (hM k)) (neg_abs_le _))
  rw [tailOsc]; linarith

lemma tailInf_abs_le (hrank : Tendsto rank atTop atTop) (hM : ∀ n, |h n| ≤ M) (R : ℕ) :
    |tailInf h rank R| ≤ M := by
  rw [abs_le]
  have hinf_ge : -M ≤ tailInf h rank R :=
    le_csInf (tailSet_nonempty (h := h) hrank R)
      (by rintro _ ⟨k, _, rfl⟩; exact le_trans (neg_le_neg (hM k)) (neg_abs_le _))
  have hinf_le : tailInf h rank R ≤ M := by
    obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.1 hrank) R
    exact le_trans (csInf_le (tail_bddBelow hM R) ⟨N, hN N le_rfl, rfl⟩)
      (le_trans (le_abs_self _) (hM N))
  exact ⟨hinf_ge, hinf_le⟩

/-- `V` is antitone: a deeper tail has larger oscillation. -/
lemma tailOsc_antitone (hrank : Tendsto rank atTop atTop) (hM : ∀ n, |h n| ≤ M)
    {R R' : ℕ} (hRR : R ≤ R') : tailOsc h rank R' ≤ tailOsc h rank R := by
  have himg : h '' tailSet rank R' ⊆ h '' tailSet rank R :=
    Set.image_mono (fun k hk => le_trans hRR hk)
  have hne' : (h '' tailSet rank R').Nonempty := tailSet_nonempty (h := h) hrank R'
  have hsup : tailSup h rank R' ≤ tailSup h rank R :=
    csSup_le_csSup (tail_bddAbove hM R) hne' himg
  have hinf : tailInf h rank R ≤ tailInf h rank R' :=
    csInf_le_csInf (tail_bddBelow hM R) hne' himg
  rw [tailOsc, tailOsc]; linarith

/-- Upper bound on the tail oscillation from a uniform pairwise bound. -/
lemma tailOsc_le_of_pairwise (hrank : Tendsto rank atTop atTop) {R : ℕ} {X : ℝ}
    (hpair : ∀ i j, R ≤ rank i → R ≤ rank j → h i - h j ≤ X) :
    tailOsc h rank R ≤ X := by
  have hne := tailSet_nonempty (h := h) hrank R
  have key : tailSup h rank R ≤ X + tailInf h rank R := by
    rw [tailSup]
    refine csSup_le hne ?_
    rintro _ ⟨i, hi, rfl⟩
    have hiR : R ≤ rank i := hi
    have hle : h i - X ≤ tailInf h rank R := by
      rw [tailInf]
      refine le_csInf hne ?_
      rintro _ ⟨j, hj, rfl⟩
      have hjR : R ≤ rank j := hj
      linarith [hpair i j hiR hjR]
    linarith
  rw [tailOsc]; linarith

end AnalyticCombinatorics.Ch8.Partitions.Erdos
