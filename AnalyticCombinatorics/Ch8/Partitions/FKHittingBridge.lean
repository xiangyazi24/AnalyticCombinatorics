import AnalyticCombinatorics.Ch8.Partitions.FKBlockBridge

/-!
# Hitting-to-FK block drop

This file contains the finite-state algebraic corollary used by the concrete
block-drop task: if the free walk hits a drop set with uniformly positive
probability during a block, then the Feynman--Kac block weight has a uniform
drop.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {S : Type*} [Fintype S]

/-- Free-walk probability to hit `A` during one of the first `M` departure states. -/
def hitProb (Q : S → S → ℝ) (A : S → Prop) [DecidablePred A] : ℕ → S → ℝ
  | 0 => fun _ => 0
  | M + 1 => fun s => if A s then 1 else ∑ z, Q s z * hitProb Q A M z

lemma blockWeight_le_one {K : S → S → ℝ}
    (hKnn : ∀ s z, 0 ≤ K s z) (hrow : ∀ s, ∑ z, K s z ≤ 1) :
    ∀ M s, blockWeight K M s ≤ 1 := by
  intro M
  induction M with
  | zero =>
      intro s
      simp [blockWeight]
  | succ M ih =>
      intro s
      rw [blockWeight_succ]
      calc
        (∑ z, K s z * blockWeight K M z) ≤ ∑ z, K s z * 1 := by
          refine Finset.sum_le_sum ?_
          intro z _hz
          exact mul_le_mul_of_nonneg_left (ih z) (hKnn s z)
        _ = ∑ z, K s z := by simp
        _ ≤ 1 := hrow s

lemma hitProb_nonneg {Q : S → S → ℝ} {A : S → Prop} [DecidablePred A]
    (hQnn : ∀ s z, 0 ≤ Q s z) :
    ∀ M s, 0 ≤ hitProb Q A M s := by
  intro M
  induction M with
  | zero =>
      intro s
      simp [hitProb]
  | succ M ih =>
      intro s
      simp only [hitProb]
      split
      · norm_num
      · exact Finset.sum_nonneg fun z _ => mul_nonneg (hQnn s z) (ih z)

lemma hitProb_le_one {Q : S → S → ℝ} {A : S → Prop} [DecidablePred A]
    (hQnn : ∀ s z, 0 ≤ Q s z) (hQsum : ∀ s, ∑ z, Q s z = 1) :
    ∀ M s, hitProb Q A M s ≤ 1 := by
  intro M
  induction M with
  | zero =>
      intro s
      simp [hitProb]
  | succ M ih =>
      intro s
      simp only [hitProb]
      split
      · norm_num
      · calc
          (∑ z, Q s z * hitProb Q A M z) ≤ ∑ z, Q s z * 1 := by
            refine Finset.sum_le_sum ?_
            intro z _hz
            exact mul_le_mul_of_nonneg_left (ih z) (hQnn s z)
          _ = ∑ z, Q s z := by simp
          _ = 1 := hQsum s

lemma blockWeight_le_one_minus_delta_hitProb
    (Q : S → S → ℝ) (w : S → ℝ) (A : S → Prop) [DecidablePred A] (δ : ℝ)
    (hQnn : ∀ s z, 0 ≤ Q s z) (hQsum : ∀ s, ∑ z, Q s z = 1)
    (hw01 : ∀ s, 0 ≤ w s ∧ w s ≤ 1)
    (hdrop_on_A : ∀ s, A s → w s ≤ 1 - δ) :
    ∀ M s,
      blockWeight (weightedKernel Q w) M s ≤ 1 - δ * hitProb Q A M s := by
  let K := weightedKernel Q w
  have hKnn : ∀ s z, 0 ≤ K s z := weightedKernel_nonneg hQnn hw01
  have hrow : ∀ s, ∑ z, K s z ≤ 1 := weightedKernel_row_le_one hQsum hw01
  intro M
  induction M with
  | zero =>
      intro s
      simp [blockWeight, hitProb]
  | succ M ih =>
      intro s
      rw [blockWeight_succ]
      simp only [hitProb]
      by_cases hs : A s
      · simp only [if_pos hs]
        have hsum_le_one : (∑ z, Q s z * blockWeight K M z) ≤ 1 := by
          calc
            (∑ z, Q s z * blockWeight K M z) ≤ ∑ z, Q s z * 1 := by
              refine Finset.sum_le_sum ?_
              intro z _hz
              exact mul_le_mul_of_nonneg_left (blockWeight_le_one hKnn hrow M z) (hQnn s z)
            _ = ∑ z, Q s z := by simp
            _ = 1 := hQsum s
        have hfactor :
            (∑ z, K s z * blockWeight K M z) =
              w s * ∑ z, Q s z * blockWeight K M z := by
          dsimp [K, weightedKernel]
          simp_rw [mul_assoc]
          rw [← Finset.mul_sum]
        rw [hfactor]
        calc
          w s * (∑ z, Q s z * blockWeight K M z) ≤ w s * 1 :=
            mul_le_mul_of_nonneg_left hsum_le_one (hw01 s).1
          _ = w s := by ring
          _ ≤ 1 - δ := hdrop_on_A s hs
          _ = 1 - δ * 1 := by ring
      · simp only [if_neg hs]
        have hsum_nonneg : 0 ≤ ∑ z, Q s z * blockWeight K M z :=
          Finset.sum_nonneg fun z _ => mul_nonneg (hQnn s z) (blockWeight_nonneg' hKnn M z)
        have hfactor :
            (∑ z, K s z * blockWeight K M z) =
              w s * ∑ z, Q s z * blockWeight K M z := by
          dsimp [K, weightedKernel]
          simp_rw [mul_assoc]
          rw [← Finset.mul_sum]
        have hfree :
            (∑ z, Q s z * blockWeight K M z)
              ≤ ∑ z, Q s z * (1 - δ * hitProb Q A M z) := by
          refine Finset.sum_le_sum ?_
          intro z _hz
          exact mul_le_mul_of_nonneg_left (ih z) (hQnn s z)
        rw [hfactor]
        calc
          w s * (∑ z, Q s z * blockWeight K M z)
              ≤ 1 * (∑ z, Q s z * blockWeight K M z) :=
                mul_le_mul_of_nonneg_right (hw01 s).2 hsum_nonneg
          _ = ∑ z, Q s z * blockWeight K M z := by ring
          _ ≤ ∑ z, Q s z * (1 - δ * hitProb Q A M z) := hfree
          _ = 1 - δ * ∑ z, Q s z * hitProb Q A M z := by
            calc
              (∑ z, Q s z * (1 - δ * hitProb Q A M z))
                  = ∑ z, (Q s z - δ * (Q s z * hitProb Q A M z)) := by
                    refine Finset.sum_congr rfl ?_
                    intro z _hz
                    ring
              _ = (∑ z, Q s z) - δ * ∑ z, Q s z * hitProb Q A M z := by
                    rw [Finset.sum_sub_distrib, Finset.mul_sum]
              _ = 1 - δ * ∑ z, Q s z * hitProb Q A M z := by rw [hQsum s]

/-- A uniform free-walk hitting lower bound gives a uniform FK block drop. -/
theorem blockWeight_le_of_hitProb
    (Q : S → S → ℝ) (w : S → ℝ) (A : S → Prop) [DecidablePred A]
    (δ p0 : ℝ)
    (hQnn : ∀ s z, 0 ≤ Q s z) (hQsum : ∀ s, ∑ z, Q s z = 1)
    (hw01 : ∀ s, 0 ≤ w s ∧ w s ≤ 1)
    (hδ0 : 0 ≤ δ) (hdrop_on_A : ∀ s, A s → w s ≤ 1 - δ)
    (M : ℕ) (hhit : ∀ s, p0 ≤ hitProb Q A M s) :
    ∀ s, blockWeight (weightedKernel Q w) M s ≤ 1 - δ * p0 := by
  intro s
  calc
    blockWeight (weightedKernel Q w) M s ≤ 1 - δ * hitProb Q A M s :=
      blockWeight_le_one_minus_delta_hitProb Q w A δ hQnn hQsum hw01 hdrop_on_A M s
    _ ≤ 1 - δ * p0 := by
      exact sub_le_sub_left (mul_le_mul_of_nonneg_left (hhit s) hδ0) 1

#print axioms blockWeight_le_of_hitProb

end AnalyticCombinatorics.Ch8.Partitions.Erdos
