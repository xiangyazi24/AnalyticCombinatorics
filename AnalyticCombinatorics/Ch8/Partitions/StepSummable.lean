import Mathlib

/-!
# R7 Fact B via Doeblin: summability from a `B`-step geometric contraction

If `f ≥ 0` and `f(n+B) ≤ q·f(n)` with `0 ≤ q < 1`, then `f` is summable.  Clean proof via uniformly
bounded partial sums: splitting `∑_{range m} f` at `B` and applying the step bound gives
`S_m ≤ S_B + q·S_m`, hence `S_m ≤ S_B/(1−q)`.  No floor/rpow needed.  This converts the tail-sup
block-oscillation contraction `V(R) ≤ (1−δ)·V(R−B)` into `Summable V` for the §9 convergence engine.
Opus-authored.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

lemma summable_of_step_le {f : ℕ → ℝ} {q : ℝ} {B : ℕ}
    (hf : ∀ n, 0 ≤ f n) (hq1 : q < 1) (hq0 : 0 ≤ q)
    (hstep : ∀ n, f (n + B) ≤ q * f n) :
    Summable f := by
  have hmono : Monotone (fun m => ∑ i ∈ Finset.range m, f i) := by
    intro a b hab
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun i hi => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hab))
      (fun i _ _ => hf i)
  have hkey : ∀ m, (∑ i ∈ Finset.range m, f i)
      ≤ (∑ i ∈ Finset.range B, f i) + q * ∑ i ∈ Finset.range m, f i := by
    intro m
    rcases le_or_gt m B with hmB | hmB
    · have h1 : (∑ i ∈ Finset.range m, f i) ≤ ∑ i ∈ Finset.range B, f i := hmono hmB
      have h2 : 0 ≤ q * ∑ i ∈ Finset.range m, f i :=
        mul_nonneg hq0 (Finset.sum_nonneg (fun i _ => hf i))
      linarith
    · obtain ⟨d, rfl⟩ : ∃ d, m = B + d := ⟨m - B, by omega⟩
      have hadd : (∑ i ∈ Finset.range (B + d), f i)
          = (∑ i ∈ Finset.range B, f i) + ∑ i ∈ Finset.range d, f (B + i) :=
        Finset.sum_range_add f B d
      have hstep_sum : ∑ i ∈ Finset.range d, f (B + i) ≤ q * ∑ i ∈ Finset.range d, f i := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun i _ => by rw [add_comm B i]; exact hstep i)
      have hdle : (∑ i ∈ Finset.range d, f i) ≤ ∑ i ∈ Finset.range (B + d), f i :=
        hmono (by omega)
      rw [hadd] at hdle ⊢
      nlinarith [hstep_sum, hdle, hq0, mul_nonneg hq0 (sub_nonneg.mpr hdle)]
  apply summable_of_sum_range_le (c := (∑ i ∈ Finset.range B, f i) / (1 - q)) hf
  intro n
  rw [le_div_iff₀ (by linarith : (0:ℝ) < 1 - q)]
  nlinarith [hkey n]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
