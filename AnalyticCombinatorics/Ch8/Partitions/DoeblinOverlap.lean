import Mathlib

/-!
# R7 Fact B via Doeblin (File A): the deterministic overlap-contraction inequality

ChatGPT's recommended route to Fact B replaces entrance-distribution convergence by a finite-time
Doeblin oscillation contraction.  Its deterministic keystone is: if two probability vectors `p, q`
share a common mass `≥ δ` (overlap), then their averages of any function `f` of oscillation `≤ W`
differ by at most `(1 − δ)·W`.  This is pure nonnegative-sequence analysis — no probability theory.
Opus-authored.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Two sub-probability vectors of equal mass `m`, averaging a function valued in `[lo, lo+W]`,
differ by at most `m·W`. -/
lemma subprob_avg_diff {s : Finset ℕ} {a b f : ℕ → ℝ} {m lo W : ℝ}
    (ha : ∀ k ∈ s, 0 ≤ a k) (hb : ∀ k ∈ s, 0 ≤ b k)
    (ham : ∑ k ∈ s, a k = m) (hbm : ∑ k ∈ s, b k = m)
    (hf : ∀ k ∈ s, lo ≤ f k ∧ f k ≤ lo + W) :
    |∑ k ∈ s, a k * f k - ∑ k ∈ s, b k * f k| ≤ m * W := by
  have hshift : ∀ g : ℕ → ℝ, ∑ k ∈ s, g k = m →
      ∑ k ∈ s, g k * f k = ∑ k ∈ s, g k * (f k - lo) + m * lo := by
    intro g hg
    rw [Finset.sum_congr rfl (fun k _ => by ring : ∀ k ∈ s, g k * f k = g k * (f k - lo) + g k * lo),
      Finset.sum_add_distrib, ← Finset.sum_mul, hg]
  rw [hshift a ham, hshift b hbm]
  have hAlo : 0 ≤ ∑ k ∈ s, a k * (f k - lo) :=
    Finset.sum_nonneg (fun k hk => mul_nonneg (ha k hk) (by linarith [(hf k hk).1]))
  have hAhi : ∑ k ∈ s, a k * (f k - lo) ≤ m * W := by
    rw [← ham, Finset.sum_mul]
    exact Finset.sum_le_sum (fun k hk =>
      mul_le_mul_of_nonneg_left (by linarith [(hf k hk).2]) (ha k hk))
  have hBlo : 0 ≤ ∑ k ∈ s, b k * (f k - lo) :=
    Finset.sum_nonneg (fun k hk => mul_nonneg (hb k hk) (by linarith [(hf k hk).1]))
  have hBhi : ∑ k ∈ s, b k * (f k - lo) ≤ m * W := by
    rw [← hbm, Finset.sum_mul]
    exact Finset.sum_le_sum (fun k hk =>
      mul_le_mul_of_nonneg_left (by linarith [(hf k hk).2]) (hb k hk))
  rw [show (∑ k ∈ s, a k * (f k - lo) + m * lo) - (∑ k ∈ s, b k * (f k - lo) + m * lo)
      = (∑ k ∈ s, a k * (f k - lo)) - (∑ k ∈ s, b k * (f k - lo)) by ring]
  rw [abs_le]
  constructor <;> linarith

/-- **Doeblin averaging contraction.** Probability vectors `p, q` with overlap `≥ δ`, averaging a
function `f` valued in `[lo, lo+W]`, differ by at most `(1−δ)·W`. -/
lemma doeblin_average_diff_bound {s : Finset ℕ} {p q f : ℕ → ℝ} {δ lo W : ℝ}
    (hpm : ∑ k ∈ s, p k = 1) (hqm : ∑ k ∈ s, q k = 1)
    (hov : δ ≤ ∑ k ∈ s, min (p k) (q k))
    (hf : ∀ k ∈ s, lo ≤ f k ∧ f k ≤ lo + W) (hW : 0 ≤ W) :
    |∑ k ∈ s, p k * f k - ∑ k ∈ s, q k * f k| ≤ (1 - δ) * W := by
  set r : ℕ → ℝ := fun k => min (p k) (q k) with hr
  set m : ℝ := 1 - ∑ k ∈ s, r k with hm
  have hra : ∀ k ∈ s, 0 ≤ p k - r k := fun k _ => by simp only [hr]; linarith [min_le_left (p k) (q k)]
  have hrb : ∀ k ∈ s, 0 ≤ q k - r k := fun k _ => by simp only [hr]; linarith [min_le_right (p k) (q k)]
  have hma : ∑ k ∈ s, (p k - r k) = m := by rw [Finset.sum_sub_distrib, hpm, hm]
  have hmb : ∑ k ∈ s, (q k - r k) = m := by rw [Finset.sum_sub_distrib, hqm, hm]
  have hcancel : ∑ k ∈ s, p k * f k - ∑ k ∈ s, q k * f k
      = ∑ k ∈ s, (p k - r k) * f k - ∑ k ∈ s, (q k - r k) * f k := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  rw [hcancel]
  have hkey := subprob_avg_diff hra hrb hma hmb hf
  have hmle : m ≤ 1 - δ := by rw [hm]; linarith [hov]
  calc |∑ k ∈ s, (p k - r k) * f k - ∑ k ∈ s, (q k - r k) * f k| ≤ m * W := hkey
    _ ≤ (1 - δ) * W := mul_le_mul_of_nonneg_right hmle hW

end AnalyticCombinatorics.Ch8.Partitions.Erdos
