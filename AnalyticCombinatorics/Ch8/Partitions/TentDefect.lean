import AnalyticCombinatorics.Ch8.Partitions.QVTelescope

/-!
# The tent / defect function `Φ_W(d) = max(|d| − W, 0)` (renewal route B primitives)

The fixed-window Tanaka-DEFECT route to the renewal limit uses `Φ_W(d) = max(|d| − W, 0)`: it counts
window crossings robustly to the soft far jumps that break the plain window-occupation local time
(route A is dead — fixed-`b` truncation removes constant mass; see `DOCTRINE-walls.md`).

This file banks the certain primitives:
* `tentW_nonneg`, `tentW_ge` (`Φ_W d ≥ |d| − W`, the PZ-transfer with a `−W` loss),
* `tentW_le_abs`, `tentW_lipschitz`,
* `expected_tentW_ge` (`E[Φ_W(D)] ≥ E|D| − W`), turning the banked `E|D_T| ≥ c√T` into growth of the
  defect potential.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι]

/-- The tent/defect function `Φ_W(d) = max(|d| − W, 0)`. -/
def tentW (W : ℝ) (d : ℝ) : ℝ := max (|d| - W) 0

@[simp] lemma tentW_nonneg (W d : ℝ) : 0 ≤ tentW W d := le_max_right _ _

/-- The PZ-transfer inequality: `Φ_W d ≥ |d| − W`. -/
lemma tentW_ge (W d : ℝ) : |d| - W ≤ tentW W d := le_max_left _ _

/-- `Φ_W d ≤ |d|` (for `W ≥ 0`). -/
lemma tentW_le_abs {W : ℝ} (hW : 0 ≤ W) (d : ℝ) : tentW W d ≤ |d| := by
  unfold tentW
  rcases le_total (|d| - W) 0 with h | h
  · rw [max_eq_right h]; exact abs_nonneg d
  · rw [max_eq_left h]; linarith

/-- `max u 0 = (u + |u|)/2`. -/
private lemma max_zero_eq (u : ℝ) : max u 0 = (u + |u|) / 2 := by
  rcases le_total u 0 with h | h
  · rw [max_eq_right h, abs_of_nonpos h]; ring
  · rw [max_eq_left h, abs_of_nonneg h]; ring

/-- `max · 0` is `1`-Lipschitz. -/
private lemma abs_max_zero_sub_le (u v : ℝ) : |max u 0 - max v 0| ≤ |u - v| := by
  rw [max_zero_eq, max_zero_eq,
    show (u + |u|) / 2 - (v + |v|) / 2 = ((u - v) + (|u| - |v|)) / 2 by ring]
  have h1 : |(u - v) + (|u| - |v|)| ≤ |u - v| + |(|u| - |v|)| := abs_add_le _ _
  have h2 : |(|u| - |v|)| ≤ |u - v| := abs_abs_sub_abs_le_abs_sub u v
  rw [abs_div, show |(2 : ℝ)| = 2 by norm_num]
  linarith

/-- `Φ_W` is `1`-Lipschitz. -/
lemma tentW_lipschitz (W a b : ℝ) : |tentW W a - tentW W b| ≤ |a - b| := by
  unfold tentW
  calc |max (|a| - W) 0 - max (|b| - W) 0|
      ≤ |(|a| - W) - (|b| - W)| := abs_max_zero_sub_le _ _
    _ = |(|a| - |b|)| := by rw [show (|a| - W) - (|b| - W) = |a| - |b| by ring]
    _ ≤ |a - b| := abs_abs_sub_abs_le_abs_sub a b

/-- The defect potential lower-bounds the mean modulus (with a `−W` loss):
`E[Φ_W(D)] ≥ E|D| − W` for a probability vector. -/
lemma expected_tentW_ge (W : ℝ) (D : ι → ℝ) (μ : ι → ℝ)
    (hμsum : ∑ x, μ x = 1) (hμnn : ∀ x, 0 ≤ μ x) :
    (∑ x, μ x * |D x|) - W ≤ ∑ x, μ x * tentW W (D x) := by
  have hstep : (∑ x, μ x * (|D x| - W)) = (∑ x, μ x * |D x|) - W := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hμsum, one_mul]
  rw [← hstep]
  exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (tentW_ge W (D x)) (hμnn x))

end AnalyticCombinatorics.Ch8.Partitions.Erdos
