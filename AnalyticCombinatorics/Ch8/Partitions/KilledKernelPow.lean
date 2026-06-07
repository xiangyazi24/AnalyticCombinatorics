import Mathlib

/-!
# R7 Fact B via Doeblin (killed kernel): boundary-absorbing kernel powers

The killed kernel `P̃` (predecessor steps above the cutoff, identity-absorb on the boundary) has
support `k ≤ n` (predecessor OR diagonal), so its composition sums over `range (n+1)`.  This file
builds `KCompK`/`KPowK` and proves nonnegativity and the support `n < k → · = 0`.  The `L`-fold killed
power is the law used in the Doeblin pairwise contraction for the exactly-harmonic `hitVal`.
Opus-authored.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Killed-kernel composition (sum over `range (n+1)`, allowing the diagonal). -/
def KCompK (P Q : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ :=
  fun n k => ∑ j ∈ Finset.range (n + 1), P n j * Q j k

/-- `L`-fold killed-kernel power; `KPowK 0` is the identity kernel `δ(k=n)`. -/
def KPowK : ℕ → (ℕ → ℕ → ℝ) → ℕ → ℕ → ℝ
  | 0, _ => fun n k => if k = n then 1 else 0
  | L + 1, P => KCompK P (KPowK L P)

lemma KCompK_nonneg {P Q : ℕ → ℕ → ℝ} (hP : ∀ n k, 0 ≤ P n k) (hQ : ∀ n k, 0 ≤ Q n k)
    (n k : ℕ) : 0 ≤ KCompK P Q n k :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (hP n j) (hQ j k))

/-- Composition kills `n < k` when the right kernel has support `· ≤ ·` (`a < b → Q a b = 0`). -/
lemma KCompK_support {P Q : ℕ → ℕ → ℝ} (hQ : ∀ a b, a < b → Q a b = 0)
    {n k : ℕ} (hnk : n < k) : KCompK P Q n k = 0 := by
  rw [KCompK]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_range] at hj
  rw [hQ j k (by omega), mul_zero]

lemma KPowK_nonneg {P : ℕ → ℕ → ℝ} (hP : ∀ n k, 0 ≤ P n k) :
    ∀ (L n k : ℕ), 0 ≤ KPowK L P n k := by
  intro L
  induction L with
  | zero => intro n k; simp only [KPowK]; split <;> norm_num
  | succ L ih => intro n k; rw [KPowK]; exact KCompK_nonneg hP ih n k

/-- `KPowK L P` has support `n < k → · = 0` (the killed chain never moves to a strictly larger index). -/
lemma KPowK_support {P : ℕ → ℕ → ℝ} : ∀ (L : ℕ) {n k : ℕ}, n < k → KPowK L P n k = 0 := by
  intro L
  induction L with
  | zero => intro n k hnk; simp only [KPowK]; rw [if_neg (by omega)]
  | succ L ih => intro n k hnk; rw [KPowK]; exact KCompK_support (fun a b hab => ih hab) hnk

end AnalyticCombinatorics.Ch8.Partitions.Erdos
