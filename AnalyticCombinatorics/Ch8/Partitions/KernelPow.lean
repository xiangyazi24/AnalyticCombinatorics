import Mathlib

/-!
# R7 Fact B via Doeblin (File B): kernel composition and powers

Composition `KComp P Q n k = ∑_{j<n} P n j · Q j k` and the `L`-fold power `KPow L P` of a predecessor
kernel.  Proves nonnegativity and (strict) predecessor-support preservation by induction on `L` — the
algebraic foundation for the finite-time Doeblin overlap and the `P^L`-harmonic identity for `hitVal`.
The identity kernel `KPow 0 = δ(k=n)` forces the *strict* support `n < k → · = 0`.  Opus-authored.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Kernel composition over predecessors: `(KComp P Q) n k = ∑_{j < n} P n j · Q j k`. -/
def KComp (P Q : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ :=
  fun n k => ∑ j ∈ Finset.range n, P n j * Q j k

/-- `L`-fold kernel power; `KPow 0` is the identity kernel `δ(k=n)`. -/
def KPow : ℕ → (ℕ → ℕ → ℝ) → ℕ → ℕ → ℝ
  | 0, _ => fun n k => if k = n then 1 else 0
  | L + 1, P => KComp P (KPow L P)

lemma KComp_nonneg {P Q : ℕ → ℕ → ℝ} (hP : ∀ n k, 0 ≤ P n k) (hQ : ∀ n k, 0 ≤ Q n k)
    (n k : ℕ) : 0 ≤ KComp P Q n k :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (hP n j) (hQ j k))

/-- Composition kills `n ≤ k` whenever the right kernel has strict predecessor support. -/
lemma KComp_support {P Q : ℕ → ℕ → ℝ} (hQ : ∀ a b, a < b → Q a b = 0)
    {n k : ℕ} (hnk : n ≤ k) : KComp P Q n k = 0 := by
  rw [KComp]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_range] at hj
  rw [hQ j k (by omega), mul_zero]

lemma KPow_nonneg {P : ℕ → ℕ → ℝ} (hP : ∀ n k, 0 ≤ P n k) :
    ∀ (L n k : ℕ), 0 ≤ KPow L P n k := by
  intro L
  induction L with
  | zero => intro n k; simp only [KPow]; split <;> norm_num
  | succ L ih => intro n k; rw [KPow]; exact KComp_nonneg hP ih n k

/-- `KPow L P` has strict predecessor support `n < k → · = 0`. -/
lemma KPow_support {P : ℕ → ℕ → ℝ} : ∀ (L : ℕ) {n k : ℕ}, n < k → KPow L P n k = 0 := by
  intro L
  induction L with
  | zero => intro n k hnk; simp only [KPow]; rw [if_neg (by omega)]
  | succ L ih => intro n k hnk; rw [KPow]; exact KComp_support (fun a b hab => ih hab) (le_of_lt hnk)

/-- For `L ≥ 1`, `KPow (L+1) P` kills `n ≤ k` (one step strictly drops the index). -/
lemma KPow_succ_support {P : ℕ → ℕ → ℝ} (L : ℕ) {n k : ℕ} (hnk : n ≤ k) :
    KPow (L + 1) P n k = 0 := by
  rw [KPow]
  exact KComp_support (fun a b hab => KPow_support L hab) hnk

end AnalyticCombinatorics.Ch8.Partitions.Erdos
