import Mathlib

/-!
# R7 Fact B via Doeblin: the escape-split overlap contraction

The plain Doeblin inequality `doeblin_average_diff_bound` bounds `|∑p·f − ∑q·f|` by `(1−δ)·W` where `W`
is the oscillation of `f` over the *whole* support.  For the partition predecessor kernel the support is
wide (a single step can drop the rank arbitrarily far), so `W` does not contract.  The fix: split the
support into a high-rank "good" band `G` carrying the overlap `δ` and a low-rank "bad" set carrying only
mass `≤ η`.  Then

  `|∑p·f − ∑q·f| ≤ (1−δ)·W + 3·η·M`,

where `W` is the oscillation of `f` over `G` only and `M` bounds `|f|`.  Driving `η → 0` (escape mass)
and keeping `δ` fixed turns this into the step contraction `V(R) ≤ (1−δ)·V(R−B) + e(R)`, `e → 0`.
Pure nonnegative-sequence algebra — no probability.  Opus-authored.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **Escape-split Doeblin contraction.** Probability vectors `p, q` on `s` with overlap `≥ δ` on the
good band `G`, bad-mass `≤ η`, `f` valued in `[lo, lo+W]` on `G` and `|f| ≤ M`, `|lo| ≤ M`, differ by
at most `(1−δ)·W + 3·η·M`. -/
lemma doeblin_escape_bound {s : Finset ℕ} {p q f : ℕ → ℝ} {δ η lo W M : ℝ}
    (G : ℕ → Prop) [DecidablePred G]
    (hpnn : ∀ k ∈ s, 0 ≤ p k) (hqnn : ∀ k ∈ s, 0 ≤ q k)
    (hpm : ∑ k ∈ s, p k = 1) (hqm : ∑ k ∈ s, q k = 1)
    (hov : δ ≤ ∑ k ∈ s.filter G, min (p k) (q k))
    (hpbad : ∑ k ∈ s.filter (fun k => ¬ G k), p k ≤ η)
    (hqbad : ∑ k ∈ s.filter (fun k => ¬ G k), q k ≤ η)
    (hfband : ∀ k ∈ s.filter G, lo ≤ f k ∧ f k ≤ lo + W) (hW : 0 ≤ W)
    (hfbd : ∀ k ∈ s, |f k| ≤ M) (hlo : |lo| ≤ M) (hη : 0 ≤ η) :
    |∑ k ∈ s, p k * f k - ∑ k ∈ s, q k * f k| ≤ (1 - δ) * W + 3 * η * M := by
  classical
  set sg := s.filter G with hsg
  set sb := s.filter (fun k => ¬ G k) with hsb
  have hMnn : 0 ≤ M := le_trans (abs_nonneg lo) hlo
  -- split each sum over `s` into the good and bad parts
  have hsplit : ∀ g : ℕ → ℝ, ∑ k ∈ s, g k * f k
      = (∑ k ∈ sg, g k * f k) + ∑ k ∈ sb, g k * f k := by
    intro g
    rw [hsg, hsb, Finset.sum_filter_add_sum_filter_not s G (fun k => g k * f k)]
  rw [hsplit p, hsplit q]
  -- bad-part bound: |∑_bad g·f| ≤ η·M
  have hbad : ∀ g : ℕ → ℝ, (∀ k ∈ s, 0 ≤ g k) → (∑ k ∈ sb, g k ≤ η) →
      |∑ k ∈ sb, g k * f k| ≤ η * M := by
    intro g hgnn hgη
    have hsubset : sb ⊆ s := by rw [hsb]; exact Finset.filter_subset _ _
    calc |∑ k ∈ sb, g k * f k| ≤ ∑ k ∈ sb, |g k * f k| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k ∈ sb, g k * |f k| := by
          apply Finset.sum_congr rfl; intro k hk
          rw [abs_mul, abs_of_nonneg (hgnn k (hsubset hk))]
      _ ≤ ∑ k ∈ sb, g k * M := by
          apply Finset.sum_le_sum; intro k hk
          exact mul_le_mul_of_nonneg_left (hfbd k (hsubset hk)) (hgnn k (hsubset hk))
      _ = (∑ k ∈ sb, g k) * M := by rw [Finset.sum_mul]
      _ ≤ η * M := mul_le_mul_of_nonneg_right hgη hMnn
  have hbadp := hbad p hpnn hpbad
  have hbadq := hbad q hqnn hqbad
  -- good-part bound: |∑_good p·f − ∑_good q·f| ≤ (1−δ)·W + η·M
  set r : ℕ → ℝ := fun k => min (p k) (q k) with hr
  have hgnn_p : ∀ k ∈ sg, 0 ≤ p k := fun k hk => hpnn k (Finset.filter_subset _ _ hk)
  have hgnn_q : ∀ k ∈ sg, 0 ≤ q k := fun k hk => hqnn k (Finset.filter_subset _ _ hk)
  have hpr : ∀ k ∈ sg, 0 ≤ p k - r k := fun k _ => by
    simp only [hr]; linarith [min_le_left (p k) (q k)]
  have hqr : ∀ k ∈ sg, 0 ≤ q k - r k := fun k _ => by
    simp only [hr]; linarith [min_le_right (p k) (q k)]
  set mp := ∑ k ∈ sg, p k with hmp
  set mq := ∑ k ∈ sg, q k with hmq
  set ρ := ∑ k ∈ sg, r k with hρ
  have hmp1 : mp ≤ 1 := by
    rw [hmp]; calc ∑ k ∈ sg, p k ≤ ∑ k ∈ s, p k :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun k hk _ => hpnn k hk)
      _ = 1 := hpm
  have hmq1 : mq ≤ 1 := by
    rw [hmq]; calc ∑ k ∈ sg, q k ≤ ∑ k ∈ s, q k :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun k hk _ => hqnn k hk)
      _ = 1 := hqm
  have hρδ : δ ≤ ρ := by rw [hρ, hr]; exact hov
  -- `r = min p q` cancels in the difference of good averages
  set Sp := ∑ k ∈ sg, (p k - r k) * f k with hSp
  set Sq := ∑ k ∈ sg, (q k - r k) * f k with hSq
  have hcancel : (∑ k ∈ sg, p k * f k) - (∑ k ∈ sg, q k * f k) = Sp - Sq := by
    rw [hSp, hSq, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  have hmass_pr : ∑ k ∈ sg, (p k - r k) = mp - ρ := by
    rw [Finset.sum_sub_distrib, ← hmp, ← hρ]
  have hmass_qr : ∑ k ∈ sg, (q k - r k) = mq - ρ := by
    rw [Finset.sum_sub_distrib, ← hmq, ← hρ]
  -- bracket each good sub-average between `mass·lo` and `mass·lo + mass·W`
  have hSp_lo : (mp - ρ) * lo ≤ Sp := by
    rw [hSp, ← hmass_pr, Finset.sum_mul]
    exact Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (hfband k hk).1 (hpr k hk))
  have hSp_hi : Sp ≤ (mp - ρ) * lo + (mp - ρ) * W := by
    calc Sp ≤ ∑ k ∈ sg, (p k - r k) * (lo + W) := by
          rw [hSp]; exact Finset.sum_le_sum
            (fun k hk => mul_le_mul_of_nonneg_left (hfband k hk).2 (hpr k hk))
      _ = (mp - ρ) * (lo + W) := by rw [← Finset.sum_mul, hmass_pr]
      _ = (mp - ρ) * lo + (mp - ρ) * W := by ring
  have hSq_lo : (mq - ρ) * lo ≤ Sq := by
    rw [hSq, ← hmass_qr, Finset.sum_mul]
    exact Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (hfband k hk).1 (hqr k hk))
  have hSq_hi : Sq ≤ (mq - ρ) * lo + (mq - ρ) * W := by
    calc Sq ≤ ∑ k ∈ sg, (q k - r k) * (lo + W) := by
          rw [hSq]; exact Finset.sum_le_sum
            (fun k hk => mul_le_mul_of_nonneg_left (hfband k hk).2 (hqr k hk))
      _ = (mq - ρ) * (lo + W) := by rw [← Finset.sum_mul, hmass_qr]
      _ = (mq - ρ) * lo + (mq - ρ) * W := by ring
  have hPW : (mp - ρ) * W ≤ (1 - δ) * W := mul_le_mul_of_nonneg_right (by linarith) hW
  have hQW : (mq - ρ) * W ≤ (1 - δ) * W := mul_le_mul_of_nonneg_right (by linarith) hW
  -- |mp − mq| ≤ η  (each good mass is 1 minus its bad mass, both bad masses in [0, η])
  have hpgood_split : mp + ∑ k ∈ sb, p k = 1 := by
    rw [hmp, hsg, hsb, Finset.sum_filter_add_sum_filter_not s G p, hpm]
  have hqgood_split : mq + ∑ k ∈ sb, q k = 1 := by
    rw [hmq, hsg, hsb, Finset.sum_filter_add_sum_filter_not s G q, hqm]
  have hpbnn : 0 ≤ ∑ k ∈ sb, p k :=
    Finset.sum_nonneg (fun k hk => hpnn k (Finset.filter_subset _ _ hk))
  have hqbnn : 0 ≤ ∑ k ∈ sb, q k :=
    Finset.sum_nonneg (fun k hk => hqnn k (Finset.filter_subset _ _ hk))
  have hmpmq : |mp - mq| ≤ η := by
    have h1 : mp - mq = (∑ k ∈ sb, q k) - (∑ k ∈ sb, p k) := by linarith
    rw [h1, abs_le]; constructor <;> linarith
  have hPLQL : |(mp - ρ) * lo - (mq - ρ) * lo| ≤ η * M := by
    have heq : (mp - ρ) * lo - (mq - ρ) * lo = (mp - mq) * lo := by ring
    rw [heq, abs_mul]
    exact mul_le_mul hmpmq hlo (abs_nonneg lo) hη
  rw [abs_le] at hPLQL
  have hgood : |(∑ k ∈ sg, p k * f k) - (∑ k ∈ sg, q k * f k)| ≤ (1 - δ) * W + η * M := by
    rw [hcancel, abs_le]
    constructor
    · linarith [hSp_lo, hSp_hi, hSq_lo, hSq_hi, hPW, hQW, hPLQL.1, hPLQL.2]
    · linarith [hSp_lo, hSp_hi, hSq_lo, hSq_hi, hPW, hQW, hPLQL.1, hPLQL.2]
  -- bad difference bound
  have hbd2 : |(∑ k ∈ sb, p k * f k) - (∑ k ∈ sb, q k * f k)| ≤ η * M + η * M := by
    have h := abs_add_le (∑ k ∈ sb, p k * f k) (-(∑ k ∈ sb, q k * f k))
    rw [← sub_eq_add_neg, abs_neg] at h
    linarith [hbadp, hbadq]
  -- combine good + bad
  calc |(∑ k ∈ sg, p k * f k + ∑ k ∈ sb, p k * f k)
          - (∑ k ∈ sg, q k * f k + ∑ k ∈ sb, q k * f k)|
      = |((∑ k ∈ sg, p k * f k) - (∑ k ∈ sg, q k * f k))
          + ((∑ k ∈ sb, p k * f k) - (∑ k ∈ sb, q k * f k))| := by congr 1; ring
    _ ≤ |(∑ k ∈ sg, p k * f k) - (∑ k ∈ sg, q k * f k)|
          + |(∑ k ∈ sb, p k * f k) - (∑ k ∈ sb, q k * f k)| := abs_add_le _ _
    _ ≤ ((1 - δ) * W + η * M) + (η * M + η * M) := by linarith [hgood, hbd2]
    _ = (1 - δ) * W + 3 * η * M := by ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
