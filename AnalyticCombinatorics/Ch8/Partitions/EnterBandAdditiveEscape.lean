import AnalyticCombinatorics.Ch8.Partitions.RankBandEntrance
import AnalyticCombinatorics.Ch8.Partitions.RankDropKer

/-!
# Ceiling-escape brick 4 (THE KEY BRICK): the abstract additive escape super-solution

This is the deterministic core of the elementary close (R9).  It replaces the conditional-ratio
strategy of `enterBand_deep_mass_le_of_conditional` by a **direct additive super-solution** driven by
the banked drop-1 minorization `η` and the banked deep-mass tail majorant `U`.

For the first-entrance kernel into the ceiling down-set `B = ceilBand R A`, the overshoot below the
band floor `R` from any off-band start `n` satisfies the finite super-solution

  `esc(n) ≤ E(g(n))`,   `E(g) = (1/η)·∑_{i∈range(g+1)} U(A+i)`,   `g(v) = rnk v − (R+A)`,

proved by strong induction on `n`.  The mechanism (R9): one off-band step splits into deep crossing
(`≤ U(A+g)` by `hdeep`), safe crossing (lands in-band, not deep), and off-band continuation (IH).
The drop-1 mass `≥ η` either shifts `g → g−1` (when `g > 0`), and `η·(E(g)−E(g−1)) = U(A+g)` pays the
deep forcing exactly, or — when `g = 0` — crosses safely into the band, removing `≥ η` from the
off-band continuation, and `η·E(0) = U(A)` again pays the forcing.

Since `E(g) ≤ (1/η)·∑'_i U(A+i)`, this drives the overshoot to `0` once the band floor `R → ∞`
(brick 5).

NEW file; imports the banked engine bricks; does not modify them.  Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **Brick 4 — abstract additive escape super-solution (finite form).**

Let `P ≥ 0` be a sub-stochastic predecessor kernel supported on `k < v`, row-stochastic off the
ceiling band `B = ceilBand R A`.  Suppose, at every off-band vertex `v`:

* (deep) the one-step deep-crossing mass (landing in `B` below rank `R`) is `≤ U (A + g v)`, where
  `g v = rnk v − (R + A)`;
* (drop-1) the rank-drop-exactly-1 mass is `≥ η`.

With `U ≥ 0` and `η > 0`, the first-entrance overshoot below `R` from any off-band start `n`
satisfies `esc(n) ≤ E (g n)`, `E g = (1/η)·∑_{i∈range(g+1)} U (A+i)`. -/
theorem enterBand_deep_mass_le_of_tail_forcing_drop_one
    {P : ℕ → ℕ → ℝ} {R A : ℕ} {U : ℕ → ℝ} {η : ℝ}
    (hη : 0 < η) (hU0 : ∀ t, 0 ≤ U t)
    (hPnn : ∀ n k, 0 ≤ P n k)
    (hPsupp : ∀ m k, m ≤ k → P m k = 0)
    (hrow : ∀ v, v ∉ ceilBand R A → ∑ k ∈ Finset.range v, P v k = 1)
    (hdeep : ∀ v, v ∉ ceilBand R A →
        (∑ k ∈ (ceilBand R A).filter (fun k => ¬ R ≤ rnk k), P v k)
          ≤ U (A + (rnk v - (R + A))))
    (hdrop1 : ∀ v, v ∉ ceilBand R A →
        η ≤ ∑ k ∈ (Finset.range v).filter (fun k => rnk v - rnk k = 1), P v k) :
    ∀ n, n ∉ ceilBand R A →
      (∑ z ∈ (ceilBand R A).filter (fun z => ¬ R ≤ rnk z),
            enterBandKer P (ceilBand R A) n z)
        ≤ (1 / η) * ∑ i ∈ Finset.range ((rnk n - (R + A)) + 1), U (A + i) := by
  classical
  set B := ceilBand R A with hBdef
  -- the potential E g
  set E : ℕ → ℝ := fun g => (1 / η) * ∑ i ∈ Finset.range (g + 1), U (A + i) with hEdef
  -- esc' k : deep first-entrance mass from k
  set esc : ℕ → ℝ := fun k => ∑ z ∈ B.filter (fun z => ¬ R ≤ rnk z), enterBandKer P B k z with hescdef
  set g : ℕ → ℕ := fun v => rnk v - (R + A) with hgdef
  -- basic facts about E
  have hEnn : ∀ m, 0 ≤ E m := by
    intro m; simp only [hEdef]
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun i _ => hU0 _)
  have hEmono : ∀ {m m' : ℕ}, m ≤ m' → E m ≤ E m' := by
    intro m m' hmm
    simp only [hEdef]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi; rw [Finset.mem_range] at hi ⊢; omega
    · intro i _ _; exact hU0 _
  -- E g − E (g−1) = (1/η)·U(A+g) for g ≥ 1
  have hEdiff : ∀ m : ℕ, 1 ≤ m → E m - E (m - 1) = (1 / η) * U (A + m) := by
    intro m hm
    simp only [hEdef]
    have hmsucc : (m - 1) + 1 = m := by omega
    have hsplit : ∑ i ∈ Finset.range (m + 1), U (A + i)
        = (∑ i ∈ Finset.range ((m - 1) + 1), U (A + i)) + U (A + m) := by
      rw [hmsucc, Finset.sum_range_succ]
    rw [hsplit]; ring
  -- E 0 = (1/η)·U(A)
  have hE0 : E 0 = (1 / η) * U (A + 0) := by
    rw [hEdef]; simp
  -- the goal reduced to esc n ≤ E (g n)
  suffices hmain : ∀ n, n ∉ B → esc n ≤ E (g n) by exact hmain
  -- main strong induction
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    -- expand esc n over range n
    have hexpand : ∀ z, enterBandKer P B n z
        = ∑ k ∈ Finset.range n, P n k * enterBandKer P B k z := by
      intro z; rw [enterBandKer_eq, if_neg hn]
    have hescn : esc n = ∑ k ∈ Finset.range n, P n k * esc k := by
      simp only [hescdef]
      rw [Finset.sum_congr rfl (fun z _ => hexpand z), Finset.sum_comm]
      exact Finset.sum_congr rfl (fun k _ => by rw [Finset.mul_sum])
    -- off-band n facts
    have hrnkn : rnk n = R + A + g n := by
      have := not_mem_ceilBand_rank_ge hn; simp only [hgdef]; omega
    -- esc k for in-band k : point mass at k, deep iff ¬ R ≤ rnk k
    have hesc_inband : ∀ k, k ∈ B → esc k = if ¬ R ≤ rnk k then (1:ℝ) else 0 := by
      intro k hk
      simp only [hescdef]
      have hval : ∀ z, enterBandKer P B k z = if z = k then 1 else 0 := by
        intro z; rw [enterBandKer_eq, if_pos hk]
      rw [Finset.sum_congr rfl (fun z _ => hval z)]
      by_cases hkd : ¬ R ≤ rnk k
      · rw [if_pos hkd, Finset.sum_ite_eq' (B.filter (fun z => ¬ R ≤ rnk z)) k (fun _ => (1:ℝ)),
          if_pos (Finset.mem_filter.mpr ⟨hk, hkd⟩)]
      · rw [if_neg hkd]
        refine Finset.sum_eq_zero (fun z hz => ?_)
        rw [if_neg]; rintro rfl; exact hkd (Finset.mem_filter.mp hz).2
    -- pointwise bound esc k ≤ φ k on range n
    set φ : ℕ → ℝ := fun k => if k ∈ B then (if ¬ R ≤ rnk k then (1:ℝ) else 0) else E (g k)
      with hφdef
    have hesc_le : ∀ k ∈ Finset.range n, esc k ≤ φ k := by
      intro k hk
      rw [Finset.mem_range] at hk
      simp only [hφdef]
      by_cases hkB : k ∈ B
      · rw [if_pos hkB, hesc_inband k hkB]
      · rw [if_neg hkB]; exact ih k hk hkB
    -- ∑ P n k · esc k ≤ ∑ P n k · φ k
    have hstep1 : esc n ≤ ∑ k ∈ Finset.range n, P n k * φ k := by
      rw [hescn]
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hesc_le k hk) (hPnn n k)
    -- split range n into in-band / off-band predecessors
    have hsplit : ∑ k ∈ Finset.range n, P n k * φ k
        = (∑ k ∈ (Finset.range n).filter (fun k => k ∈ B), P n k * φ k)
          + ∑ k ∈ (Finset.range n).filter (fun k => k ∉ B), P n k * φ k := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.range n) (fun k => k ∈ B)]
    -- in-band part = deep in-band mass = ∑_{B.filter deep} P n k ≤ U (A + g n)
    have hinband : (∑ k ∈ (Finset.range n).filter (fun k => k ∈ B), P n k * φ k)
        = ∑ k ∈ B.filter (fun k => ¬ R ≤ rnk k), P n k := by
      -- φ k = [deep k] for k ∈ B; then extend the index set (P n k = 0 off range n)
      have hval : ∀ k ∈ (Finset.range n).filter (fun k => k ∈ B),
          P n k * φ k = if ¬ R ≤ rnk k then P n k else 0 := by
        intro k hk
        have hkB : k ∈ B := (Finset.mem_filter.mp hk).2
        simp only [hφdef, if_pos hkB]
        by_cases hkd : ¬ R ≤ rnk k <;> simp [hkd]
      rw [Finset.sum_congr rfl hval, ← Finset.sum_filter]
      apply Finset.sum_subset_zero_on_sdiff
      · intro k hk
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at hk
        exact Finset.mem_filter.mpr ⟨hk.1.2, hk.2⟩
      · intro k hk
        rw [Finset.mem_sdiff, Finset.mem_filter] at hk
        have hkn : n ≤ k := by
          by_contra h; push_neg at h
          exact hk.2 (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr h, hk.1.1⟩, hk.1.2⟩)
        exact hPsupp n k hkn
      · intro k _; rfl
    have hinband_le : (∑ k ∈ (Finset.range n).filter (fun k => k ∈ B), P n k * φ k)
        ≤ U (A + g n) := by
      rw [hinband]; exact hdeep n hn
    -- off-band part written with E(g k)
    have hoffval : ∀ k ∈ (Finset.range n).filter (fun k => k ∉ B),
        P n k * φ k = P n k * E (g k) := by
      intro k hk
      have hkB : k ∉ B := (Finset.mem_filter.mp hk).2
      simp only [hφdef, if_neg hkB]
    rw [hsplit, Finset.sum_congr rfl hoffval] at hstep1
    -- Now: esc n ≤ inband + ∑_{offband} P n k · E(g k); bound inband ≤ U(A+g n)
    set Soff := ∑ k ∈ (Finset.range n).filter (fun k => k ∉ B), P n k with hSoffdef
    -- each off-band k<n: rnk k ≤ rnk n, k ∉ B so rnk k ≥ R+A, hence g k ≤ g n
    have hgk_le : ∀ k ∈ (Finset.range n).filter (fun k => k ∉ B), g k ≤ g n := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      have hrnkkle : rnk k ≤ rnk n := rnk_mono hk.1.le
      simp only [hgdef]; omega
    -- row-sum bound : Soff ≤ 1
    have hSoff_le_one : Soff ≤ 1 := by
      rw [hSoffdef, ← hrow n hn]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk; exact (Finset.mem_filter.mp hk).1
      · intro k _ _; exact hPnn n k
    have hSoff_nn : 0 ≤ Soff := Finset.sum_nonneg (fun k _ => hPnn n k)
    -- the drop-1 mass over range n (banked ≥ η)
    set Drop1 := ∑ k ∈ (Finset.range n).filter (fun k => rnk n - rnk k = 1), P n k with hDrop1def
    have hDrop1_ge : η ≤ Drop1 := by
      rw [hDrop1def]; exact hdrop1 n hn
    have hDrop1_nn : 0 ≤ Drop1 := Finset.sum_nonneg (fun k _ => hPnn n k)
    -- It suffices: U(A+g n) + (off-band E-sum) ≤ E (g n)
    have hoffsum_def : True := trivial
    refine le_trans hstep1 ?_
    -- abbreviate the off-band E-sum
    set OffE := ∑ k ∈ (Finset.range n).filter (fun k => k ∉ B), P n k * E (g k) with hOffEdef
    refine le_trans (by linarith [hinband_le] :
        (∑ k ∈ (Finset.range n).filter (fun k => k ∈ B), P n k * φ k)
        + OffE ≤ U (A + g n) + OffE) ?_
    -- now goal: U (A + g n) + OffE ≤ E (g n)
    rcases Nat.eq_zero_or_pos (g n) with hg0 | hgpos
    · -- CASE g n = 0
      -- every off-band k<n has g k = 0 (rnk k = R+A); so OffE = Soff · E 0
      have hgk0 : ∀ k ∈ (Finset.range n).filter (fun k => k ∉ B), g k = 0 := by
        intro k hk
        have hle := hgk_le k hk
        omega
      have hOffE_eq : OffE = Soff * E 0 := by
        rw [hOffEdef, hSoffdef, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        rw [hgk0 k hk]
      -- drop-1 predecessors are in-band (rnk = rnk n - 1 = R+A-1 < R+A), disjoint from off-band
      -- so Soff + Drop1 ≤ row-sum = 1, hence Soff ≤ 1 - η
      have hdisj : Disjoint ((Finset.range n).filter (fun k => k ∉ B))
          ((Finset.range n).filter (fun k => rnk n - rnk k = 1)) := by
        rw [Finset.disjoint_left]
        intro k hkoff hkd1
        rw [Finset.mem_filter] at hkoff hkd1
        have hkB : k ∉ B := hkoff.2
        have hd1 : rnk n - rnk k = 1 := hkd1.2
        -- rnk k = rnk n - 1 = R + A - 1 < R + A ⟹ k ∈ B, contradiction
        have hkn : k < n := Finset.mem_range.mp hkoff.1
        have hrnkkle : rnk k ≤ rnk n := rnk_mono hkn.le
        have : rnk k < R + A := by rw [hrnkn, hg0] at hd1 hrnkkle; omega
        exact hkB (mem_ceilBand_iff.mpr this)
      have hSD_le : Soff + Drop1 ≤ 1 := by
        rw [hSoffdef, hDrop1def, ← Finset.sum_union hdisj, ← hrow n hn]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          rw [Finset.mem_union] at hk
          rcases hk with h | h
          · exact (Finset.mem_filter.mp h).1
          · exact (Finset.mem_filter.mp h).1
        · intro k _ _; exact hPnn n k
      have hSoff_le : Soff ≤ 1 - η := by linarith [hDrop1_ge, hSD_le]
      -- assemble: U(A+0) + Soff·E0 ≤ U(A+0) + (1-η)E0 = E0 ; and goal RHS = E (g n) = E 0
      have hgnE : E (g n) = E 0 := by rw [hg0]
      rw [hOffE_eq, hgnE, hE0, hg0]
      -- goal: U (A + 0) + Soff * ((1/η)*U(A+0)) ≤ (1/η)*U(A+0)
      have hUA0 : 0 ≤ U (A + 0) := hU0 _
      have hηE0 : η * ((1 / η) * U (A + 0)) = U (A + 0) := by
        field_simp
      nlinarith [mul_le_mul_of_nonneg_right hSoff_le
          (by positivity : (0:ℝ) ≤ (1 / η) * U (A + 0)), hηE0, hUA0, hη]
    · -- CASE g n ≥ 1
      -- per-term bound on off-band k: E (g k) ≤ E (g n) − [drop1 k]·(E (g n) − E (g n − 1))
      set diff := E (g n) - E (g n - 1) with hdiffdef
      have hdiff_eq : η * diff = U (A + g n) := by
        rw [hdiffdef, hEdiff (g n) hgpos]; field_simp
      have hdiff_nn : 0 ≤ diff := by rw [hdiffdef]; linarith [hEmono (Nat.sub_le (g n) 1)]
      -- drop1 ⊆ off-band (in case g n ≥ 1)
      have hsubD : (Finset.range n).filter (fun k => rnk n - rnk k = 1)
          ⊆ (Finset.range n).filter (fun k => k ∉ B) := by
        intro k hk
        rw [Finset.mem_filter] at hk ⊢
        refine ⟨hk.1, ?_⟩
        have hd1 : rnk n - rnk k = 1 := hk.2
        have hkn : k < n := Finset.mem_range.mp hk.1
        have hrnkkle : rnk k ≤ rnk n := rnk_mono hkn.le
        -- rnk k = rnk n - 1 = R+A+g n - 1 ≥ R+A (since g n ≥ 1) ⟹ k ∉ B
        have : R + A ≤ rnk k := by rw [hrnkn] at hd1 hrnkkle; omega
        intro hcon; exact (Nat.not_le.mpr (mem_ceilBand_iff.mp hcon)) this
      -- OffE ≤ Soff·E(g n) − Drop1·diff
      have hOffE_le : OffE ≤ Soff * E (g n) - Drop1 * diff := by
        -- split off-band by drop1
        have hsp : (∑ k ∈ (Finset.range n).filter (fun k => k ∉ B), P n k * E (g k))
            = (∑ k ∈ ((Finset.range n).filter (fun k => k ∉ B)).filter
                  (fun k => rnk n - rnk k = 1), P n k * E (g k))
              + ∑ k ∈ ((Finset.range n).filter (fun k => k ∉ B)).filter
                  (fun k => ¬ rnk n - rnk k = 1), P n k * E (g k) := by
          rw [← Finset.sum_filter_add_sum_filter_not
            ((Finset.range n).filter (fun k => k ∉ B)) (fun k => rnk n - rnk k = 1)]
        rw [hOffEdef, hsp]
        -- drop1-part: E (g k) = E (g n − 1)
        have hpart1 : (∑ k ∈ ((Finset.range n).filter (fun k => k ∉ B)).filter
                  (fun k => rnk n - rnk k = 1), P n k * E (g k))
            = Drop1 * E (g n - 1) := by
          rw [hDrop1def, Finset.sum_mul]
          -- the two index sets coincide (drop1 ⊆ off-band), and E(g k)=E(g n−1)
          have hidx : ((Finset.range n).filter (fun k => k ∉ B)).filter
                (fun k => rnk n - rnk k = 1)
              = (Finset.range n).filter (fun k => rnk n - rnk k = 1) := by
            apply Finset.filter_comm _ _ _ |>.trans
            apply Finset.filter_eq_self.mpr
            intro k hk
            have := hsubD hk
            exact (Finset.mem_filter.mp this).2
          rw [hidx]
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mem_filter, Finset.mem_range] at hk
          have hd1 : rnk n - rnk k = 1 := hk.2
          have hrnkkle : rnk k ≤ rnk n := rnk_mono hk.1.le
          have hgkeq : g k = g n - 1 := by simp only [hgdef]; rw [hrnkn] at *; omega
          rw [hgkeq]
        rw [hpart1]
        -- non-drop1 part: E (g k) ≤ E (g n)
        have hpart2 : (∑ k ∈ ((Finset.range n).filter (fun k => k ∉ B)).filter
                  (fun k => ¬ rnk n - rnk k = 1), P n k * E (g k))
            ≤ (∑ k ∈ ((Finset.range n).filter (fun k => k ∉ B)).filter
                  (fun k => ¬ rnk n - rnk k = 1), P n k * E (g n)) := by
          apply Finset.sum_le_sum
          intro k hk
          have hkoff : k ∈ (Finset.range n).filter (fun k => k ∉ B) :=
            (Finset.mem_filter.mp hk).1
          exact mul_le_mul_of_nonneg_left (hEmono (hgk_le k hkoff)) (hPnn n k)
        -- Soff = drop1-mass + non-drop1-mass (within off-band)
        have hSoff_split : Soff
            = Drop1 + ∑ k ∈ ((Finset.range n).filter (fun k => k ∉ B)).filter
                (fun k => ¬ rnk n - rnk k = 1), P n k := by
          rw [hSoffdef,
            ← Finset.sum_filter_add_sum_filter_not
              ((Finset.range n).filter (fun k => k ∉ B)) (fun k => rnk n - rnk k = 1)]
          congr 1
          rw [hDrop1def]
          have hidx : ((Finset.range n).filter (fun k => k ∉ B)).filter
                (fun k => rnk n - rnk k = 1)
              = (Finset.range n).filter (fun k => rnk n - rnk k = 1) := by
            apply Finset.filter_comm _ _ _ |>.trans
            apply Finset.filter_eq_self.mpr
            intro k hk
            have := hsubD hk
            exact (Finset.mem_filter.mp this).2
          rw [hidx]
        -- assemble
        have hnon_eq : (∑ k ∈ ((Finset.range n).filter (fun k => k ∉ B)).filter
                  (fun k => ¬ rnk n - rnk k = 1), P n k * E (g n))
            = (Soff - Drop1) * E (g n) := by
          rw [hSoff_split]; rw [← Finset.sum_mul]; ring_nf
        calc Drop1 * E (g n - 1)
              + (∑ k ∈ ((Finset.range n).filter (fun k => k ∉ B)).filter
                  (fun k => ¬ rnk n - rnk k = 1), P n k * E (g k))
            ≤ Drop1 * E (g n - 1)
              + (∑ k ∈ ((Finset.range n).filter (fun k => k ∉ B)).filter
                  (fun k => ¬ rnk n - rnk k = 1), P n k * E (g n)) := by linarith [hpart2]
          _ = Drop1 * E (g n - 1) + (Soff - Drop1) * E (g n) := by rw [hnon_eq]
          _ = Soff * E (g n) - Drop1 * diff := by rw [hdiffdef]; ring
      -- final: U(A+g n) + OffE ≤ U(A+g n) + Soff·E(g n) − Drop1·diff ≤ E(g n)
      have hDdiff : U (A + g n) ≤ Drop1 * diff := by
        rw [← hdiff_eq]; exact mul_le_mul_of_nonneg_right hDrop1_ge hdiff_nn
      have hSE : Soff * E (g n) ≤ E (g n) := by
        nlinarith [mul_le_mul_of_nonneg_right hSoff_le_one (hEnn (g n)), hEnn (g n)]
      linarith [hOffE_le, hDdiff, hSE]

#print axioms enterBand_deep_mass_le_of_tail_forcing_drop_one

end AnalyticCombinatorics.Ch8.Partitions.Erdos
