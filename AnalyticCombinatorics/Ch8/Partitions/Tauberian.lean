import Mathlib

/-!
# A logarithmic Tauberian theorem for cumulative coefficients

This file is intentionally independent of the partition development.  The
results are stated for an arbitrary nonnegative sequence of real coefficients.
-/

open Filter
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Tauberian

noncomputable section

/-- Cumulative sums of a sequence. -/
def Cum (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), a n

lemma Cum_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (N : ℕ) :
    0 ≤ Cum a N := by
  unfold Cum
  exact Finset.sum_nonneg fun n _ => ha n

lemma Cum_pos_of_pos_zero {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (ha0 : 0 < a 0) (N : ℕ) :
    0 < Cum a N := by
  unfold Cum
  have hmem : 0 ∈ Finset.range (N + 1) := by simp
  exact Finset.sum_pos' (fun n _ => ha n) ⟨0, hmem, ha0⟩

lemma Cum_mono {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) :
    Monotone (Cum a) := by
  intro M N hMN
  unfold Cum
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro n hn
    exact Finset.mem_range.mpr (Nat.lt_of_lt_of_le (Finset.mem_range.mp hn)
      (Nat.succ_le_succ hMN))
  · intro n _ _
    exact ha n

lemma term_le_Cum {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    a n ≤ Cum a n := by
  unfold Cum
  have hmem : n ∈ Finset.range (n + 1) := by simp
  exact Finset.single_le_sum (fun m _ => ha m) hmem

lemma Cum_succ (a : ℕ → ℝ) (N : ℕ) :
    Cum a (N + 1) = Cum a N + a (N + 1) := by
  unfold Cum
  rw [show N + 1 + 1 = N + 2 by omega]
  rw [Finset.sum_range_succ]

lemma finite_abel_cum (a : ℕ → ℝ) (q : ℝ) :
    ∀ M : ℕ,
      (1 - q) * (∑ N ∈ Finset.range (M + 1), Cum a N * q ^ N)
        =
      (∑ n ∈ Finset.range (M + 1), a n * q ^ n)
        - Cum a M * q ^ (M + 1)
  | 0 => by
      simp [Cum]
      ring_nf
  | M + 1 => by
      have ih := finite_abel_cum a q M
      rw [Finset.sum_range_succ
        (f := fun N => Cum a N * q ^ N) (n := M + 1)]
      rw [Finset.sum_range_succ
        (f := fun n => a n * q ^ n) (n := M + 1)]
      rw [mul_add, ih, Cum_succ]
      ring_nf
      simp [mul_comm]

theorem laplace_eq_abel_cum_q
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hsum : Summable fun n : ℕ => a n * q ^ n) :
    (∑' n : ℕ, a n * q ^ n)
      =
    ∑' N : ℕ, (1 - q) * (Cum a N * q ^ N) := by
  let f : ℕ → ℝ := fun n => a n * q ^ n
  let g : ℕ → ℝ := fun N => (1 - q) * (Cum a N * q ^ N)
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    dsimp [f]
    exact mul_nonneg (ha n) (pow_nonneg hq0 n)
  have hg_nonneg : ∀ N, 0 ≤ g N := by
    intro N
    dsimp [g]
    exact mul_nonneg (sub_nonneg.mpr hq1.le) (mul_nonneg (Cum_nonneg ha N) (pow_nonneg hq0 N))
  have hg_sum_bound : ∀ M : ℕ, ∑ N ∈ Finset.range M, g N ≤ ∑' n : ℕ, f n := by
    intro M
    cases M with
    | zero =>
        simpa [g] using tsum_nonneg hf_nonneg
    | succ M =>
        have hfin := finite_abel_cum a q M
        have htail_nonneg : 0 ≤ Cum a M * q ^ (M + 1) :=
          mul_nonneg (Cum_nonneg ha M) (pow_nonneg hq0 (M + 1))
        have hpartial :
            (1 - q) * (∑ N ∈ Finset.range (M + 1), Cum a N * q ^ N)
              ≤ ∑ n ∈ Finset.range (M + 1), a n * q ^ n := by
          linarith
        have hpartial_tsum :
            ∑ n ∈ Finset.range (M + 1), a n * q ^ n ≤ ∑' n : ℕ, f n := by
          simpa [f] using
            hsum.sum_le_tsum (Finset.range (M + 1)) (fun n _ => hf_nonneg n)
        calc
          ∑ N ∈ Finset.range (M + 1), g N
              = (1 - q) * (∑ N ∈ Finset.range (M + 1), Cum a N * q ^ N) := by
                simp [g, Finset.mul_sum]
          _ ≤ ∑ n ∈ Finset.range (M + 1), a n * q ^ n := hpartial
          _ ≤ ∑' n : ℕ, f n := hpartial_tsum
  have hg_summable : Summable g :=
    summable_of_sum_range_le hg_nonneg hg_sum_bound
  have htail_zero :
      Tendsto (fun M : ℕ => Cum a M * q ^ (M + 1)) atTop (𝓝 0) := by
    have hg_zero : Tendsto g atTop (𝓝 0) := hg_summable.tendsto_atTop_zero
    have hconst := hg_zero.const_mul (q / (1 - q))
    have hconst0 : Tendsto (fun M : ℕ => (q / (1 - q)) * g M) atTop (𝓝 0) := by
      simpa using hconst
    refine hconst0.congr' ?_
    filter_upwards with M
    dsimp [g]
    have hne : 1 - q ≠ 0 := by linarith
    field_simp [hne]
    rw [pow_succ']
    ring_nf
  have hsum_f_nat :
      Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M, f n) atTop
        (𝓝 (∑' n : ℕ, f n)) :=
    hsum.hasSum.tendsto_sum_nat
  have hsum_g_nat :
      Tendsto (fun M : ℕ => ∑ N ∈ Finset.range M, g N) atTop
        (𝓝 (∑' N : ℕ, g N)) :=
    hg_summable.hasSum.tendsto_sum_nat
  have hlim_right :
      Tendsto
        (fun M : ℕ => (∑ n ∈ Finset.range (M + 1), f n) - Cum a M * q ^ (M + 1))
        atTop
        (𝓝 ((∑' n : ℕ, f n) - 0)) :=
    (hsum_f_nat.comp (tendsto_add_atTop_nat 1)).sub htail_zero
  have hlim_left :
      Tendsto (fun M : ℕ => ∑ N ∈ Finset.range (M + 1), g N) atTop
        (𝓝 (∑' N : ℕ, g N)) :=
    hsum_g_nat.comp (tendsto_add_atTop_nat 1)
  have heq_seq :
      (fun M : ℕ => ∑ N ∈ Finset.range (M + 1), g N)
        =ᶠ[atTop]
      (fun M : ℕ => (∑ n ∈ Finset.range (M + 1), f n) - Cum a M * q ^ (M + 1)) := by
    refine Eventually.of_forall ?_
    intro M
    have hfin := finite_abel_cum a q M
    dsimp [f, g]
    rw [← hfin]
    simp [Finset.mul_sum]
  have hlim_left' :
      Tendsto (fun M : ℕ => ∑ N ∈ Finset.range (M + 1), g N) atTop
        (𝓝 ((∑' n : ℕ, f n) - 0)) :=
    hlim_right.congr' heq_seq.symm
  have huniq := tendsto_nhds_unique hlim_left hlim_left'
  simpa [f, g, sub_zero] using huniq.symm

theorem laplace_eq_abel_cum
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    {t : ℝ} (ht : 0 < t)
    (hsum : Summable fun n : ℕ => a n * Real.exp (-(t * n))) :
    (∑' n : ℕ, a n * Real.exp (-(t * n)))
      =
    (1 - Real.exp (-t))
      * ∑' N : ℕ, Cum a N * Real.exp (-(t * N)) := by
  let q : ℝ := Real.exp (-t)
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
  have hpow : ∀ n : ℕ, q ^ n = Real.exp (-(t * n)) := by
    intro n
    dsimp [q]
    rw [← Real.exp_nat_mul]
    ring_nf
  have hsum_q : Summable fun n : ℕ => a n * q ^ n := by
    refine hsum.congr ?_
    intro n
    rw [hpow n]
  have habel := laplace_eq_abel_cum_q a ha hq0 hq1 hsum_q
  calc
    (∑' n : ℕ, a n * Real.exp (-(t * n)))
        = ∑' n : ℕ, a n * q ^ n := by
          apply tsum_congr
          intro n
          rw [hpow n]
    _ = ∑' N : ℕ, (1 - q) * (Cum a N * q ^ N) := habel
    _ = (1 - q) * ∑' N : ℕ, Cum a N * q ^ N := by
          rw [tsum_mul_left]
    _ = (1 - Real.exp (-t))
      * ∑' N : ℕ, Cum a N * Real.exp (-(t * N)) := by
          dsimp [q]
          congr 1
          apply tsum_congr
          intro N
          rw [hpow N]

lemma laplace_term_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {t : ℝ} (n : ℕ) :
    0 ≤ a n * Real.exp (-(t * n)) := by
  exact mul_nonneg (ha n) (Real.exp_pos _).le

lemma Cum_mul_exp_le_laplace_sum
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    {t : ℝ} (ht : 0 < t) (N : ℕ) :
    Cum a N * Real.exp (-(t * N))
      ≤ ∑ n ∈ Finset.range (N + 1), a n * Real.exp (-(t * n)) := by
  unfold Cum
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum ?_
  intro n hn
  have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hexp :
      Real.exp (-(t * (N : ℝ))) ≤ Real.exp (-(t * (n : ℝ))) := by
    refine Real.exp_monotone ?_
    have hnN' : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
    nlinarith [mul_le_mul_of_nonneg_left hnN' ht.le]
  exact mul_le_mul_of_nonneg_left hexp (ha n)

lemma Cum_mul_exp_le_laplace_tsum
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    {t : ℝ} (ht : 0 < t)
    (hsum : Summable fun n : ℕ => a n * Real.exp (-(t * n)))
    (N : ℕ) :
    Cum a N * Real.exp (-(t * N))
      ≤ ∑' n : ℕ, a n * Real.exp (-(t * n)) := by
  exact (Cum_mul_exp_le_laplace_sum ha ht N).trans
    (hsum.sum_le_tsum (Finset.range (N + 1)) (fun n _ => laplace_term_nonneg ha n))

lemma laplace_tsum_pos_of_pos_zero
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (ha0 : 0 < a 0)
    {t : ℝ} (hsum : Summable fun n : ℕ => a n * Real.exp (-(t * n))) :
    0 < ∑' n : ℕ, a n * Real.exp (-(t * n)) := by
  have h0 : 0 < a 0 * Real.exp (-(t * (0 : ℕ))) := by
    simpa using ha0
  exact hsum.tsum_pos (fun n => laplace_term_nonneg ha n) 0 h0

lemma exp_quadratic_lower {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 / 4 ≤ Real.exp x := by
  have hlin : x / 2 ≤ Real.exp (x / 2) := by
    have h := Real.add_one_le_exp (x / 2)
    linarith
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ x / 2) (Real.exp_pos _).le).mpr hlin
  calc
    x ^ 2 / 4 = (x / 2) ^ 2 := by ring_nf
    _ ≤ Real.exp (x / 2) ^ 2 := hsq
    _ = Real.exp x := by
      rw [sq, ← Real.exp_add]
      ring_nf

lemma one_sub_exp_neg_ge_half {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    u / 2 ≤ 1 - Real.exp (-u) := by
  have hpos : 0 < 1 + u := by linarith
  have hexp_ge : 1 + u ≤ Real.exp u := by
    simpa [add_comm] using Real.add_one_le_exp u
  have hinv : (Real.exp u)⁻¹ ≤ (1 + u)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos _) hpos).mpr hexp_ge
  have hden : u / (1 + u) ≤ 1 - Real.exp (-u) := by
    rw [Real.exp_neg]
    calc
      u / (1 + u) = 1 - (1 + u)⁻¹ := by
        field_simp [hpos.ne']
        ring_nf
      _ ≤ 1 - (Real.exp u)⁻¹ := by linarith
  have hhalf : u / 2 ≤ u / (1 + u) := by
    field_simp [hpos.ne']
    nlinarith
  exact hhalf.trans hden

lemma geom_inv_le_exp_eventually {θ c : ℝ} (hθ : 0 < θ) (hc : 0 < c) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      (1 - Real.exp (-(θ * t)))⁻¹ ≤ Real.exp (c / t) := by
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0,
      t ≤ min (1 / θ) (θ * c ^ 2 / 8) :=
    by
      have hnhds : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
          t ≤ min (1 / θ) (θ * c ^ 2 / 8) :=
        Iic_mem_nhds (show (0 : ℝ) < min (1 / θ) (θ * c ^ 2 / 8) by
          exact lt_min (one_div_pos.mpr hθ) (by positivity))
      exact hnhds.filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht ht_small
  have htpos : 0 < t := ht
  have ht_le₁ : t ≤ 1 / θ := ht_small.trans (min_le_left _ _)
  have ht_le₂ : t ≤ θ * c ^ 2 / 8 := ht_small.trans (min_le_right _ _)
  have hu0 : 0 ≤ θ * t := mul_nonneg hθ.le htpos.le
  have hu1 : θ * t ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left ht_le₁ hθ.le
    simpa [one_div, hθ.ne'] using hmul
  have hden_lower : θ * t / 2 ≤ 1 - Real.exp (-(θ * t)) :=
    one_sub_exp_neg_ge_half hu0 hu1
  have hden_pos : 0 < 1 - Real.exp (-(θ * t)) := by
    have hhalf_pos : 0 < θ * t / 2 := by positivity
    exact hhalf_pos.trans_le hden_lower
  have hinv_le : (1 - Real.exp (-(θ * t)))⁻¹ ≤ (θ * t / 2)⁻¹ :=
    (inv_le_inv₀ hden_pos (by positivity : 0 < θ * t / 2)).mpr hden_lower
  have hrat_le : (θ * t / 2)⁻¹ ≤ Real.exp (c / t) := by
    have hx_nonneg : 0 ≤ c / t := by positivity
    have hquad := exp_quadratic_lower hx_nonneg
    have hposct : 0 < c / t := div_pos hc htpos
    have htarget : (θ * t / 2)⁻¹ ≤ (c / t) ^ 2 / 4 := by
      field_simp [hθ.ne', htpos.ne', hc.ne']
      nlinarith [ht_le₂, hθ, hc, htpos, sq_pos_of_pos hc]
    exact htarget.trans hquad
  exact hinv_le.trans hrat_le

lemma exp_sqrt_sub_linear_le
    {B lam t : ℝ} (_hB : 0 ≤ B) (hlam : 0 < lam) (ht : 0 < t) (N : ℕ) :
    B * Real.sqrt (N : ℝ) - t * N
      ≤ B ^ 2 / (4 * lam * t) - (1 - lam) * t * N := by
  let x : ℝ := Real.sqrt (N : ℝ)
  have hx2 : x ^ 2 = (N : ℝ) := by
    dsimp [x]
    exact Real.sq_sqrt (by positivity)
  have hbasic : B * x ≤ lam * t * x ^ 2 + B ^ 2 / (4 * lam * t) := by
    have hsq : 0 ≤ (2 * lam * t * x - B) ^ 2 := sq_nonneg _
    have hden : 0 < 4 * lam * t := by positivity
    have hscaled := div_nonneg hsq hden.le
    have hident :
        (2 * lam * t * x - B) ^ 2 / (4 * lam * t)
          = lam * t * x ^ 2 - B * x + B ^ 2 / (4 * lam * t) := by
      field_simp [hlam.ne', ht.ne']
      ring_nf
    rw [hident] at hscaled
    linarith
  have hbasicN :
      B * Real.sqrt (N : ℝ) ≤ lam * t * (N : ℝ) + B ^ 2 / (4 * lam * t) := by
    simpa [x, hx2] using hbasic
  nlinarith [hbasicN]

lemma exp_sqrt_sub_linear_bound
    {B lam t : ℝ} (hB : 0 ≤ B) (hlam : 0 < lam) (ht : 0 < t) (N : ℕ) :
    Real.exp (B * Real.sqrt (N : ℝ) - t * N)
      ≤ Real.exp (B ^ 2 / (4 * lam * t)) *
        Real.exp (-((1 - lam) * t) * N) := by
  have h := exp_sqrt_sub_linear_le (B := B) (lam := lam) (t := t) hB hlam ht N
  calc
    Real.exp (B * Real.sqrt (N : ℝ) - t * N)
        ≤ Real.exp (B ^ 2 / (4 * lam * t) - (1 - lam) * t * N) :=
          Real.exp_monotone h
    _ = Real.exp (B ^ 2 / (4 * lam * t)) *
        Real.exp (-((1 - lam) * t) * N) := by
      rw [← Real.exp_add]
      ring_nf

lemma exp_sqrt_sub_linear_summable
    {B t : ℝ} (ht : 0 < t) :
    Summable fun N : ℕ => Real.exp (B * Real.sqrt (N : ℝ) - t * N) := by
  by_cases hB : 0 ≤ B
  · have hdom :
        ∀ N : ℕ,
          Real.exp (B * Real.sqrt (N : ℝ) - t * N)
            ≤ Real.exp (B ^ 2 / (4 * ((1 : ℝ) / 2) * t)) *
              Real.exp (-(((1 : ℝ) - (1 : ℝ) / 2) * t) * N) := by
      intro N
      exact exp_sqrt_sub_linear_bound (B := B) (lam := (1 : ℝ) / 2) (t := t) hB
        (by norm_num) ht N
    have hgeom : Summable fun N : ℕ => Real.exp (-(((1 : ℝ) - (1 : ℝ) / 2) * t) * N) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (Real.summable_exp_nat_mul_iff.mpr (by nlinarith [ht] :
          -(((1 : ℝ) - (1 : ℝ) / 2) * t) < 0))
    have hnonneg :
        ∀ N : ℕ, 0 ≤ Real.exp (B * Real.sqrt (N : ℝ) - t * N) :=
      fun N => (Real.exp_pos _).le
    exact (hgeom.mul_left
      (Real.exp (B ^ 2 / (4 * ((1 : ℝ) / 2) * t)))).of_nonneg_of_le hnonneg hdom
  · have hBle : B ≤ 0 := le_of_not_ge hB
    have hdom :
        ∀ N : ℕ,
          Real.exp (B * Real.sqrt (N : ℝ) - t * N)
            ≤ Real.exp (-(t * N)) := by
      intro N
      refine Real.exp_monotone ?_
      have hsqrt_nonneg : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hBle hsqrt_nonneg]
    have hgeom : Summable fun N : ℕ => Real.exp (-(t * N)) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr ht))
    have hnonneg :
        ∀ N : ℕ, 0 ≤ Real.exp (B * Real.sqrt (N : ℝ) - t * N) :=
      fun N => (Real.exp_pos _).le
    exact hgeom.of_nonneg_of_le hnonneg hdom

lemma tsum_exp_neg_mul_nat {r : ℝ} (hr : 0 < r) :
    (∑' N : ℕ, Real.exp (-r * N)) = (1 - Real.exp (-r))⁻¹ := by
  have h0 : 0 ≤ Real.exp (-r) := (Real.exp_pos _).le
  have h1 : Real.exp (-r) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hr)
  have hgeom := tsum_geometric_of_lt_one h0 h1
  calc
    (∑' N : ℕ, Real.exp (-r * N)) = ∑' N : ℕ, (Real.exp (-r)) ^ N := by
      apply tsum_congr
      intro N
      rw [← Real.exp_nat_mul]
      ring_nf
    _ = (1 - Real.exp (-r))⁻¹ := hgeom

lemma exists_lam_for_quadratic_gap {K B : ℝ}
    (hK : 0 < K) (hBsq : B ^ 2 / 4 < K) :
    ∃ lam : ℝ, 0 < lam ∧ lam < 1 ∧ B ^ 2 / (4 * lam) < K := by
  let A : ℝ := B ^ 2 / 4
  let lam : ℝ := (A + K) / (2 * K)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hA_lt : A < K := by simpa [A] using hBsq
  have hden : 0 < 2 * K := by positivity
  have hlam_pos : 0 < lam := by
    dsimp [lam]
    positivity
  have hlam_lt : lam < 1 := by
    dsimp [lam]
    rw [div_lt_one hden]
    nlinarith
  have hsum_pos : 0 < A + K := by positivity
  have hcoef_eq : B ^ 2 / (4 * lam) = (2 * A * K) / (A + K) := by
    dsimp [A, lam]
    field_simp [hK.ne']
  have hcoef_lt : B ^ 2 / (4 * lam) < K := by
    rw [hcoef_eq]
    rw [div_lt_iff₀ hsum_pos]
    nlinarith
  exact ⟨lam, hlam_pos, hlam_lt, hcoef_lt⟩

theorem sqrt_laplace_full_gap_of_sq_lt
    {K B : ℝ} (hK : 0 < K) (hB : 0 ≤ B) (hBsq : B ^ 2 / 4 < K) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ t : ℝ in 𝓝[>] 0,
        (∑' N : ℕ, Real.exp (B * Real.sqrt (N : ℝ) - t * N))
          ≤ Real.exp ((K - ρ) / t) := by
  rcases exists_lam_for_quadratic_gap hK hBsq with ⟨lam, hlam_pos, hlam_lt, hcoef_lt⟩
  let C : ℝ := B ^ 2 / (4 * lam)
  let θ : ℝ := 1 - lam
  have hθ : 0 < θ := by
    dsimp [θ]
    exact sub_pos.mpr hlam_lt
  let ρ : ℝ := (K - C) / 2
  have hρ : 0 < ρ := by
    dsimp [ρ, C]
    linarith
  refine ⟨ρ, hρ, ?_⟩
  have hgeom_event := geom_inv_le_exp_eventually hθ hρ
  filter_upwards [self_mem_nhdsWithin, hgeom_event] with t ht hgeom_inv
  have htpos : 0 < t := ht
  have hdom :
      ∀ N : ℕ,
        Real.exp (B * Real.sqrt (N : ℝ) - t * N)
          ≤ Real.exp (C / t) * Real.exp (-(θ * t) * N) := by
    intro N
    have h0 := exp_sqrt_sub_linear_bound (B := B) (lam := lam) (t := t) hB hlam_pos htpos N
    have hC :
        B ^ 2 / (4 * lam * t) = C / t := by
      dsimp [C]
      field_simp [hlam_pos.ne', htpos.ne']
    have hθeq :
        -((1 - lam) * t) * (N : ℝ) = -(θ * t) * (N : ℝ) := by
      dsimp [θ]
    simpa [hC, hθeq] using h0
  have hgeom_summable : Summable fun N : ℕ => Real.exp (-(θ * t) * N) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Real.summable_exp_nat_mul_iff.mpr (by nlinarith [hθ, htpos] : -(θ * t) < 0))
  have hmajor_summable :
      Summable fun N : ℕ => Real.exp (C / t) * Real.exp (-(θ * t) * N) :=
    hgeom_summable.mul_left (Real.exp (C / t))
  have hleft_summable :
      Summable fun N : ℕ => Real.exp (B * Real.sqrt (N : ℝ) - t * N) :=
    hmajor_summable.of_nonneg_of_le (fun N => (Real.exp_pos _).le) hdom
  calc
    (∑' N : ℕ, Real.exp (B * Real.sqrt (N : ℝ) - t * N))
        ≤ ∑' N : ℕ, Real.exp (C / t) * Real.exp (-(θ * t) * N) :=
          hleft_summable.tsum_le_tsum hdom hmajor_summable
    _ = Real.exp (C / t) * (∑' N : ℕ, Real.exp (-(θ * t) * N)) := by
          rw [tsum_mul_left]
    _ = Real.exp (C / t) * (1 - Real.exp (-(θ * t)))⁻¹ := by
          rw [tsum_exp_neg_mul_nat (mul_pos hθ htpos)]
    _ ≤ Real.exp (C / t) * Real.exp (ρ / t) := by
          exact mul_le_mul_of_nonneg_left hgeom_inv (Real.exp_pos _).le
    _ = Real.exp ((K - ρ) / t) := by
          rw [← Real.exp_add]
          dsimp [ρ, C]
          field_simp [htpos.ne']
          ring_nf

lemma sq_div_four_lt_of_nonneg_lt_two_sqrt
    {K B : ℝ} (hK : 0 < K) (hB0 : 0 ≤ B)
    (hBlt : B < 2 * Real.sqrt K) :
    B ^ 2 / 4 < K := by
  have hsqrt_nonneg : 0 ≤ 2 * Real.sqrt K := by positivity
  have hsq : B ^ 2 < (2 * Real.sqrt K) ^ 2 :=
    (sq_lt_sq₀ hB0 hsqrt_nonneg).mpr hBlt
  rw [mul_pow, Real.sq_sqrt hK.le] at hsq
  nlinarith

theorem sqrt_laplace_full_gap
    {K B : ℝ} (hK : 0 < K) (hBlt : B < 2 * Real.sqrt K) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ t : ℝ in 𝓝[>] 0,
        (∑' N : ℕ, Real.exp (B * Real.sqrt (N : ℝ) - t * N))
          ≤ Real.exp ((K - ρ) / t) := by
  by_cases hB0 : 0 ≤ B
  · exact sqrt_laplace_full_gap_of_sq_lt hK hB0
      (sq_div_four_lt_of_nonneg_lt_two_sqrt hK hB0 hBlt)
  · have hBle : B ≤ 0 := le_of_not_ge hB0
    rcases sqrt_laplace_full_gap_of_sq_lt (B := 0) hK (by norm_num)
        (by simpa using hK) with ⟨ρ, hρ, hEv⟩
    refine ⟨ρ, hρ, ?_⟩
    filter_upwards [self_mem_nhdsWithin, hEv] with t ht hsum
    have htpos : 0 < t := ht
    have hdom :
        ∀ N : ℕ,
          Real.exp (B * Real.sqrt (N : ℝ) - t * N)
            ≤ Real.exp (0 * Real.sqrt (N : ℝ) - t * N) := by
      intro N
      refine Real.exp_monotone ?_
      have hsqrt_nonneg : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hBle hsqrt_nonneg]
    have hleft : Summable fun N : ℕ => Real.exp (B * Real.sqrt (N : ℝ) - t * N) :=
      exp_sqrt_sub_linear_summable htpos
    have hright : Summable fun N : ℕ => Real.exp (0 * Real.sqrt (N : ℝ) - t * N) :=
      exp_sqrt_sub_linear_summable (B := 0) htpos
    exact (hleft.tsum_le_tsum hdom hright).trans hsum

theorem sqrt_laplace_bad_inside_gap
    {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ t : ℝ in 𝓝[>] 0,
        (1 - Real.exp (-t))
          *
        (∑' N : ℕ,
          Real.exp ((2 * Real.sqrt K - ε) * Real.sqrt (N : ℝ) - t * N))
        ≤ Real.exp ((K - ρ) / t) := by
  have hBlt : 2 * Real.sqrt K - ε < 2 * Real.sqrt K := by linarith
  rcases sqrt_laplace_full_gap (K := K) (B := 2 * Real.sqrt K - ε) hK hBlt with
    ⟨ρ, hρ, hEv⟩
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hEv] with t ht hsum
  have hfac_le : 1 - Real.exp (-t) ≤ 1 := by
    linarith [Real.exp_pos (-t)]
  have htsum_nonneg :
      0 ≤ ∑' N : ℕ,
        Real.exp ((2 * Real.sqrt K - ε) * Real.sqrt (N : ℝ) - t * N) :=
    tsum_nonneg fun N => (Real.exp_pos _).le
  have hprod_le :
      (1 - Real.exp (-t))
          *
        (∑' N : ℕ,
          Real.exp ((2 * Real.sqrt K - ε) * Real.sqrt (N : ℝ) - t * N))
        ≤
        (∑' N : ℕ,
          Real.exp ((2 * Real.sqrt K - ε) * Real.sqrt (N : ℝ) - t * N)) := by
    simpa using mul_le_mul_of_nonneg_right hfac_le htsum_nonneg
  exact hprod_le.trans hsum

theorem sqrt_laplace_restricted_gap
    {K B δ : ℝ} (hK : 0 < K) (_hδ : 0 < δ)
    (hBlt : B < 2 * Real.sqrt K) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ t : ℝ in 𝓝[>] 0,
        (1 - Real.exp (-t))
          *
        (∑' N : ℕ,
          if (1 - δ) * K / t ^ 2 ≤ (N : ℝ)
             ∧ (N : ℝ) ≤ (1 + δ) * K / t ^ 2
          then 0
          else Real.exp (B * Real.sqrt (N : ℝ) - t * N))
        ≤ Real.exp ((K - ρ) / t) := by
  rcases sqrt_laplace_full_gap (K := K) (B := B) hK hBlt with ⟨ρ, hρ, hEv⟩
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hEv] with t ht hfull
  have htpos : 0 < t := ht
  let rterm : ℕ → ℝ := fun N =>
    if (1 - δ) * K / t ^ 2 ≤ (N : ℝ)
       ∧ (N : ℝ) ≤ (1 + δ) * K / t ^ 2
    then 0
    else Real.exp (B * Real.sqrt (N : ℝ) - t * N)
  have hr_nonneg : ∀ N, 0 ≤ rterm N := by
    intro N
    dsimp [rterm]
    split <;> positivity
  have hr_le :
      ∀ N, rterm N ≤ Real.exp (B * Real.sqrt (N : ℝ) - t * N) := by
    intro N
    dsimp [rterm]
    split
    · exact (Real.exp_pos _).le
    · exact le_rfl
  have hfull_summable :
      Summable fun N : ℕ => Real.exp (B * Real.sqrt (N : ℝ) - t * N) :=
    exp_sqrt_sub_linear_summable htpos
  have hr_summable : Summable rterm :=
    hfull_summable.of_nonneg_of_le hr_nonneg hr_le
  have htsum_le :
      (∑' N : ℕ, rterm N)
        ≤ ∑' N : ℕ, Real.exp (B * Real.sqrt (N : ℝ) - t * N) :=
    hr_summable.tsum_le_tsum hr_le hfull_summable
  have hfac_le : 1 - Real.exp (-t) ≤ 1 := by
    linarith [Real.exp_pos (-t)]
  have htsum_nonneg : 0 ≤ ∑' N : ℕ, rterm N :=
    tsum_nonneg hr_nonneg
  have hprod_le :
      (1 - Real.exp (-t)) * (∑' N : ℕ, rterm N) ≤ ∑' N : ℕ, rterm N := by
    simpa using mul_le_mul_of_nonneg_right hfac_le htsum_nonneg
  calc
    (1 - Real.exp (-t)) * (∑' N : ℕ, rterm N)
        ≤ ∑' N : ℕ, rterm N := hprod_le
    _ ≤ ∑' N : ℕ, Real.exp (B * Real.sqrt (N : ℝ) - t * N) := htsum_le
    _ ≤ Real.exp ((K - ρ) / t) := hfull

lemma log_Cum_le_laplace
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (ha0 : 0 < a 0)
    {t : ℝ} (ht : 0 < t)
    (hsum : Summable fun n : ℕ => a n * Real.exp (-(t * n)))
    (N : ℕ) :
    Real.log (Cum a N)
      ≤ t * N + Real.log (∑' n : ℕ, a n * Real.exp (-(t * n))) := by
  have hcum_pos : 0 < Cum a N := Cum_pos_of_pos_zero ha ha0 N
  have hleft_pos : 0 < Cum a N * Real.exp (-(t * N)) :=
    mul_pos hcum_pos (Real.exp_pos _)
  have hle := Cum_mul_exp_le_laplace_tsum ha ht hsum N
  have hlogle := Real.log_le_log hleft_pos hle
  have hexp_ne : Real.exp (-(t * (N : ℝ))) ≠ 0 := (Real.exp_pos _).ne'
  have hcum_ne : Cum a N ≠ 0 := hcum_pos.ne'
  rw [Real.log_mul hcum_ne hexp_ne, Real.log_exp] at hlogle
  nlinarith

end

end AnalyticCombinatorics.Ch8.Partitions.Tauberian
