import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.BarrierHarmonic

/-!
# Boundedness of `u` by barrier induction (R6 lemmas 8–12, conditional)

Strong induction on the Erdős recurrence against super/subharmonic barriers:

* `u_upper_of_superharmonic` — if the upper barrier is superharmonic (with positive values)
  then `u n ≤ M·H₊(n)` for all `n`, hence `u` is eventually bounded above;
* `u_lower_of_subharmonic` — if the lower barrier is subharmonic then `c·H₋(n) ≤ u n` for
  all `n ≥ 1`, hence `liminf u > 0`.

Both take the harmonic inequality as a hypothesis (supplied conditionally-on-rate by
`BarrierHarmonic`; unconditionally once the mass-rate brick lands).  Opus-authored.
-/

set_option maxHeartbeats 800000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `u` is positive for `n ≥ 1` (R6 lemma 10). -/
lemma u_pos {n : ℕ} (hn : 1 ≤ n) : 0 < u n := by
  rw [u]
  have h1 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h2 := Partitions.part_pos n
  have h3 : (0 : ℝ) < Real.exp (-C * Real.sqrt (n : ℝ)) := Real.exp_pos _
  positivity

/-- `u 0 = 0`. -/
lemma u_zero : u 0 = 0 := by
  rw [u]
  norm_num

/--
**Upper boundedness by barrier induction** (R6 lemma 8): a globally positive superharmonic
upper barrier dominates `u` up to a constant.
-/
theorem u_upper_of_superharmonic {A E δ : ℝ} (hA : 0 < A) (hE : 3 ≤ E) (hδ : 0 < δ)
    (hpos : ∀ k : ℕ, 0 < upperBarrier A E k)
    (hsuper : ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * upperBarrier A E (n - m))
        ≤ upperBarrier A E n - δ * barrierSlack E n) :
    ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ, u n ≤ M * upperBarrier A E n := by
  classical
  -- threshold where superharmonicity + boundary control + n ≥ 2 all hold
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hsuper
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (boundaryTerm_le_barrierSlack hE hδ)
  set N₀ : ℕ := max (max N₁ N₂) 2 with hN₀def
  -- M covers the initial segment and is ≥ 1
  have hne_range : (Finset.range (N₀ + 1)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
  set M₀ : ℝ := (Finset.range (N₀ + 1)).sup' hne_range
    (fun k => u k / upperBarrier A E k) with hM₀def
  set M : ℝ := max M₀ 1 with hMdef
  have hM1 : (1 : ℝ) ≤ M := le_max_right _ _
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
  refine ⟨M, hMpos, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hsmall : n ≤ N₀
    · -- initial segment: M ≥ u n / H₊ n
      have hmem : n ∈ Finset.range (N₀ + 1) := Finset.mem_range.mpr (by omega)
      have hsup : u n / upperBarrier A E n ≤ M₀ :=
        Finset.le_sup' (fun k => u k / upperBarrier A E k) hmem
      have hHpos := hpos n
      have : u n / upperBarrier A E n ≤ M := le_trans hsup (le_max_left _ _)
      calc u n = (u n / upperBarrier A E n) * upperBarrier A E n := by
            field_simp
        _ ≤ M * upperBarrier A E n :=
            mul_le_mul_of_nonneg_right this hHpos.le
    · -- inductive step via the recurrence
      push_neg at hsmall
      have hn2 : 2 ≤ n := by omega
      have hnN₁ : N₁ ≤ n := by omega
      have hnN₂ : N₂ ≤ n := by omega
      have hrec := u_recurrence n hn2
      have hsup_n := hN₁ n hnN₁
      have hbdy_n := hN₂ n hnN₂
      -- termwise IH: u (n−m) ≤ M·H₊(n−m) for m ∈ Icc 1 (n−1)
      have hterm : (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * u (n - m))
          ≤ ∑ m ∈ Finset.Icc 1 (n - 1),
              erdosWeight n m * (M * upperBarrier A E (n - m)) := by
        refine Finset.sum_le_sum ?_
        intro m hm
        have hW : 0 ≤ erdosWeight n m := erdosWeight_nonneg_of_mem hm
        obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
        have hlt : n - m < n := by omega
        exact mul_le_mul_of_nonneg_left (ih (n - m) hlt) hW
      have hfactor : (∑ m ∈ Finset.Icc 1 (n - 1),
          erdosWeight n m * (M * upperBarrier A E (n - m)))
          = M * ∑ m ∈ Finset.Icc 1 (n - 1),
              erdosWeight n m * upperBarrier A E (n - m) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro m _hm
        ring
      calc u n = (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * u (n - m))
            + boundaryTerm n := hrec
        _ ≤ (∑ m ∈ Finset.Icc 1 (n - 1),
              erdosWeight n m * (M * upperBarrier A E (n - m)))
            + boundaryTerm n := by linarith [hterm]
        _ = M * (∑ m ∈ Finset.Icc 1 (n - 1),
              erdosWeight n m * upperBarrier A E (n - m))
            + boundaryTerm n := by rw [hfactor]
        _ ≤ M * (upperBarrier A E n - δ * barrierSlack E n)
            + δ * barrierSlack E n := by
            have h1 := mul_le_mul_of_nonneg_left hsup_n hMpos.le
            linarith [h1, hbdy_n]
        _ ≤ M * upperBarrier A E n := by
            have hslack_nonneg : 0 ≤ δ * barrierSlack E n := by
              -- δ > 0 and slack ≥ 0 for n in this regime (n ≥ 2)
              have h1 : (1 : ℝ) < (n : ℝ) + E := by
                have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
                linarith
              have hlog : 0 < Real.log ((n : ℝ) + E) := Real.log_pos h1
              have hs : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
              rw [barrierSlack]
              positivity
            nlinarith [hslack_nonneg, hM1]

/-- Eventual upper bound (R6 lemma 9): `u n ≤ M` eventually. -/
theorem u_limsup_finite_of_superharmonic {A E δ : ℝ} (hA : 0 < A) (hE : 3 ≤ E) (hδ : 0 < δ)
    (hpos : ∀ k : ℕ, 0 < upperBarrier A E k)
    (hsuper : ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * upperBarrier A E (n - m))
        ≤ upperBarrier A E n - δ * barrierSlack E n) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in atTop, u n ≤ M := by
  obtain ⟨M, hMpos, hM⟩ := u_upper_of_superharmonic hA hE hδ hpos hsuper
  refine ⟨M, hMpos, ?_⟩
  filter_upwards with n
  calc u n ≤ M * upperBarrier A E n := hM n
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left (upperBarrier_le_one hA hE n) hMpos.le
    _ = M := mul_one M

/--
**Lower bound by barrier induction** (R6 lemma 11): a subharmonic lower barrier
supports `u` from below up to a constant, for all `n ≥ 1`.
-/
theorem u_lower_of_subharmonic {A E δ : ℝ} (hA : 0 < A) (hE : 3 ≤ E) (hδ : 0 < δ)
    (hsub : ∀ᶠ n : ℕ in atTop,
      lowerBarrier A E n + δ * barrierSlack E n
        ≤ (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * lowerBarrier A E (n - m))) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → c * lowerBarrier A E n ≤ u n := by
  classical
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hsub
  set N₀ : ℕ := max N₁ 2 with hN₀def
  -- c below the initial segment ratios; H₋ ∈ [1, 1+A] always (E ≥ 3)
  have hH_ge_one : ∀ k : ℕ, 1 ≤ lowerBarrier A E k := by
    intro k
    rw [lowerBarrier]
    have h1 : (1 : ℝ) < (k : ℝ) + E := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hlog : 0 < Real.log ((k : ℝ) + E) := Real.log_pos h1
    have : 0 ≤ A / Real.log ((k : ℝ) + E) := by positivity
    linarith
  have hH_pos : ∀ k : ℕ, 0 < lowerBarrier A E k := fun k =>
    lt_of_lt_of_le one_pos (hH_ge_one k)
  -- min of u k / H₋ k over 1 ≤ k ≤ N₀, capped by 1... use inf'
  have hne : ((Finset.Icc 1 N₀)).Nonempty := by
    refine ⟨1, Finset.mem_Icc.mpr ⟨le_refl 1, ?_⟩⟩
    omega
  set c₀ : ℝ := (Finset.Icc 1 N₀).inf' hne (fun k => u k / lowerBarrier A E k) with hc₀def
  have hc₀pos : 0 < c₀ := by
    rw [hc₀def]
    apply Finset.lt_inf'_iff hne (a := (0:ℝ)) |>.mpr
    intro k hk
    obtain ⟨hk1, _⟩ := Finset.mem_Icc.mp hk
    exact div_pos (u_pos hk1) (hH_pos k)
  set c : ℝ := min c₀ 1 with hcdef
  have hcpos : 0 < c := lt_min hc₀pos one_pos
  have hc1 : c ≤ 1 := min_le_right _ _
  refine ⟨c, hcpos, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn1
    by_cases hsmall : n ≤ N₀
    · -- initial segment
      have hmem : n ∈ Finset.Icc 1 N₀ := Finset.mem_Icc.mpr ⟨hn1, hsmall⟩
      have hinf : c₀ ≤ u n / lowerBarrier A E n :=
        Finset.inf'_le (fun k => u k / lowerBarrier A E k) hmem
      have hcle : c ≤ u n / lowerBarrier A E n := le_trans (min_le_left _ _) hinf
      have hHpos := hH_pos n
      calc c * lowerBarrier A E n
          ≤ (u n / lowerBarrier A E n) * lowerBarrier A E n :=
            mul_le_mul_of_nonneg_right hcle hHpos.le
        _ = u n := by field_simp
    · push_neg at hsmall
      have hn2 : 2 ≤ n := by omega
      have hnN₁ : N₁ ≤ n := by omega
      have hrec := u_recurrence n hn2
      have hsub_n := hN₁ n hnN₁
      -- termwise IH (all n−m ∈ [1, n−1])
      have hterm : (∑ m ∈ Finset.Icc 1 (n - 1),
          erdosWeight n m * (c * lowerBarrier A E (n - m)))
          ≤ ∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * u (n - m) := by
        refine Finset.sum_le_sum ?_
        intro m hm
        have hW : 0 ≤ erdosWeight n m := erdosWeight_nonneg_of_mem hm
        obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
        have hlt : n - m < n := by omega
        have hge1 : 1 ≤ n - m := by omega
        exact mul_le_mul_of_nonneg_left (ih (n - m) hlt hge1) hW
      have hfactor : (∑ m ∈ Finset.Icc 1 (n - 1),
          erdosWeight n m * (c * lowerBarrier A E (n - m)))
          = c * ∑ m ∈ Finset.Icc 1 (n - 1),
              erdosWeight n m * lowerBarrier A E (n - m) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro m _hm
        ring
      have hbdy : 0 ≤ boundaryTerm n := boundaryTerm_nonneg n
      have hslack_nonneg : 0 ≤ δ * barrierSlack E n := by
        have h1 : (1 : ℝ) < (n : ℝ) + E := by
          have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
          linarith
        have hlog : 0 < Real.log ((n : ℝ) + E) := Real.log_pos h1
        have hs : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
        rw [barrierSlack]
        positivity
      calc c * lowerBarrier A E n
          ≤ c * (lowerBarrier A E n + δ * barrierSlack E n) := by nlinarith
        _ ≤ c * (∑ m ∈ Finset.Icc 1 (n - 1),
              erdosWeight n m * lowerBarrier A E (n - m)) :=
            mul_le_mul_of_nonneg_left hsub_n hcpos.le
        _ = ∑ m ∈ Finset.Icc 1 (n - 1),
              erdosWeight n m * (c * lowerBarrier A E (n - m)) := by
            rw [hfactor]
        _ ≤ ∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * u (n - m) := hterm
        _ ≤ (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * u (n - m))
            + boundaryTerm n := by linarith
        _ = u n := hrec.symm

/-- Positive liminf (R6 lemma 12): `c ≤ u n` eventually. -/
theorem u_liminf_positive_of_subharmonic {A E δ : ℝ} (hA : 0 < A) (hE : 3 ≤ E) (hδ : 0 < δ)
    (hsub : ∀ᶠ n : ℕ in atTop,
      lowerBarrier A E n + δ * barrierSlack E n
        ≤ (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * lowerBarrier A E (n - m))) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c ≤ u n := by
  obtain ⟨c, hcpos, hc⟩ := u_lower_of_subharmonic hA hE hδ hsub
  refine ⟨c, hcpos, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn1
  have hH := hc n hn1
  have hH1 : 1 ≤ lowerBarrier A E n := by
    rw [lowerBarrier]
    have h1 : (1 : ℝ) < (n : ℝ) + E := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hlog : 0 < Real.log ((n : ℝ) + E) := Real.log_pos h1
    have : 0 ≤ A / Real.log ((n : ℝ) + E) := by positivity
    linarith
  calc c = c * 1 := (mul_one c).symm
    _ ≤ c * lowerBarrier A E n := mul_le_mul_of_nonneg_left hH1 hcpos.le
    _ ≤ u n := hH

end AnalyticCombinatorics.Ch8.Partitions.Erdos
