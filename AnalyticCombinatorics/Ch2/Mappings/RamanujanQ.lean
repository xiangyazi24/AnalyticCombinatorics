import Mathlib

/-!
# Ramanujan's Q-function for random mappings

This file defines the finite Ramanujan Q-function from Flajolet--Sedgewick,
Chapter II.3.  The intended asymptotic is

`Q(n) ~ sqrt (pi * n / 2)`.

The full Laplace-method asymptotic is not yet present in Mathlib.  This file
records the faithful finite definition and elementary verified bounds that are
used by that proof.
-/

open Filter Asymptotics
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

noncomputable section

/-- The `k`-th summand in Ramanujan's Q-function.  The empty product is `1`. -/
def ramanujanQTerm (n k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k, (1 - (((j + 1 : ℕ) : ℝ) / (n : ℝ)))

/--
Ramanujan's Q-function:

`Q(n) = 1 + (1 - 1/n) + (1 - 1/n)(1 - 2/n) + ...`.

For `n = 0` the finite sum is empty, which is harmless for asymptotic uses.
-/
def ramanujanQ (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, ramanujanQTerm n k

/-- The Gaussian kernel that dominates the summands of `ramanujanQ`. -/
def gaussianKernel (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-((n : ℝ)⁻¹ * 2⁻¹ * x ^ 2))

@[simp] lemma ramanujanQ_zero : ramanujanQ 0 = 0 := by
  simp [ramanujanQ]

@[simp] lemma ramanujanQTerm_zero (n : ℕ) : ramanujanQTerm n 0 = 1 := by
  simp [ramanujanQTerm]

lemma sum_range_succ_cast (k : ℕ) :
    (∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ))) =
      (k : ℝ) * ((k : ℝ) + 1) / 2 := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      norm_num [Nat.cast_add, Nat.cast_succ]
      ring

lemma sum_range_succ_cast_div (k n : ℕ) :
    (∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / (n : ℝ))) =
      ((k : ℝ) * ((k : ℝ) + 1) / 2) / (n : ℝ) := by
  rw [← Finset.sum_div, sum_range_succ_cast]

lemma ramanujanQTerm_nonneg {n k : ℕ} (hk : k ≤ n) :
    0 ≤ ramanujanQTerm n k := by
  classical
  unfold ramanujanQTerm
  refine Finset.prod_nonneg ?_
  intro j hj
  have hjk : j + 1 ≤ k := Finset.mem_range.mp hj
  have hjn : j + 1 ≤ n := hjk.trans hk
  by_cases hn : n = 0
  · subst hn
    have : j + 1 ≤ 0 := hjn
    omega
  have hnpos_nat : 0 < n := Nat.pos_of_ne_zero hn
  have hle : (((j + 1 : ℕ) : ℝ) / (n : ℝ)) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hnpos_nat)]
    exact_mod_cast hjn
  linarith

lemma ramanujanQTerm_factor_le_exp {n k j : ℕ} (_hk : k ≤ n) (_hj : j ∈ Finset.range k) :
    1 - (((j + 1 : ℕ) : ℝ) / (n : ℝ)) ≤
      Real.exp (-(((j + 1 : ℕ) : ℝ) / (n : ℝ))) := by
  have h := Real.add_one_le_exp (-(((j + 1 : ℕ) : ℝ) / (n : ℝ)))
  linarith

lemma ramanujanQTerm_le_exp_sum {n k : ℕ} (hk : k ≤ n) :
    ramanujanQTerm n k ≤
      Real.exp (-(∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / (n : ℝ)))) := by
  classical
  unfold ramanujanQTerm
  calc
    (∏ j ∈ Finset.range k, (1 - (((j + 1 : ℕ) : ℝ) / (n : ℝ)))) ≤
        ∏ j ∈ Finset.range k, Real.exp (-(((j + 1 : ℕ) : ℝ) / (n : ℝ))) := by
      refine Finset.prod_le_prod ?_ ?_
      · intro j hj
        have hjk : j + 1 ≤ k := Finset.mem_range.mp hj
        have hjn : j + 1 ≤ n := hjk.trans hk
        by_cases hn : n = 0
        · subst hn
          have : j + 1 ≤ 0 := hjn
          omega
        have hnpos_nat : 0 < n := Nat.pos_of_ne_zero hn
        have hle : (((j + 1 : ℕ) : ℝ) / (n : ℝ)) ≤ 1 := by
          rw [div_le_one (by exact_mod_cast hnpos_nat)]
          exact_mod_cast hjn
        linarith
      · intro j hj
        exact ramanujanQTerm_factor_le_exp hk hj
    _ = Real.exp (∑ j ∈ Finset.range k, -(((j + 1 : ℕ) : ℝ) / (n : ℝ))) := by
      rw [Real.exp_sum]
    _ = Real.exp (-(∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / (n : ℝ)))) := by
      rw [Finset.sum_neg_distrib]

lemma ramanujanQTerm_le_exp_quadratic {n k : ℕ} (hk : k ≤ n) :
    ramanujanQTerm n k ≤
      Real.exp (-(((k : ℝ) * ((k : ℝ) + 1) / 2) / (n : ℝ))) := by
  have hsum :
      (∑ j ∈ Finset.range k, (((j : ℝ) + 1) / (n : ℝ))) =
        ((k : ℝ) * ((k : ℝ) + 1) / 2) / (n : ℝ) := by
    simpa [Nat.cast_add] using sum_range_succ_cast_div k n
  simpa [Nat.cast_add, hsum] using ramanujanQTerm_le_exp_sum (n := n) (k := k) hk

lemma ramanujanQTerm_le_one {n k : ℕ} (hk : k ≤ n) :
    ramanujanQTerm n k ≤ 1 := by
  have h := ramanujanQTerm_le_exp_sum (n := n) (k := k) hk
  have hsum_nonneg : 0 ≤ ∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / (n : ℝ)) := by
    refine Finset.sum_nonneg ?_
    intro j hj
    by_cases hn : n = 0
    · subst hn
      simp
    exact div_nonneg (by positivity) (by positivity)
  have hexp : Real.exp (-(∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / (n : ℝ)))) ≤ 1 := by
    rw [← Real.exp_zero, Real.exp_le_exp]
    linarith
  exact h.trans hexp

lemma ramanujanQ_nonneg (n : ℕ) : 0 ≤ ramanujanQ n := by
  unfold ramanujanQ
  refine Finset.sum_nonneg ?_
  intro k hk
  exact ramanujanQTerm_nonneg (Nat.le_of_lt (Finset.mem_range.mp hk))

/-- A crude universal upper bound: every summand is at most `1`. -/
theorem ramanujanQ_le_n (n : ℕ) : ramanujanQ n ≤ n := by
  unfold ramanujanQ
  calc
    (∑ k ∈ Finset.range n, ramanujanQTerm n k) ≤
        ∑ _k ∈ Finset.range n, (1 : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro k hk
      exact ramanujanQTerm_le_one (Nat.le_of_lt (Finset.mem_range.mp hk))
    _ = n := by simp

/--
Sharp one-sided Gaussian envelope for each summand.  This is the main elementary
estimate needed for the upper half of the Laplace comparison.
-/
theorem ramanujanQTerm_gaussian_envelope {n k : ℕ} (hk : k ≤ n) :
    ramanujanQTerm n k ≤
      Real.exp (-(((k : ℝ) * ((k : ℝ) + 1) / 2) / (n : ℝ))) :=
  ramanujanQTerm_le_exp_quadratic hk

lemma prod_one_sub_ge_one_sub_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  classical
  revert h0 h1
  refine Finset.induction_on s ?_ ?_
  · intro _h0 _h1
    simp
  · intro a s ha ih h0 h1
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have ih' : 1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
      exact ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have hprod_le_one : ∏ i ∈ s, (1 - f i) ≤ 1 := by
      refine Finset.prod_le_one ?_ ?_
      · intro i hi
        have : f i ≤ 1 := h1 i (Finset.mem_insert_of_mem hi)
        linarith
      · intro i hi
        have : 0 ≤ f i := h0 i (Finset.mem_insert_of_mem hi)
        linarith
    have hfa_nonneg : 0 ≤ f a := h0 a (Finset.mem_insert_self a s)
    calc
      1 - (f a + ∑ i ∈ s, f i) = 1 - ∑ i ∈ s, f i - f a := by ring
      _ ≤ (∏ i ∈ s, (1 - f i)) - f a := by linarith
      _ ≤ (∏ i ∈ s, (1 - f i)) - f a * (∏ i ∈ s, (1 - f i)) := by
        have hmul : f a * (∏ i ∈ s, (1 - f i)) ≤ f a * 1 :=
          mul_le_mul_of_nonneg_left hprod_le_one hfa_nonneg
        linarith
      _ = (1 - f a) * ∏ i ∈ s, (1 - f i) := by ring

lemma one_sub_sum_le_ramanujanQTerm {n k : ℕ} (hk : k ≤ n) :
    1 - (∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / (n : ℝ))) ≤
      ramanujanQTerm n k := by
  classical
  unfold ramanujanQTerm
  refine prod_one_sub_ge_one_sub_sum (Finset.range k)
    (fun j => (((j + 1 : ℕ) : ℝ) / (n : ℝ))) ?_ ?_
  · intro j hj
    by_cases hn : n = 0
    · subst hn
      simp
    exact div_nonneg (by positivity) (by positivity)
  · intro j hj
    have hjk : j + 1 ≤ k := Finset.mem_range.mp hj
    have hjn : j + 1 ≤ n := hjk.trans hk
    by_cases hn : n = 0
    · subst hn
      have : j + 1 ≤ 0 := hjn
      omega
    have hnpos_nat : 0 < n := Nat.pos_of_ne_zero hn
    rw [div_le_one (by exact_mod_cast hnpos_nat)]
    exact_mod_cast hjn

lemma ramanujanQTerm_ge_half_of_lt_sqrt {n k : ℕ} (hk : k < Nat.sqrt n) :
    (1 / 2 : ℝ) ≤ ramanujanQTerm n k := by
  have hk_sqrt : k ≤ Nat.sqrt n := le_of_lt hk
  have hk_succ_sqrt : k + 1 ≤ Nat.sqrt n := Nat.succ_le_of_lt hk
  have hmul_nat : k * (k + 1) ≤ n := by
    calc
      k * (k + 1) ≤ Nat.sqrt n * Nat.sqrt n :=
        Nat.mul_le_mul hk_sqrt hk_succ_sqrt
      _ ≤ n := Nat.sqrt_le n
  have hnpos : 0 < n := by
    have : 0 < Nat.sqrt n := lt_of_le_of_lt (Nat.zero_le k) hk
    exact (Nat.sqrt_pos).mp this
  have hsum_le :
      (∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / (n : ℝ))) ≤ 1 / 2 := by
    rw [sum_range_succ_cast_div]
    have hnpos_real : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hmul_real : (k : ℝ) * ((k : ℝ) + 1) ≤ (n : ℝ) := by
      exact_mod_cast hmul_nat
    field_simp [hnpos_real.ne']
    nlinarith
  have hterm := one_sub_sum_le_ramanujanQTerm (n := n) (k := k)
    (le_trans hk_sqrt (Nat.sqrt_le_self n))
  linarith

/-- A crude but useful lower bound from the first `sqrt n` summands. -/
theorem half_nat_sqrt_le_ramanujanQ (n : ℕ) :
    ((Nat.sqrt n : ℝ) / 2) ≤ ramanujanQ n := by
  unfold ramanujanQ
  have hsubset : Finset.range (Nat.sqrt n) ⊆ Finset.range n := by
    intro k hk
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) (Nat.sqrt_le_self n))
  calc
    ((Nat.sqrt n : ℝ) / 2) =
        ∑ _k ∈ Finset.range (Nat.sqrt n), (1 / 2 : ℝ) := by
      simp [div_eq_mul_inv]
    _ ≤ ∑ k ∈ Finset.range (Nat.sqrt n), ramanujanQTerm n k := by
      refine Finset.sum_le_sum ?_
      intro k hk
      exact ramanujanQTerm_ge_half_of_lt_sqrt (Finset.mem_range.mp hk)
    _ ≤ ∑ k ∈ Finset.range n, ramanujanQTerm n k := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
      intro k hk _hnot
      exact ramanujanQTerm_nonneg (Nat.le_of_lt (Finset.mem_range.mp hk))

theorem eventually_sqrt_div_four_le_ramanujanQ :
    ∀ᶠ n : ℕ in atTop, Real.sqrt (n : ℝ) / 4 ≤ ramanujanQ n := by
  refine eventually_atTop.2 ⟨4, ?_⟩
  intro n hn
  have hfloor := half_nat_sqrt_le_ramanujanQ n
  have hs2 : 2 ≤ Nat.sqrt n := by
    rw [Nat.le_sqrt]
    omega
  have hs_real : Real.sqrt (n : ℝ) ≤ 2 * (Nat.sqrt n : ℝ) := by
    have hsqrtle : Real.sqrt (n : ℝ) ≤ Nat.sqrt n + 1 :=
      Real.real_sqrt_le_nat_sqrt_succ
    have htwo : ((Nat.sqrt n : ℝ) + 1) ≤ 2 * (Nat.sqrt n : ℝ) := by
      have : (1 : ℝ) ≤ Nat.sqrt n := by
        exact_mod_cast (show 1 ≤ Nat.sqrt n from le_trans (by decide) hs2)
      linarith
    exact hsqrtle.trans htwo
  linarith

lemma gaussianKernel_antitoneOn {n : ℕ} (hn : 0 < n) (a : ℝ) :
    AntitoneOn (gaussianKernel n) (Set.Icc 0 a) := by
  intro x hx y hy hxy
  rw [gaussianKernel, gaussianKernel, Real.exp_le_exp]
  have hb_nonneg : 0 ≤ (n : ℝ)⁻¹ * 2⁻¹ := by positivity
  have hsq : x ^ 2 ≤ y ^ 2 := (sq_le_sq₀ hx.1 hy.1).2 hxy
  have hmul : ((n : ℝ)⁻¹ * 2⁻¹) * x ^ 2 ≤
      ((n : ℝ)⁻¹ * 2⁻¹) * y ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hb_nonneg
  linarith

lemma ramanujanQTerm_le_gaussianKernel {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    ramanujanQTerm n k ≤ gaussianKernel n k := by
  have hterm := ramanujanQTerm_le_exp_quadratic (n := n) (k := k) hk
  have hquad :
      -(((k : ℝ) * ((k : ℝ) + 1) / 2) / (n : ℝ)) ≤
        -((n : ℝ)⁻¹ * 2⁻¹ * (k : ℝ) ^ 2) := by
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
    have hsquare : (k : ℝ) ^ 2 ≤ (k : ℝ) * ((k : ℝ) + 1) := by
      nlinarith [hk_nonneg]
    have hdiv : (n : ℝ)⁻¹ * 2⁻¹ * (k : ℝ) ^ 2 ≤
        (((k : ℝ) * ((k : ℝ) + 1) / 2) / (n : ℝ)) := by
      field_simp [hnpos.ne']
      nlinarith
    linarith
  exact hterm.trans (Real.exp_le_exp.mpr hquad)

lemma gaussianKernel_zero (n : ℕ) : gaussianKernel n 0 = 1 := by
  simp [gaussianKernel]

lemma sum_gaussianKernel_range_le_one_add_integral {n : ℕ} (hn : 0 < n) :
    (∑ k ∈ Finset.range n, gaussianKernel n k) ≤
      1 + ∫ x in (0 : ℝ)..((n - 1 : ℕ) : ℝ), gaussianKernel n x := by
  cases n with
  | zero => omega
  | succ m =>
      have hanti : AntitoneOn (gaussianKernel (m + 1)) (Set.Icc 0 (0 + (m : ℝ))) := by
        exact gaussianKernel_antitoneOn (n := m + 1) (by omega) (0 + (m : ℝ))
      have hsum := AntitoneOn.sum_le_integral (x₀ := (0 : ℝ)) (a := m) hanti
      calc
        (∑ k ∈ Finset.range (m + 1), gaussianKernel (m + 1) k) =
            (∑ k ∈ Finset.range m, gaussianKernel (m + 1) (k + 1)) + 1 := by
          rw [Finset.sum_range_succ']
          simp [gaussianKernel_zero]
        _ ≤ (∫ x in (0 : ℝ)..(0 + (m : ℝ)), gaussianKernel (m + 1) x) + 1 := by
          simpa using add_le_add_right hsum 1
        _ = 1 + ∫ x in (0 : ℝ)..((m + 1 - 1 : ℕ) : ℝ), gaussianKernel (m + 1) x := by
          simp [add_comm]

lemma integral_gaussianKernel_Ioc_le_Ioi {n : ℕ} (hn : 0 < n) :
    (∫ x in (0 : ℝ)..((n - 1 : ℕ) : ℝ), gaussianKernel n x) ≤
      ∫ x : ℝ in Set.Ioi (0 : ℝ), gaussianKernel n x := by
  have hb : 0 < 1 / (2 * (n : ℝ)) := by positivity
  have hint : MeasureTheory.IntegrableOn (gaussianKernel n) (Set.Ioi (0 : ℝ)) := by
    simpa [gaussianKernel] using
      (integrableOn_Ioi_exp_neg_mul_sq_iff (b := (n : ℝ)⁻¹ * 2⁻¹)).2 (by positivity)
  have hnonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))] gaussianKernel n := by
    exact Eventually.of_forall fun x => (Real.exp_pos _).le
  have hsubset : Set.Ioc (0 : ℝ) ((n - 1 : ℕ) : ℝ) ≤ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) := by
    exact Eventually.of_forall fun x hx => hx.1
  have hset :
      (∫ x in Set.Ioc (0 : ℝ) ((n - 1 : ℕ) : ℝ), gaussianKernel n x) ≤
        ∫ x : ℝ in Set.Ioi (0 : ℝ), gaussianKernel n x :=
    MeasureTheory.setIntegral_mono_set (s := Set.Ioc (0 : ℝ) ((n - 1 : ℕ) : ℝ))
      (t := Set.Ioi (0 : ℝ)) hint hnonneg hsubset
  have hle : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by positivity
  simpa [intervalIntegral.integral_of_le hle] using hset

lemma integral_gaussianKernel_Ioi {n : ℕ} (_hn : 0 < n) :
    (∫ x : ℝ in Set.Ioi (0 : ℝ), gaussianKernel n x) =
      Real.sqrt (Real.pi / ((n : ℝ)⁻¹ * 2⁻¹)) / 2 := by
  simpa [gaussianKernel] using integral_gaussian_Ioi (b := (n : ℝ)⁻¹ * 2⁻¹)

/--
One-sided sharp Gaussian-integral upper bound.  The right side is equal to
`1 + sqrt (π * n / 2)` for positive `n`.
-/
theorem ramanujanQ_le_one_add_gaussian_halfline {n : ℕ} (hn : 0 < n) :
    ramanujanQ n ≤ 1 + Real.sqrt (Real.pi / ((n : ℝ)⁻¹ * 2⁻¹)) / 2 := by
  unfold ramanujanQ
  calc
    (∑ k ∈ Finset.range n, ramanujanQTerm n k) ≤
        ∑ k ∈ Finset.range n, gaussianKernel n k := by
      refine Finset.sum_le_sum ?_
      intro k hk
      exact ramanujanQTerm_le_gaussianKernel hn (Nat.le_of_lt (Finset.mem_range.mp hk))
    _ ≤ 1 + ∫ x in (0 : ℝ)..((n - 1 : ℕ) : ℝ), gaussianKernel n x :=
      sum_gaussianKernel_range_le_one_add_integral hn
    _ ≤ 1 + ∫ x : ℝ in Set.Ioi (0 : ℝ), gaussianKernel n x := by
      exact add_le_add (le_refl 1) (integral_gaussianKernel_Ioc_le_Ioi hn)
    _ = 1 + Real.sqrt (Real.pi / ((n : ℝ)⁻¹ * 2⁻¹)) / 2 := by
      rw [integral_gaussianKernel_Ioi hn]

lemma gaussian_halfline_value_eq_sqrt_pi_mul_nat_div_two {n : ℕ} (hn : 0 < n) :
    Real.sqrt (Real.pi / ((n : ℝ)⁻¹ * 2⁻¹)) / 2 =
      Real.sqrt (Real.pi * (n : ℝ) / 2) := by
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  have hnpos : (n : ℝ) ≠ 0 := by positivity
  field_simp [hnpos]

/-- Clean form of the one-sided Gaussian upper bound. -/
theorem ramanujanQ_le_one_add_sqrt_pi_mul_nat_div_two {n : ℕ} (hn : 0 < n) :
    ramanujanQ n ≤ 1 + Real.sqrt (Real.pi * (n : ℝ) / 2) := by
  have h := ramanujanQ_le_one_add_gaussian_halfline hn
  rw [gaussian_halfline_value_eq_sqrt_pi_mul_nat_div_two hn] at h
  exact h

lemma sqrt_pi_mul_nat_div_two_le_two_sqrt (n : ℕ) :
    Real.sqrt (Real.pi * (n : ℝ) / 2) ≤ 2 * Real.sqrt (n : ℝ) := by
  apply (Real.sqrt_le_left (by positivity)).mpr
  have hnnonneg : 0 ≤ (n : ℝ) := by positivity
  nlinarith [Real.sq_sqrt hnnonneg, Real.pi_le_four]

theorem eventually_ramanujanQ_le_three_sqrt :
    ∀ᶠ n : ℕ in atTop, ramanujanQ n ≤ 3 * Real.sqrt (n : ℝ) := by
  refine eventually_atTop.2 ⟨1, ?_⟩
  intro n hn
  have hnpos : 0 < n := by omega
  have hQ := ramanujanQ_le_one_add_sqrt_pi_mul_nat_div_two hnpos
  have hone : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hn
  have hgauss := sqrt_pi_mul_nat_div_two_le_two_sqrt n
  calc
    ramanujanQ n ≤ 1 + Real.sqrt (Real.pi * (n : ℝ) / 2) := hQ
    _ ≤ Real.sqrt (n : ℝ) + 2 * Real.sqrt (n : ℝ) := add_le_add hone hgauss
    _ = 3 * Real.sqrt (n : ℝ) := by ring

/-- Bankable floor: Ramanujan's Q-function has order `sqrt n`. -/
theorem ramanujanQ_isTheta_sqrt :
    (fun n : ℕ => ramanujanQ n) =Θ[atTop] (fun n : ℕ => Real.sqrt (n : ℝ)) := by
  constructor
  · refine IsBigO.of_bound 3 ?_
    exact eventually_ramanujanQ_le_three_sqrt.mono fun n hn => by
      have hQ : 0 ≤ ramanujanQ n := ramanujanQ_nonneg n
      have hs : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
      simpa [Real.norm_eq_abs, abs_of_nonneg hQ, abs_of_nonneg hs] using hn
  · refine IsBigO.of_bound 4 ?_
    exact eventually_sqrt_div_four_le_ramanujanQ.mono fun n hn => by
      have hQ : 0 ≤ ramanujanQ n := ramanujanQ_nonneg n
      have hs : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
      have hle : Real.sqrt (n : ℝ) ≤ 4 * ramanujanQ n := by nlinarith
      simpa [Real.norm_eq_abs, abs_of_nonneg hQ, abs_of_nonneg hs] using hle

end

end AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS
