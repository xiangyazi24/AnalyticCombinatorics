import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.SigmaRecurrence
import AnalyticCombinatorics.Ch8.Partitions.SigmaSummatory
import AnalyticCombinatorics.Ch8.Partitions.LogAsymptotic

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open Filter
open scoped BigOperators Topology

noncomputable section

noncomputable def C : ℝ :=
  Real.pi * Real.sqrt (2 / 3)

noncomputable def u (n : ℕ) : ℝ :=
  (n : ℝ) * Partitions.part n * Real.exp (-C * Real.sqrt (n : ℝ))

noncomputable def erdosWeight (n m : ℕ) : ℝ :=
  Sigma.sigmaR m / ((n - m : ℕ) : ℝ) *
    Real.exp (-C * (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ)))

noncomputable def boundaryTerm (n : ℕ) : ℝ :=
  Sigma.sigmaR n * Real.exp (-C * Real.sqrt (n : ℝ))

lemma C_pos : 0 < C := by
  dsimp [C]
  positivity

lemma C_sq_eq_four_mul_A : C ^ 2 = 4 * Partitions.A := by
  dsimp [C, Partitions.A]
  rw [mul_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 / 3 : ℝ))]
  ring

lemma sigmaR_nonneg (n : ℕ) : 0 ≤ Sigma.sigmaR n := by
  rw [Sigma.sigmaR_eq_sum_divisors]
  exact Finset.sum_nonneg fun d _hd => by positivity

lemma sigmaR_le_square {n : ℕ} (hn : 1 ≤ n) :
    Sigma.sigmaR n ≤ (n : ℝ) ^ 2 := by
  rw [Sigma.sigmaR_eq_sum_divisors]
  have hsub : n.divisors ⊆ Finset.Icc 1 n := by
    intro d hd
    have hmem := (Nat.mem_divisors.mp hd)
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hmem.1 (Nat.pos_of_ne_zero hmem.2)
    have hdle : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hmem.2) hmem.1
    exact Finset.mem_Icc.mpr ⟨hdpos, hdle⟩
  have hcard_nat : n.divisors.card ≤ n := by
    calc
      n.divisors.card ≤ (Finset.Icc 1 n).card := Finset.card_le_card hsub
      _ = n := by
        simp
  have hsum_le :
      (∑ d ∈ n.divisors, (d : ℝ)) ≤ ∑ _d ∈ n.divisors, (n : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro d hd
    have hmem := (Nat.mem_divisors.mp hd)
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hmem.2) hmem.1
  calc
    (∑ d ∈ n.divisors, (d : ℝ))
        ≤ ∑ _d ∈ n.divisors, (n : ℝ) := hsum_le
    _ = (n.divisors.card : ℝ) * (n : ℝ) := by
          simp [nsmul_eq_mul, mul_comm]
    _ ≤ (n : ℝ) ^ 2 := by
          have hcard : (n.divisors.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcard_nat
          have hn0 : 0 ≤ (n : ℝ) := by positivity
          nlinarith

lemma sigma_summatory_nonneg (N : ℕ) :
    0 ≤ ∑ m ∈ Finset.Icc 1 N, Sigma.sigmaR m := by
  exact Finset.sum_nonneg fun m _hm => sigmaR_nonneg m

lemma sigma_summatory_quadratic_bound :
    ∃ B : ℝ, 0 < B ∧
      ∀ N : ℕ, (∑ m ∈ Finset.Icc 1 N, Sigma.sigmaR m) ≤ B * (N : ℝ) ^ 2 := by
  rcases Sigma.sigma_summatory_asymptotic with ⟨K, hKpos, hK⟩
  refine ⟨Real.pi ^ 2 / 12 + 2 * K + 1, by positivity, ?_⟩
  intro N
  by_cases hN : 1 ≤ N
  · have hNR : 1 ≤ (N : ℝ) := by exact_mod_cast hN
    have hKbound := hK (N : ℝ) hNR
    have hfloor : ⌊(N : ℝ)⌋₊ = N := Nat.floor_natCast N
    have hmain_nonneg : 0 ≤ (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2 := by positivity
    have hlog_le : Real.log (2 * (N : ℝ)) ≤ 2 * (N : ℝ) := by
      exact Real.log_le_self (by positivity : 0 ≤ 2 * (N : ℝ))
    have hlog_term :
        K * (N : ℝ) * Real.log (2 * (N : ℝ)) ≤
          2 * K * (N : ℝ) ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hlog_le (by positivity : 0 ≤ K * (N : ℝ))
      nlinarith
    have hupper :
        (∑ m ∈ Finset.Icc 1 N, Sigma.sigmaR m) ≤
          (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2 +
            K * (N : ℝ) * Real.log (2 * (N : ℝ)) := by
      have hle_abs :
          (∑ m ∈ Finset.Icc 1 N, Sigma.sigmaR m) -
              (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2 ≤
            |(∑ m ∈ Finset.Icc 1 N, Sigma.sigmaR m) -
              (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2| :=
        le_abs_self _
      have hKbound' :
          |(∑ m ∈ Finset.Icc 1 N, Sigma.sigmaR m) -
              (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2| ≤
            K * (N : ℝ) * Real.log (2 * (N : ℝ)) := by
        simpa [hfloor] using hKbound
      linarith
    calc
      (∑ m ∈ Finset.Icc 1 N, Sigma.sigmaR m)
          ≤ (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2 +
              K * (N : ℝ) * Real.log (2 * (N : ℝ)) := hupper
      _ ≤ (Real.pi ^ 2 / 12 + 2 * K) * (N : ℝ) ^ 2 := by
            nlinarith [hlog_term]
      _ ≤ (Real.pi ^ 2 / 12 + 2 * K + 1) * (N : ℝ) ^ 2 := by
            have hN2 : 0 ≤ (N : ℝ) ^ 2 := by positivity
            nlinarith
  · have hN0 : N = 0 := by omega
    subst hN0
    simp

lemma boundaryTerm_nonneg (n : ℕ) : 0 ≤ boundaryTerm n := by
  dsimp [boundaryTerm]
  exact mul_nonneg (sigmaR_nonneg n) (Real.exp_pos _).le

lemma erdosWeight_nonneg_of_lt {n m : ℕ} (hmn : m < n) :
    0 ≤ erdosWeight n m := by
  dsimp [erdosWeight]
  have hden : 0 < ((n - m : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hmn
  exact mul_nonneg (div_nonneg (sigmaR_nonneg m) hden.le) (Real.exp_pos _).le

lemma erdosWeight_nonneg_of_mem {n m : ℕ} (hm : m ∈ Finset.Icc 1 (n - 1)) :
    0 ≤ erdosWeight n m := by
  have hmI := Finset.mem_Icc.mp hm
  exact erdosWeight_nonneg_of_lt (n := n) (m := m) (by omega)

lemma erdos_kernel_sum_nonneg (n : ℕ) :
    0 ≤ ∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m := by
  exact Finset.sum_nonneg fun m hm => erdosWeight_nonneg_of_mem hm

lemma erdos_kernel_cut_sum_nonneg (n : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    0 ≤ ∑ m ∈ Finset.Icc 1 (n - 1), if P m then erdosWeight n m else 0 := by
  refine Finset.sum_nonneg ?_
  intro m hm
  by_cases hP : P m
  · simp [hP, erdosWeight_nonneg_of_mem hm]
  · simp [hP]

lemma nat_sq_mul_exp_neg_sqrt_tendsto_zero :
    Tendsto
      (fun n : ℕ => (n : ℝ) ^ 2 * Real.exp (-C * Real.sqrt (n : ℝ)))
      atTop
      (𝓝 0) := by
  have hreal :
      Tendsto
        (fun x : ℝ => x ^ (4 : ℝ) * Real.exp (-C * x))
        atTop
        (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4 : ℝ) C C_pos
  have hsqrt_nat :
      Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  refine (hreal.comp hsqrt_nat).congr' ?_
  filter_upwards with n
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hpow : Real.sqrt (n : ℝ) ^ (4 : ℝ) = (n : ℝ) ^ 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num]
    rw [Real.rpow_mul hsqrt_nonneg]
    rw [show Real.sqrt (n : ℝ) ^ (2 : ℝ) = (n : ℝ) by
      simp [Real.sq_sqrt hn0]]
    rw [Real.rpow_two]
  change
    Real.sqrt (n : ℝ) ^ (4 : ℝ) * Real.exp (-C * Real.sqrt (n : ℝ)) =
      (n : ℝ) ^ 2 * Real.exp (-C * Real.sqrt (n : ℝ))
  rw [hpow]

theorem boundaryTerm_negligible :
    Tendsto boundaryTerm atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    nat_sq_mul_exp_neg_sqrt_tendsto_zero ?_ ?_
  · filter_upwards with n
    exact boundaryTerm_nonneg n
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    dsimp [boundaryTerm]
    have hsig := sigmaR_le_square (n := n) hn
    exact mul_le_mul_of_nonneg_right hsig (Real.exp_pos _).le

theorem u_recurrence (n : ℕ) (hn : 2 ≤ n) :
    u n =
      (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * u (n - m)) +
        boundaryTerm n := by
  classical
  have hn1 : 1 ≤ n := hn.trans' (by norm_num)
  have hrec := Sigma.partition_sigma_recurrence n hn1
  have hsplit :
      (∑ m ∈ Finset.Icc 1 n, Sigma.sigmaR m * Partitions.part (n - m)) =
        (∑ m ∈ Finset.Icc 1 (n - 1),
            Sigma.sigmaR m * Partitions.part (n - m)) +
          Sigma.sigmaR n * Partitions.part 0 := by
    have htop :
        (∑ m ∈ Finset.Icc 1 ((n - 1) + 1),
            Sigma.sigmaR m * Partitions.part (((n - 1) + 1) - m)) =
          (∑ m ∈ Finset.Icc 1 (n - 1),
              Sigma.sigmaR m * Partitions.part (((n - 1) + 1) - m)) +
            Sigma.sigmaR ((n - 1) + 1) *
              Partitions.part (((n - 1) + 1) - ((n - 1) + 1)) := by
      exact Finset.sum_Icc_succ_top
        (a := 1) (b := n - 1)
        (by omega)
        (fun m => Sigma.sigmaR m * Partitions.part (((n - 1) + 1) - m))
    have hnsub : (n - 1) + 1 = n := by omega
    simpa [hnsub] using htop
  have hmain :
      (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * u (n - m)) =
        (∑ m ∈ Finset.Icc 1 (n - 1),
            Sigma.sigmaR m * Partitions.part (n - m) *
              Real.exp (-C * Real.sqrt (n : ℝ))) := by
    refine Finset.sum_congr rfl ?_
    intro m hm
    have hmI := Finset.mem_Icc.mp hm
    have hmle : m ≤ n - 1 := hmI.2
    have hmn_pos_nat : 0 < n - m := by omega
    have hmn_pos : 0 < ((n - m : ℕ) : ℝ) := by exact_mod_cast hmn_pos_nat
    have hmn_ne : ((n - m : ℕ) : ℝ) ≠ 0 := hmn_pos.ne'
    have hsqrt_add :
        -C * (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ)) +
            (-C * Real.sqrt ((n - m : ℕ) : ℝ)) =
          -C * Real.sqrt (n : ℝ) := by
      ring
    calc
      erdosWeight n m * u (n - m)
          =
            (Sigma.sigmaR m / ((n - m : ℕ) : ℝ) *
                Real.exp (-C *
                  (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ)))) *
              (((n - m : ℕ) : ℝ) * Partitions.part (n - m) *
                Real.exp (-C * Real.sqrt ((n - m : ℕ) : ℝ))) := by
                  rfl
      _ =
            Sigma.sigmaR m * Partitions.part (n - m) *
              (Real.exp (-C *
                  (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))) *
                Real.exp (-C * Real.sqrt ((n - m : ℕ) : ℝ))) := by
                  field_simp [hmn_ne]
      _ =
            Sigma.sigmaR m * Partitions.part (n - m) *
              Real.exp (-C * Real.sqrt (n : ℝ)) := by
                  rw [← Real.exp_add, hsqrt_add]
  calc
    u n
        = ((n : ℝ) * Partitions.part n) *
            Real.exp (-C * Real.sqrt (n : ℝ)) := by
          rw [u]
    _ = (∑ m ∈ Finset.Icc 1 n,
            Sigma.sigmaR m * Partitions.part (n - m)) *
          Real.exp (-C * Real.sqrt (n : ℝ)) := by
          rw [hrec]
    _ = ((∑ m ∈ Finset.Icc 1 (n - 1),
            Sigma.sigmaR m * Partitions.part (n - m)) +
          Sigma.sigmaR n * Partitions.part 0) *
          Real.exp (-C * Real.sqrt (n : ℝ)) := by
          rw [hsplit]
    _ = (∑ m ∈ Finset.Icc 1 (n - 1),
            Sigma.sigmaR m * Partitions.part (n - m) *
              Real.exp (-C * Real.sqrt (n : ℝ))) +
          Sigma.sigmaR n * Real.exp (-C * Real.sqrt (n : ℝ)) := by
          rw [Partitions.part_zero]
          rw [add_mul, Finset.sum_mul]
          ring
    _ = (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * u (n - m)) +
          boundaryTerm n := by
          rw [hmain]
          rfl

end

end AnalyticCombinatorics.Ch8.Partitions.Erdos
