import Mathlib

/-!
# Abstract finite-state Feynman--Kac block bridge

This file contains only finite-sum semigroup algebra.  A stochastic kernel `Q`
with survival weight `w` induces the substochastic kernel
`weightedKernel Q w s z = w s * Q s z`.  If every `M`-step Feynman--Kac block
has a uniform drop, then the total surviving mass tends to zero.
-/

noncomputable section

open Filter Finset Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {S : Type*} [Fintype S]

/-- One step of a substochastic kernel applied to a row vector. -/
def evolve (K : S → S → ℝ) (μ : S → ℝ) : ℕ → S → ℝ
  | 0 => μ
  | t + 1 => fun z => ∑ s, evolve K μ t s * K s z

/-- Total mass after evolving by `K`. -/
def uMass (K : S → S → ℝ) (μ : S → ℝ) (t : ℕ) : ℝ :=
  ∑ s, evolve K μ t s

/-- The `M`-step Feynman--Kac block weight from `s`. -/
def blockWeight (K : S → S → ℝ) : ℕ → S → ℝ
  | 0 => fun _ => 1
  | M + 1 => fun s => ∑ z, K s z * blockWeight K M z

/-- The substochastic kernel with departure-state survival weight `w`. -/
def weightedKernel (Q : S → S → ℝ) (w : S → ℝ) : S → S → ℝ :=
  fun s z => w s * Q s z

lemma evolve_nonneg {K : S → S → ℝ} {μ : S → ℝ}
    (hKnn : ∀ s z, 0 ≤ K s z) (hμnn : ∀ s, 0 ≤ μ s) :
    ∀ t s, 0 ≤ evolve K μ t s := by
  intro t
  induction t with
  | zero =>
      intro s
      exact hμnn s
  | succ t ih =>
      intro z
      simp only [evolve]
      exact Finset.sum_nonneg fun s _ => mul_nonneg (ih s) (hKnn s z)

lemma uMass_nonneg {K : S → S → ℝ} {μ : S → ℝ}
    (hKnn : ∀ s z, 0 ≤ K s z) (hμnn : ∀ s, 0 ≤ μ s) (t : ℕ) :
    0 ≤ uMass K μ t := by
  exact Finset.sum_nonneg fun s _ => evolve_nonneg hKnn hμnn t s

lemma blockWeight_nonneg {K : S → S → ℝ} (hKnn : ∀ s z, 0 ≤ K s z) :
    ∀ M s, 0 ≤ blockWeight K M s := by
  intro M
  induction M with
  | zero =>
      intro s
      simp [blockWeight]
  | succ M ih =>
      intro s
      simp only [blockWeight]
      exact Finset.sum_nonneg fun z _ => mul_nonneg (hKnn s z) (ih z)

lemma blockWeight_nonneg' {K : S → S → ℝ} (hKnn : ∀ s z, 0 ≤ K s z) (M : ℕ) (s : S) :
    0 ≤ blockWeight K M s := by
  exact blockWeight_nonneg hKnn M s

lemma uMass_zero (K : S → S → ℝ) (μ : S → ℝ) :
    uMass K μ 0 = ∑ s, μ s := by
  rfl

lemma uMass_succ (K : S → S → ℝ) (μ : S → ℝ) (t : ℕ) :
    uMass K μ (t + 1) = ∑ s, evolve K μ t s * ∑ z, K s z := by
  unfold uMass
  simp only [evolve]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro s _hs
  rw [Finset.mul_sum]

lemma blockWeight_zero (K : S → S → ℝ) (s : S) :
    blockWeight K 0 s = 1 := by
  rfl

lemma blockWeight_succ (K : S → S → ℝ) (M : ℕ) (s : S) :
    blockWeight K (M + 1) s = ∑ z, K s z * blockWeight K M z := by
  rfl

lemma uMass_add_eq_sum_blockWeight (K : S → S → ℝ) (μ : S → ℝ) :
    ∀ M n, uMass K μ (n + M) = ∑ s, evolve K μ n s * blockWeight K M s := by
  intro M
  induction M with
  | zero =>
      intro n
      simp [blockWeight_zero, uMass]
  | succ M ih =>
      intro n
      rw [show n + (M + 1) = (n + 1) + M by omega]
      rw [ih (n + 1)]
      simp only [evolve, blockWeight_succ]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro s _hs
      calc
        (∑ z, evolve K μ n s * K s z * blockWeight K M z)
            = ∑ z, evolve K μ n s * (K s z * blockWeight K M z) := by
              refine Finset.sum_congr rfl ?_
              intro z _hz
              ring
        _ = evolve K μ n s * ∑ z, K s z * blockWeight K M z := by
              rw [Finset.mul_sum]

lemma exists_pos_of_nonneg_sum_one {μ : S → ℝ} (hμnn : ∀ s, 0 ≤ μ s)
    (hμsum : ∑ s, μ s = 1) :
    ∃ s, 0 < μ s := by
  by_contra h
  have hzero : ∀ s, μ s = 0 := by
    intro s
    exact le_antisymm (le_of_not_gt (fun hs => h ⟨s, hs⟩)) (hμnn s)
  have : ∑ s, μ s = 0 := by simp [hzero]
  linarith

omit [Fintype S] in
lemma weightedKernel_nonneg {Q : S → S → ℝ} {w : S → ℝ}
    (hQnn : ∀ s z, 0 ≤ Q s z) (hw01 : ∀ s, 0 ≤ w s ∧ w s ≤ 1) :
    ∀ s z, 0 ≤ weightedKernel Q w s z := by
  intro s z
  exact mul_nonneg (hw01 s).1 (hQnn s z)

lemma weightedKernel_row_sum {Q : S → S → ℝ} {w : S → ℝ}
    (hQsum : ∀ s, ∑ z, Q s z = 1) (s : S) :
    ∑ z, weightedKernel Q w s z = w s := by
  unfold weightedKernel
  rw [← Finset.mul_sum, hQsum s, mul_one]

lemma weightedKernel_row_le_one {Q : S → S → ℝ} {w : S → ℝ}
    (hQsum : ∀ s, ∑ z, Q s z = 1) (hw01 : ∀ s, 0 ≤ w s ∧ w s ≤ 1) :
    ∀ s, ∑ z, weightedKernel Q w s z ≤ 1 := by
  intro s
  rw [weightedKernel_row_sum hQsum s]
  exact (hw01 s).2

lemma uMass_antitone {K : S → S → ℝ} {μ : S → ℝ}
    (hKnn : ∀ s z, 0 ≤ K s z) (hrow : ∀ s, ∑ z, K s z ≤ 1)
    (hμnn : ∀ s, 0 ≤ μ s) :
    Antitone (uMass K μ) := by
  refine antitone_nat_of_succ_le ?_
  intro t
  rw [uMass_succ]
  have hle : (∑ s, evolve K μ t s * ∑ z, K s z) ≤ ∑ s, evolve K μ t s := by
    refine Finset.sum_le_sum ?_
    intro s _hs
    have hnn := evolve_nonneg hKnn hμnn t s
    calc
      evolve K μ t s * (∑ z, K s z) ≤ evolve K μ t s * 1 :=
        mul_le_mul_of_nonneg_left (hrow s) hnn
      _ = evolve K μ t s := by ring
  exact hle

lemma nat_div_tendsto_atTop {M : ℕ} (hM : 0 < M) :
    Tendsto (fun n : ℕ => n / M) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨b * M, fun n hn => ?_⟩
  exact (Nat.le_div_iff_mul_le hM).2 hn

/-- Abstract finite-state FK block bridge.

If every length-`M` block has survival weight at most `1 - c0`, then the total
mass of the substochastic FK semigroup tends to zero. -/
theorem fk_block_bridge
    (Q : S → S → ℝ) (w : S → ℝ)
    (hQnn : ∀ s z, 0 ≤ Q s z) (hQsum : ∀ s, ∑ z, Q s z = 1)
    (hw01 : ∀ s, 0 ≤ w s ∧ w s ≤ 1)
    (M : ℕ) (hM : 0 < M) (c0 : ℝ) (hc0 : 0 < c0)
    (hdrop : ∀ s, blockWeight (weightedKernel Q w) M s ≤ 1 - c0)
    (μ0 : S → ℝ) (hμ0nn : ∀ s, 0 ≤ μ0 s) (hμ0sum : ∑ s, μ0 s = 1) :
    Tendsto (fun t => uMass (weightedKernel Q w) μ0 t) atTop (𝓝 0) := by
  let K := weightedKernel Q w
  let q : ℝ := 1 - c0
  have hKnn : ∀ s z, 0 ≤ K s z := weightedKernel_nonneg hQnn hw01
  have hrow : ∀ s, ∑ z, K s z ≤ 1 := weightedKernel_row_le_one hQsum hw01
  have hanti : Antitone (uMass K μ0) := uMass_antitone hKnn hrow hμ0nn
  have hq_nonneg : 0 ≤ q := by
    obtain ⟨s0, hs0⟩ := exists_pos_of_nonneg_sum_one hμ0nn hμ0sum
    have hbnn : 0 ≤ blockWeight K M s0 := blockWeight_nonneg' hKnn M s0
    have hbd : blockWeight K M s0 ≤ q := hdrop s0
    linarith
  have hq_lt_one : q < 1 := by
    dsimp [q]
    linarith
  have hcontract : ∀ n, uMass K μ0 (n + M) ≤ q * uMass K μ0 n := by
    intro n
    rw [uMass_add_eq_sum_blockWeight K μ0 M n]
    have hle : (∑ s, evolve K μ0 n s * blockWeight K M s) ≤
        ∑ s, evolve K μ0 n s * q := by
      refine Finset.sum_le_sum ?_
      intro s _hs
      exact mul_le_mul_of_nonneg_left (hdrop s) (evolve_nonneg hKnn hμ0nn n s)
    calc
      (∑ s, evolve K μ0 n s * blockWeight K M s)
          ≤ ∑ s, evolve K μ0 n s * q := hle
      _ = q * uMass K μ0 n := by
          unfold uMass
          rw [← Finset.sum_mul]
          ring
  have hblock : ∀ k : ℕ, uMass K μ0 (k * M) ≤ q ^ k := by
    intro k
    induction k with
    | zero =>
        rw [Nat.zero_mul, pow_zero, uMass_zero, hμ0sum]
    | succ k ih =>
        have hc := hcontract (k * M)
        calc
          uMass K μ0 ((k + 1) * M) ≤ q * uMass K μ0 (k * M) := by
            simpa [Nat.succ_mul] using hc
          _ ≤ q * q ^ k := mul_le_mul_of_nonneg_left ih hq_nonneg
          _ = q ^ (k + 1) := by ring
  have hpow : Tendsto (fun k : ℕ => q ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt_one
  have hpowdiv : Tendsto (fun n : ℕ => q ^ (n / M)) atTop (𝓝 0) :=
    hpow.comp (nat_div_tendsto_atTop hM)
  have hupper : ∀ n : ℕ, uMass K μ0 n ≤ q ^ (n / M) := by
    intro n
    have hle : (n / M) * M ≤ n := Nat.div_mul_le_self n M
    exact (hanti hle).trans (hblock (n / M))
  exact squeeze_zero' (Eventually.of_forall (uMass_nonneg hKnn hμ0nn)) (Eventually.of_forall hupper)
    hpowdiv

#print axioms fk_block_bridge

end AnalyticCombinatorics.Ch8.Partitions.Erdos
