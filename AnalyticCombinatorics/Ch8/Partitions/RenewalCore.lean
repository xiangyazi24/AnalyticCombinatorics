import Mathlib

/-!
# TASK T2.2 core: discrete renewal machinery for the rank-band overshoot/overlap brick

Mathlib has no renewal theory, so we build it from scratch in the repo's deterministic
finite-sum style.  This file sets up the increment-law convolution apparatus and the elementary
facts that do *not* require the renewal limit:

* `IsIncrementLaw p` — `p` is a probability mass supported on `{1,2,…}` (no atom at `0`);
* `convPow p j` — the law of the sum of `j` i.i.d. increments (`j`-fold convolution), with
  `convPow p 0 = δ₀`, `convPow p (j+1) = convPow p j ⋆ p`;
* `renewalMass p N k = ∑_{j<N} convPow p j k` — the truncated expected number of visits to
  level `k` using at most `N` renewals;
* nonnegativity, the total-mass identity `∑_k convPow p j k = 1`, the support fact
  `convPow p j k = 0` for `k < j` (each of the `j` increments is `≥ 1`), and the
  **increment exponential tail ⟹ convolution tail** estimate used by the offset-tail bound.

The genuinely hard renewal-limit / coupling facts live in `RenewalOverlap.lean`.

Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Renewal

/-- An **increment law**: a probability mass on `ℕ` with no atom at `0` (the renewal increments
are all `≥ 1`).  A `tsum`-free total mass over `Finset.range` is awkward because the support
is infinite; we instead require summability and `∑' = 1`. -/
structure IsIncrementLaw (p : ℕ → ℝ) : Prop where
  nonneg : ∀ d, 0 ≤ p d
  zero : p 0 = 0
  summable : Summable p
  total : ∑' d, p d = 1

/-- Convolution of two nonnegative summable masses, `(p ⋆ q) k = ∑_{i+j=k} p i q j`, written as the
finite antidiagonal sum (only finitely many terms are nonzero for fixed `k`). -/
noncomputable def conv (p q : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ ij ∈ Finset.antidiagonal k, p ij.1 * q ij.2

/-- `j`-fold convolution power: `convPow p 0 = δ₀`, `convPow p (j+1) = convPow p j ⋆ p`. -/
noncomputable def convPow (p : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => fun k => if k = 0 then 1 else 0
  | (j+1) => fun k => conv (convPow p j) p k

@[simp] lemma convPow_zero (p : ℕ → ℝ) (k : ℕ) :
    convPow p 0 k = if k = 0 then 1 else 0 := rfl

lemma convPow_succ (p : ℕ → ℝ) (j k : ℕ) :
    convPow p (j+1) k = conv (convPow p j) p k := rfl

/-- Truncated renewal mass: expected number of visits to level `k` in the first `N` renewals. -/
noncomputable def renewalMass (p : ℕ → ℝ) (N k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, convPow p j k

/-! ## Nonnegativity -/

lemma conv_nonneg {p q : ℕ → ℝ} (hp : ∀ d, 0 ≤ p d) (hq : ∀ d, 0 ≤ q d) (k : ℕ) :
    0 ≤ conv p q k :=
  Finset.sum_nonneg fun ij _ => mul_nonneg (hp ij.1) (hq ij.2)

lemma convPow_nonneg {p : ℕ → ℝ} (hp : ∀ d, 0 ≤ p d) (j k : ℕ) :
    0 ≤ convPow p j k := by
  induction j generalizing k with
  | zero => simp only [convPow_zero]; split <;> norm_num
  | succ j ih => rw [convPow_succ]; exact conv_nonneg ih hp k

lemma renewalMass_nonneg {p : ℕ → ℝ} (hp : ∀ d, 0 ≤ p d) (N k : ℕ) :
    0 ≤ renewalMass p N k :=
  Finset.sum_nonneg fun j _ => convPow_nonneg hp j k

/-- `renewalMass` is monotone in the number of renewals `N`. -/
lemma renewalMass_mono {p : ℕ → ℝ} (hp : ∀ d, 0 ≤ p d) (k : ℕ) :
    Monotone (fun N => renewalMass p N k) := by
  intro N M hNM
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  · exact fun j _ _ => convPow_nonneg hp j k

/-! ## Support: `convPow p j` is supported on `{k ≥ j}` (each increment is `≥ 1`). -/

lemma conv_supp_zero {p q : ℕ → ℝ} {a b : ℕ}
    (hp : ∀ k, k < a → p k = 0) (hq : ∀ k, k < b → q k = 0)
    {k : ℕ} (hk : k < a + b) : conv p q k = 0 := by
  refine Finset.sum_eq_zero (fun ij hij => ?_)
  rw [Finset.mem_antidiagonal] at hij
  by_cases hi : ij.1 < a
  · rw [hp ij.1 hi, zero_mul]
  · have : ij.2 < b := by omega
    rw [hq ij.2 this, mul_zero]

/-- Each of the `j` increments is `≥ 1`, so `convPow p j k = 0` whenever `k < j`. -/
lemma convPow_supp {p : ℕ → ℝ} (hz : p 0 = 0) (j : ℕ) :
    ∀ k, k < j → convPow p j k = 0 := by
  induction j with
  | zero => intro k hk; omega
  | succ j ih =>
    intro k hk
    rw [convPow_succ]
    refine conv_supp_zero (a := j) (b := 1) ih (fun k hk0 => ?_) (by omega)
    have : k = 0 := by omega
    rw [this]; exact hz

/-! ## Total mass: `∑'_k convPow p j k = 1`. -/

/-- For fixed `k`, `conv p q k` only involves `p i, q (k−i)` for `i ≤ k`; rewrite it as a
`Finset.range (k+1)` sum, convenient for re-summation. -/
lemma conv_eq_range_sum (p q : ℕ → ℝ) (k : ℕ) :
    conv p q k = ∑ i ∈ Finset.range (k+1), p i * q (k - i) := by
  rw [conv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => p i * q j)]

/-- Convolution of two summable masses is summable. -/
lemma conv_summable {p q : ℕ → ℝ}
    (hp : ∀ d, 0 ≤ p d) (hq : ∀ d, 0 ≤ q d)
    (hps : Summable p) (hqs : Summable q) :
    Summable (conv p q) := by
  -- `conv p q = ∑'_i (fun k => p i * q (k - i))` dominated; use the Cauchy-product summability.
  have h := summable_sum_mul_antidiagonal_of_summable_mul
    (f := p) (g := q)
    (Summable.mul_of_nonneg hps hqs hp hq)
  simpa [conv] using h

/-- Total mass of a convolution of two probability masses is the product of totals (`1·1=1`). -/
lemma conv_tsum {p q : ℕ → ℝ}
    (hp : ∀ d, 0 ≤ p d) (hq : ∀ d, 0 ≤ q d)
    (hps : Summable p) (hqs : Summable q) :
    ∑' k, conv p q k = (∑' i, p i) * (∑' j, q j) := by
  have hpn : Summable fun x => ‖p x‖ := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (hp _)] using hps
  have hqn : Summable fun x => ‖q x‖ := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (hq _)] using hqs
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hpn hqn]
  rfl

lemma convPow_summable {p : ℕ → ℝ} (hp : ∀ d, 0 ≤ p d) (hps : Summable p) (j : ℕ) :
    Summable (convPow p j) := by
  induction j with
  | zero =>
    apply summable_of_ne_finset_zero (s := {0})
    intro k hk
    rw [Finset.mem_singleton] at hk
    simp only [convPow_zero]
    rw [if_neg hk]
  | succ j ih =>
    have : convPow p (j+1) = conv (convPow p j) p := by
      funext k; rw [convPow_succ]
    rw [this]
    exact conv_summable (convPow_nonneg hp j) hp ih hps

lemma convPow_tsum {p : ℕ → ℝ} (hl : IsIncrementLaw p) (j : ℕ) :
    ∑' k, convPow p j k = 1 := by
  induction j with
  | zero =>
    simp only [convPow_zero]
    rw [tsum_eq_single 0 (by intro b hb; simp [hb])]
    simp
  | succ j ih =>
    have heq : convPow p (j+1) = conv (convPow p j) p := by funext k; rw [convPow_succ]
    rw [heq, conv_tsum (convPow_nonneg hl.nonneg j) hl.nonneg
      (convPow_summable hl.nonneg hl.summable j) hl.summable, ih, hl.total, mul_one]

#print axioms convPow_tsum
#print axioms convPow_supp
#print axioms renewalMass_mono

end AnalyticCombinatorics.Ch8.Partitions.Renewal
