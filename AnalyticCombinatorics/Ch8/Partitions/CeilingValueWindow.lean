import AnalyticCombinatorics.Ch8.Partitions.CeilingValueStep
import AnalyticCombinatorics.Ch8.Partitions.CeilingHit
import AnalyticCombinatorics.Ch8.Partitions.RenewalOverlap

/-!
# TASK L4 (R8 elementary route): same-ceiling value overlap via the divisor-self bound `σ(m) ≥ m`

The variable rank-band engine needs a positive in-band overlap (L4): for two starts `x, y` at the
same ceiling rank `T = R + A R`, the first-entrance laws into the band `ceilBand R (A R)` overlap by
`≥ β` on the in-band slice `{R ≤ rnk z}`.  By the banked one-step reduction
`min_Pker_le_min_enterBandKer_sum` this reduces to a positive overlap of the **one-step** predecessor
laws `Pker x ·`, `Pker y ·` on the slice.

R8's elementary idea (`/tmp/ac_a_uniform.txt`): a single **common value window**
`W_T = [ (T+1)²/9 − 2T , T²/9 − T ] ∩ ℕ` (length `~7T/9`) sits below every ceiling-rank value `x`,
inside the engine slice, and carries `Pker x z ≥ c/T` for EVERY same-ceiling `x` and `z ∈ W_T`.
The lower bound uses ONLY the trivial divisor-self bound `σ(x−z) ≥ x−z ≥ T` (no two-point divisor
estimate, no `KernelWindow`).  A constant minorant `η = c/T` on `S = W_T` with `|W_T| ≥ q·T` gives
overlap `≥ (c/T)(q·T) = cq =: β > 0` via the banked `overlap_ge_of_minorization`.

NEW file; imports the banked bricks, does not modify them.  Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-! ## Brick 1 — the divisor-self bound `σ(m) ≥ m`. -/

/-- **Divisor-self lower bound.**  `m ≤ σ(m)` for `1 ≤ m`: the divisor `m ∣ m` is a single term of
the nonnegative divisor sum `σ(m) = ∑_{d ∣ m} d`. -/
lemma sigmaR_ge_self {m : ℕ} (hm : 1 ≤ m) : (m : ℝ) ≤ Sigma.sigmaR m := by
  rw [Sigma.sigmaR_eq_sum_divisors]
  have hmem : m ∈ m.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩
  have h := Finset.single_le_sum (f := fun d : ℕ => (d : ℝ))
    (fun d _ => Nat.cast_nonneg d) hmem
  simpa using h

#print axioms sigmaR_ge_self

/-! ## Brick 2 — the common value window. -/

/-- **Common value window** `W_T = Icc ((T+1)²/9 − 2T) (T²/9 − T)` (nat division).  Length `~7T/9`;
sits below every ceiling-rank-`T` value and inside the in-band slice. -/
def commonValueWindow (T : ℕ) : Finset ℕ :=
  Finset.Icc ((T + 1) ^ 2 / 9 - 2 * T) (T ^ 2 / 9 - T)

/-- Cast bounds for nat division by `9`: `↑n/9 − 1 < ↑(n/9) ≤ ↑n/9`. -/
lemma cast_div9_bounds (n : ℕ) :
    (n : ℝ) / 9 - 1 < ((n / 9 : ℕ) : ℝ) ∧ ((n / 9 : ℕ) : ℝ) ≤ (n : ℝ) / 9 := by
  constructor
  · have hdm := Nat.div_add_mod n 9
    have hmod : n % 9 < 9 := Nat.mod_lt n (by norm_num)
    have h : n < 9 * (n / 9) + 9 := by omega
    have hc : (n : ℝ) < 9 * ((n / 9 : ℕ) : ℝ) + 9 := by exact_mod_cast h
    linarith
  · exact Nat.cast_div_le

/-! ## Brick 3 — window geometry: jump and sqrt bounds. -/

set_option maxHeartbeats 800000 in
/-- **Window geometry.**  Eventually in `T`, for every value `x` of rank exactly `T` and every `z` in
the common window: `1 ≤ z`, `z < x`, the jump satisfies `T ≤ x − z ≤ 3T`, and `√x − √z ≤ 10`. -/
lemma commonValueWindow_jump_bounds :
    ∀ᶠ T in atTop, ∀ x z, rnk x = T → z ∈ commonValueWindow T →
      1 ≤ z ∧ z < x ∧
      (T : ℝ) ≤ ((x - z : ℕ) : ℝ) ∧
      ((x - z : ℕ) : ℝ) ≤ 3 * (T : ℝ) ∧
      Real.sqrt (x : ℝ) - Real.sqrt (z : ℝ) ≤ 10 := by
  filter_upwards [eventually_ge_atTop 100] with T hT100
  intro x z hx hz
  -- unpack rank: T²/9 ≤ x < (T+1)²/9 (real), via rnk x = T
  have hTR : (100 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT100
  -- rnk x = T  ⟹  T ≤ 3√x < T+1
  have hxb := rnk_sqrt_bounds x
  rw [hx] at hxb
  obtain ⟨hxlo, hxhi⟩ := hxb        -- T ≤ 3√x ,  3√x < T+1
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    have hsx : (0 : ℝ) < Real.sqrt (x : ℝ) := by
      have : (T : ℝ) / 3 ≤ Real.sqrt (x : ℝ) := by linarith
      linarith
    have := Real.sqrt_pos.mp hsx; linarith
  -- √x ≥ T/3 and √x < (T+1)/3
  have hsx_lo : (T : ℝ) / 3 ≤ Real.sqrt (x : ℝ) := by linarith
  have hsx_hi : Real.sqrt (x : ℝ) < ((T : ℝ) + 1) / 3 := by linarith
  -- x bounds: T²/9 ≤ x and x < (T+1)²/9
  have hsxsq : Real.sqrt (x : ℝ) ^ 2 = (x : ℝ) := Real.sq_sqrt hxpos.le
  have hx_lo : (T : ℝ) ^ 2 / 9 ≤ (x : ℝ) := by
    have hmm := mul_le_mul hsx_lo hsx_lo (by positivity) (Real.sqrt_nonneg _)
    nlinarith [hmm, hsxsq]
  have hx_hi : (x : ℝ) < ((T : ℝ) + 1) ^ 2 / 9 := by
    have hsxnn : 0 ≤ Real.sqrt (x : ℝ) := Real.sqrt_nonneg _
    nlinarith [hsxsq, hsx_hi, hsxnn]
  -- window membership: aT ≤ z ≤ bT  (nat), with aT = (T+1)²/9 − 2T, bT = T²/9 − T
  rw [commonValueWindow, Finset.mem_Icc] at hz
  obtain ⟨hza, hzb⟩ := hz
  -- real bounds on aT, bT
  obtain ⟨hd1lo, hd1hi⟩ := cast_div9_bounds ((T + 1) ^ 2)
  obtain ⟨hd2lo, hd2hi⟩ := cast_div9_bounds (T ^ 2)
  -- 2T ≤ (T+1)²/9 and T ≤ T²/9 (so nat subs are genuine, casts behave)
  have h2T_le : 2 * T ≤ (T + 1) ^ 2 / 9 := by
    have : 18 * T ≤ (T + 1) ^ 2 := by nlinarith [hT100]
    omega
  have hT_le : T ≤ T ^ 2 / 9 := by
    have : 9 * T ≤ T ^ 2 := by nlinarith [hT100]
    omega
  -- cast the nat endpoints
  -- real lower bound on ↑((T+1)²/9)
  have hd1lo' : ((T : ℝ) + 1) ^ 2 / 9 - 1 ≤ (((T + 1) ^ 2 / 9 : ℕ) : ℝ) := by
    have he : (((T + 1) ^ 2 : ℕ) : ℝ) = ((T : ℝ) + 1) ^ 2 := by push_cast; ring
    rw [he] at hd1lo; linarith
  -- real upper bound on ↑(T²/9)
  have hd2hi' : (((T ^ 2 / 9 : ℕ)) : ℝ) ≤ (T : ℝ) ^ 2 / 9 := by
    have he : (((T ^ 2 : ℕ)) : ℝ) = (T : ℝ) ^ 2 := by push_cast; ring
    rw [he] at hd2hi; linarith
  have hza_real : ((T : ℝ) + 1) ^ 2 / 9 - 1 - 2 * (T : ℝ) ≤ (z : ℝ) := by
    have hzaR : (((T + 1) ^ 2 / 9 : ℕ) : ℝ) - 2 * (T : ℝ) ≤ (z : ℝ) := by
      have hc : (((T + 1) ^ 2 / 9 - 2 * T : ℕ) : ℝ) ≤ (z : ℝ) := by exact_mod_cast hza
      rwa [Nat.cast_sub h2T_le, Nat.cast_mul, Nat.cast_ofNat] at hc
    linarith
  have hzb_real : (z : ℝ) ≤ (T : ℝ) ^ 2 / 9 - (T : ℝ) := by
    have hzbR : (z : ℝ) ≤ (((T ^ 2 / 9 : ℕ)) : ℝ) - (T : ℝ) := by
      have hc : (z : ℝ) ≤ (((T ^ 2 / 9 - T : ℕ)) : ℝ) := by exact_mod_cast hzb
      rwa [Nat.cast_sub hT_le] at hc
    linarith
  -- z < x
  have hzltx : z < x := by
    have : (z : ℝ) < (x : ℝ) := by
      have : (z : ℝ) ≤ (T : ℝ) ^ 2 / 9 - T := hzb_real
      have hTge1 : (1 : ℝ) ≤ (T : ℝ) := by linarith
      nlinarith [hx_lo, this, hTge1]
    exact_mod_cast this
  -- 1 ≤ z
  have h1z : 1 ≤ z := by
    have : (1 : ℝ) ≤ (z : ℝ) := by
      have hlb : ((T : ℝ) + 1) ^ 2 / 9 - 1 - 2 * (T : ℝ) ≤ (z : ℝ) := hza_real
      nlinarith [hlb, hTR]
    exact_mod_cast this
  -- jump bounds in ℝ via (x - z : ℕ) = x - z
  have hsub_cast : ((x - z : ℕ) : ℝ) = (x : ℝ) - (z : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hzltx)]
  refine ⟨h1z, hzltx, ?_, ?_, ?_⟩
  · -- x − z ≥ T : x ≥ T²/9, z ≤ T²/9 − T
    rw [hsub_cast]; linarith [hx_lo, hzb_real]
  · -- x − z ≤ 3T : x < (T+1)²/9, z ≥ (T+1)²/9 − 1 − 2T  ⟹ x − z < 2T + 1 ≤ 3T
    rw [hsub_cast]
    have hdiff : (x : ℝ) - (z : ℝ) < 2 * (T : ℝ) + 1 := by
      linarith [hx_hi, hza_real]
    linarith [hdiff, hTR]
  · -- √x − √z ≤ 10 :  ≤ (x − z)/√x ≤ (2T+1)/(T/3) ≤ 7 ≤ 10
    have hsz_nn : 0 ≤ Real.sqrt (z : ℝ) := Real.sqrt_nonneg _
    have hsx_pos : 0 < Real.sqrt (x : ℝ) := by
      have : (T : ℝ) / 3 ≤ Real.sqrt (x : ℝ) := hsx_lo; linarith
    -- (√x − √z)(√x + √z) = x − z
    have hszsq : Real.sqrt (z : ℝ) ^ 2 = (z : ℝ) := Real.sq_sqrt (by positivity)
    have hprod : (Real.sqrt (x : ℝ) - Real.sqrt (z : ℝ)) * (Real.sqrt (x : ℝ) + Real.sqrt (z : ℝ))
        = (x : ℝ) - (z : ℝ) := by nlinarith [hsxsq, hszsq]
    have hxz_ub : (x : ℝ) - (z : ℝ) < 2 * (T : ℝ) + 1 := by
      linarith [hx_hi, hza_real]
    -- √x + √z ≥ √x ≥ T/3
    have hsum_lo : (T : ℝ) / 3 ≤ Real.sqrt (x : ℝ) + Real.sqrt (z : ℝ) := by linarith [hsx_lo, hsz_nn]
    have hgap_nn : 0 ≤ Real.sqrt (x : ℝ) - Real.sqrt (z : ℝ) := by
      have hle : Real.sqrt (z : ℝ) ≤ Real.sqrt (x : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast le_of_lt hzltx)
      linarith
    -- gap·(T/3) ≤ gap·sum = x−z < 2T+1, so gap·T < 6T+3, gap < 7 ≤ 10
    set g := Real.sqrt (x : ℝ) - Real.sqrt (z : ℝ) with hgdef
    set s := Real.sqrt (x : ℝ) + Real.sqrt (z : ℝ) with hsdef
    have hgs : g * s < 2 * (T : ℝ) + 1 := by rw [hprod]; exact hxz_ub
    have hgT : g * ((T : ℝ) / 3) ≤ g * s := by
      apply mul_le_mul_of_nonneg_left hsum_lo hgap_nn
    have hgT2 : g * (T : ℝ) < 6 * (T : ℝ) + 3 := by nlinarith [hgT, hgs]
    nlinarith [hgT2, hTR, hgap_nn]

#print axioms commonValueWindow_jump_bounds

end AnalyticCombinatorics.Ch8.Partitions.Erdos
