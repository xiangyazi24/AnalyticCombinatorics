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

/-! ## Brick 4 — the window lies in the in-band slice. -/

set_option maxHeartbeats 800000 in
/-- **Window ⊆ in-band slice.**  For a growing band width `A` (`A R → ∞`), eventually in `R` every
`z` in the window of the ceiling rank `T = R + A R` satisfies `R ≤ rnk z < T`, i.e. lies in the
engine slice `(ceilBand R (A R)).filter (R ≤ rnk ·)`. -/
lemma commonValueWindow_subset_slice (A : ℕ → ℕ) (hA : Tendsto A atTop atTop) :
    ∀ᶠ R in atTop, ∀ z, z ∈ commonValueWindow (R + A R) →
      z ∈ (ceilBand R (A R)).filter (fun z => R ≤ rnk z) := by
  -- A R ≥ 9 eventually, and R + A R ≥ 45 eventually (since A R → ∞)
  have hA9 : ∀ᶠ R in atTop, 9 ≤ A R := hA (eventually_ge_atTop 9)
  filter_upwards [hA9, eventually_ge_atTop 45] with R hA9R hR45
  intro z hz
  set T := R + A R with hTdef
  have hT45 : 45 ≤ T := by omega
  have hTR : (45 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT45
  rw [commonValueWindow, Finset.mem_Icc] at hz
  obtain ⟨hza, hzb⟩ := hz
  -- real endpoint bounds (same casts as brick 3)
  obtain ⟨hd1lo, _⟩ := cast_div9_bounds ((T + 1) ^ 2)
  obtain ⟨_, hd2hi⟩ := cast_div9_bounds (T ^ 2)
  have h2T_le : 2 * T ≤ (T + 1) ^ 2 / 9 := by
    have : 18 * T ≤ (T + 1) ^ 2 := by nlinarith [hTR]
    omega
  have hT_le : T ≤ T ^ 2 / 9 := by
    have : 9 * T ≤ T ^ 2 := by nlinarith [hTR]
    omega
  have hd1lo' : ((T : ℝ) + 1) ^ 2 / 9 - 1 ≤ (((T + 1) ^ 2 / 9 : ℕ) : ℝ) := by
    have he : (((T + 1) ^ 2 : ℕ) : ℝ) = ((T : ℝ) + 1) ^ 2 := by push_cast; ring
    rw [he] at hd1lo; linarith
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
  have hznn : (0 : ℝ) ≤ (z : ℝ) := Nat.cast_nonneg z
  -- rnk z < T : 3√z < T from z < T²/9
  have hrnk_lt : rnk z < T := by
    unfold rnk
    have hsz : 3 * Real.sqrt (z : ℝ) < (T : ℝ) := by
      have hzlt : (z : ℝ) < (T : ℝ) ^ 2 / 9 := by linarith [hzb_real, hTR]
      have hsqlt : Real.sqrt (z : ℝ) < (T : ℝ) / 3 := by
        rw [show (T : ℝ) / 3 = Real.sqrt (((T : ℝ) / 3) ^ 2) by
          rw [Real.sqrt_sq (by positivity)]]
        apply Real.sqrt_lt_sqrt hznn
        nlinarith [hzlt]
      linarith
    have : (⌊3 * Real.sqrt (z : ℝ)⌋₊ : ℝ) ≤ 3 * Real.sqrt (z : ℝ) := Nat.floor_le (by positivity)
    have hfl : (⌊3 * Real.sqrt (z : ℝ)⌋₊ : ℝ) < (T : ℝ) := by linarith
    exact_mod_cast hfl
  -- R ≤ rnk z : 3√z ≥ T − 9 ≥ R from z ≥ (T+1)²/9 − 2T − 1
  have hR_le : R ≤ rnk z := by
    have hRle : R ≤ T - 9 := by omega
    refine le_trans hRle ?_
    unfold rnk
    apply Nat.le_floor
    -- need (T − 9 : ℝ) ≤ 3√z, i.e. 9z ≥ (T−9)²
    have h9z : (T : ℝ) ^ 2 - 16 * (T : ℝ) - 8 ≤ 9 * (z : ℝ) := by
      have : 9 * (((T : ℝ) + 1) ^ 2 / 9 - 1 - 2 * (T : ℝ)) ≤ 9 * (z : ℝ) := by linarith [hza_real]
      nlinarith [this]
    have hsq : ((T - 9 : ℕ) : ℝ) ^ 2 ≤ 9 * (z : ℝ) := by
      have hcast : ((T - 9 : ℕ) : ℝ) = (T : ℝ) - 9 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [hcast]
      nlinarith [h9z, hTR]
    -- (T−9) ≤ 3√z  ⟸  (T−9)² ≤ 9z = (3√z)²
    have hszsq : (3 * Real.sqrt (z : ℝ)) ^ 2 = 9 * (z : ℝ) := by
      rw [mul_pow]; rw [Real.sq_sqrt hznn]; ring
    have hTm9nn : (0 : ℝ) ≤ ((T - 9 : ℕ) : ℝ) := Nat.cast_nonneg _
    have h3snn : (0 : ℝ) ≤ 3 * Real.sqrt (z : ℝ) := by positivity
    nlinarith [hsq, hszsq, hTm9nn, h3snn]
  rw [Finset.mem_filter]
  exact ⟨mem_ceilBand_iff.mpr hrnk_lt, hR_le⟩

#print axioms commonValueWindow_subset_slice

/-! ## Brick 5 — pointwise `Pker` lower bound on the window. -/

set_option maxHeartbeats 1000000 in
/-- **Pointwise `Pker` lower bound.**  There is `c > 0` so that eventually in the ceiling rank `T`,
for every value `x` of rank `T` and every `z` in the common window, `c/T ≤ Pker x z`.  Uses only the
divisor-self bound `σ(x−z) ≥ x−z ≥ T`, the window upper bound `z ≤ T²/9`, the sqrt-gap bound
`√x−√z ≤ 10`, and the eventual `kernelMass x ≤ 2`. -/
lemma Pker_commonValueWindow_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ T in atTop, ∀ x z, rnk x = T → z ∈ commonValueWindow T →
      c / (T : ℝ) ≤ Pker x z := by
  obtain ⟨K, hKpos, hKev⟩ := kernelMass_sub_one_rate
  -- eventual K/n ≤ 1/2 ⟹ kernelMass ∈ [1/2, 3/2] ⊆ (0,2]
  have hhalf : ∀ᶠ n : ℕ in atTop, K / (n : ℝ) ≤ 1 / 2 := by
    have htend : Tendsto (fun n : ℕ => K / (n : ℝ)) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop)
    exact htend.eventually_le_const (by norm_num)
  obtain ⟨Nkm, hNkm⟩ := eventually_atTop.1 (hKev.and hhalf)
  obtain ⟨Tj, hTj⟩ := eventually_atTop.1 commonValueWindow_jump_bounds
  refine ⟨(9 / 2) * Real.exp (-(10 * C)), by positivity, ?_⟩
  -- choose T large: ≥ 100 (jump), ≥ Tj, and rnk x = T forces x ≥ Nkm
  filter_upwards [eventually_ge_atTop (max (max 100 Tj) (3 * Nkm + 3))] with T hTbig
  intro x z hx hz
  have hT100 : 100 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hTbig
  have hTjle : Tj ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hTbig
  have hTR : (100 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT100
  have hTpos : (0 : ℝ) < (T : ℝ) := by linarith
  -- jump/geometry facts
  obtain ⟨h1z, hzltx, hjlo, _hjhi, hsqrt⟩ := hTj T hTjle x z hx hz
  -- x ≥ Nkm (from rnk x = T and T large)
  have hxge : Nkm ≤ x := by
    apply rnk_ge_of (n₀ := Nkm)
    rw [hx]
    have : 3 * Nkm + 3 ≤ T := le_trans (le_max_right _ _) hTbig
    omega
  obtain ⟨hKx, hhalfx⟩ := hNkm x hxge
  have hxR : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  obtain ⟨hSlo, hSup⟩ := abs_le.1 hKx
  have hS2 : kernelMass x ≤ 2 := by linarith [hSup, hhalfx]
  have hSpos : (0 : ℝ) < kernelMass x := by linarith [hSlo, hhalfx]
  -- z and (x−z) bounds
  have hzR : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast h1z
  have hzpos : (0 : ℝ) < (z : ℝ) := by linarith
  -- z ≤ T²/9  (from window upper edge)
  have hz_ub : (z : ℝ) ≤ (T : ℝ) ^ 2 / 9 := by
    rw [commonValueWindow, Finset.mem_Icc] at hz
    obtain ⟨_, hzb⟩ := hz
    obtain ⟨_, hd2hi⟩ := cast_div9_bounds (T ^ 2)
    have hT_le : T ≤ T ^ 2 / 9 := by
      have : 9 * T ≤ T ^ 2 := by nlinarith [hTR]
      omega
    have hd2hi' : (((T ^ 2 / 9 : ℕ)) : ℝ) ≤ (T : ℝ) ^ 2 / 9 := by
      have he : (((T ^ 2 : ℕ)) : ℝ) = (T : ℝ) ^ 2 := by push_cast; ring
      rw [he] at hd2hi; linarith
    have hzbR : (z : ℝ) ≤ (((T ^ 2 / 9 : ℕ)) : ℝ) - (T : ℝ) := by
      have hc : (z : ℝ) ≤ (((T ^ 2 / 9 - T : ℕ)) : ℝ) := by exact_mod_cast hzb
      rwa [Nat.cast_sub hT_le] at hc
    linarith
  -- expand Pker
  have hPeq : Pker x z = erdosWeight x (x - z) / kernelMass x := by
    unfold Pker; rw [if_pos ⟨h1z, hzltx⟩]
  -- erdosWeight x (x−z) = σ(x−z)/z · exp(−C(√x − √z))   [since x − (x−z) = z]
  have hxsub : x - (x - z) = z := by omega
  have hew : erdosWeight x (x - z)
      = Sigma.sigmaR (x - z) / (z : ℝ) * Real.exp (-C * (Real.sqrt (x : ℝ) - Real.sqrt (z : ℝ))) := by
    unfold erdosWeight
    rw [hxsub]
  -- σ(x−z) ≥ T
  have hsig : (T : ℝ) ≤ Sigma.sigmaR (x - z) := by
    have h1 : 1 ≤ x - z := by omega
    exact le_trans hjlo (sigmaR_ge_self (m := x - z) h1)
  -- exponential factor ≥ exp(−10C)
  have hexp : Real.exp (-(10 * C)) ≤ Real.exp (-C * (Real.sqrt (x : ℝ) - Real.sqrt (z : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have hCpos := C_pos
    nlinarith [hsqrt, hCpos]
  -- erdosWeight ≥ (T/z)·exp(−10C) ≥ (9/T)·exp(−10C)
  have hew_lb : (9 / (T : ℝ)) * Real.exp (-(10 * C)) ≤ erdosWeight x (x - z) := by
    rw [hew]
    have hsigz : (T : ℝ) / (z : ℝ) ≤ Sigma.sigmaR (x - z) / (z : ℝ) := by
      gcongr
    have hTz : (9 : ℝ) / (T : ℝ) ≤ (T : ℝ) / (z : ℝ) := by
      rw [div_le_div_iff₀ hTpos hzpos]
      nlinarith [hz_ub, hTpos]
    have hch : (9 / (T : ℝ)) ≤ Sigma.sigmaR (x - z) / (z : ℝ) := le_trans hTz hsigz
    have hexpnn : (0 : ℝ) ≤ Real.exp (-(10 * C)) := (Real.exp_pos _).le
    calc (9 / (T : ℝ)) * Real.exp (-(10 * C))
        ≤ (Sigma.sigmaR (x - z) / (z : ℝ)) * Real.exp (-(10 * C)) :=
          mul_le_mul_of_nonneg_right hch hexpnn
      _ ≤ (Sigma.sigmaR (x - z) / (z : ℝ))
            * Real.exp (-C * (Real.sqrt (x : ℝ) - Real.sqrt (z : ℝ))) := by
          apply mul_le_mul_of_nonneg_left hexp
          exact div_nonneg (sigmaR_nonneg _) hzpos.le
  -- divide by kernelMass x ≤ 2
  rw [hPeq, le_div_iff₀ hSpos]
  -- goal:  (9/2)·exp(−10C)/T · kernelMass x ≤ erdosWeight x (x−z)
  calc (9 / 2) * Real.exp (-(10 * C)) / (T : ℝ) * kernelMass x
      ≤ (9 / 2) * Real.exp (-(10 * C)) / (T : ℝ) * 2 := by
        apply mul_le_mul_of_nonneg_left hS2
        positivity
    _ = (9 / (T : ℝ)) * Real.exp (-(10 * C)) := by
          rw [div_mul_eq_mul_div]; field_simp
    _ ≤ erdosWeight x (x - z) := hew_lb

#print axioms Pker_commonValueWindow_lower

/-! ## Brick 6 — linear cardinality of the window. -/

set_option maxHeartbeats 800000 in
/-- **Linear window cardinality.**  `(1/2)·T ≤ |W_T|` eventually (the real window length is
`(7T−1)/9`, so any `q < 7/9` works; `q = 1/2` with margin). -/
lemma commonValueWindow_card_linear :
    ∀ᶠ T : ℕ in atTop, (1 / 2 : ℝ) * (T : ℝ) ≤ ((commonValueWindow T).card : ℝ) := by
  filter_upwards [eventually_ge_atTop 100] with T hT100
  have hTR : (100 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT100
  -- nat sub validity
  have h2T_le : 2 * T ≤ (T + 1) ^ 2 / 9 := by
    have : 18 * T ≤ (T + 1) ^ 2 := by nlinarith [hTR]
    omega
  have hT_le : T ≤ T ^ 2 / 9 := by
    have : 9 * T ≤ T ^ 2 := by nlinarith [hTR]
    omega
  -- cast bounds
  obtain ⟨hd1lo, hd1hi⟩ := cast_div9_bounds ((T + 1) ^ 2)
  obtain ⟨hd2lo, hd2hi⟩ := cast_div9_bounds (T ^ 2)
  rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one] at hd1lo hd1hi
  rw [Nat.cast_pow] at hd2lo hd2hi
  -- real bounds on a, b
  have ha_ub : (((T + 1) ^ 2 / 9 - 2 * T : ℕ) : ℝ) ≤ ((T : ℝ) + 1) ^ 2 / 9 - 2 * (T : ℝ) := by
    rw [Nat.cast_sub h2T_le, Nat.cast_mul, Nat.cast_ofNat]; linarith [hd1hi]
  have hb_lb : (T : ℝ) ^ 2 / 9 - 1 - (T : ℝ) ≤ (((T ^ 2 / 9 - T : ℕ)) : ℝ) := by
    rw [Nat.cast_sub hT_le]; linarith [hd2lo]
  -- a ≤ b (so Icc nonempty)
  have hab : (T + 1) ^ 2 / 9 - 2 * T ≤ T ^ 2 / 9 - T := by
    have hr : (((T + 1) ^ 2 / 9 - 2 * T : ℕ) : ℝ) ≤ (((T ^ 2 / 9 - T : ℕ)) : ℝ) := by
      nlinarith [ha_ub, hb_lb, hTR]
    exact_mod_cast hr
  -- card = b + 1 − a
  rw [commonValueWindow, Nat.card_Icc]
  have hcard_cast : ((T ^ 2 / 9 - T + 1 - ((T + 1) ^ 2 / 9 - 2 * T) : ℕ) : ℝ)
      = (((T ^ 2 / 9 - T : ℕ)) : ℝ) + 1 - (((T + 1) ^ 2 / 9 - 2 * T : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  rw [hcard_cast]
  -- (b+1−a) ≥ (T²/9 − 1 − T) + 1 − ((T+1)²/9 − 2T) = (7T−1)/9 ≥ T/2
  nlinarith [ha_ub, hb_lb, hTR]

#print axioms commonValueWindow_card_linear

/-! ## Brick 7 — one-step same-ceiling value overlap. -/

/-- The ceiling rank `R ↦ R + A R` tends to `atTop` (since `R + A R ≥ R`). -/
lemma ceilRank_tendsto (A : ℕ → ℕ) : Tendsto (fun R => R + A R) atTop atTop :=
  tendsto_atTop_mono (fun R => Nat.le_add_right R (A R)) tendsto_id

set_option maxHeartbeats 800000 in
/-- **One-step same-ceiling value overlap (L4 one-step form).**  There is `β > 0` so that eventually
in `R`, any two values `x, y` of the ceiling rank `T = R + A R` have one-step predecessor overlap
`≥ β` on the in-band slice.  Via `overlap_ge_of_minorization` with the uniform window minorant
`η = c/T` (brick 5) on `S = commonValueWindow T` of card `≥ T/2` (brick 6), inside the slice
(brick 4):  `η·|S| ≥ (c/T)(T/2) = c/2 =: β`. -/
lemma Pker_same_ceiling_oneStep_overlap (A : ℕ → ℕ) (hA : Tendsto A atTop atTop) :
    ∃ β : ℝ, 0 < β ∧
      ∀ᶠ R in atTop, ∀ x y, rnk x = R + A R → rnk y = R + A R →
        β ≤ ∑ z ∈ (ceilBand R (A R)).filter (fun z => R ≤ rnk z),
              min (Pker x z) (Pker y z) := by
  obtain ⟨c, hcpos, hclow⟩ := Pker_commonValueWindow_lower
  refine ⟨c / 2, by positivity, ?_⟩
  have htend := ceilRank_tendsto A
  -- pull the T-eventual facts (brick 5, brick 6) to R-eventual along T = R + A R
  have hlowR : ∀ᶠ R in atTop, ∀ x z, rnk x = R + A R → z ∈ commonValueWindow (R + A R) →
      c / ((R + A R : ℕ) : ℝ) ≤ Pker x z := htend.eventually hclow
  have hcardR : ∀ᶠ R in atTop, (1 / 2 : ℝ) * ((R + A R : ℕ) : ℝ)
      ≤ ((commonValueWindow (R + A R)).card : ℝ) := htend.eventually commonValueWindow_card_linear
  have hsliceR := commonValueWindow_subset_slice A hA
  have hTposR : ∀ᶠ R : ℕ in atTop, (0 : ℝ) < ((R + A R : ℕ) : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with R hR
    have : (1 : ℝ) ≤ ((R + A R : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ R + A R)
    linarith
  filter_upwards [hlowR, hcardR, hsliceR, hTposR] with R hlow hcard hslice hTpos
  intro x y hx hy
  set T : ℕ := R + A R with hTdef
  -- minorant η = c/T on S = commonValueWindow T
  have hmin : ∀ z ∈ commonValueWindow T, c / (T : ℝ) ≤ Pker x z ∧ c / (T : ℝ) ≤ Pker y z := by
    intro z hz
    exact ⟨hlow x z hx hz, hlow y z hy hz⟩
  have hov := Renewal.overlap_ge_of_minorization
    (κ := Pker) (T := ceilBand R (A R)) (q := fun z => R ≤ rnk z)
    (S := commonValueWindow T) (n := x) (n' := y) (η := c / (T : ℝ))
    hslice (fun z => Pker_nonneg x z) (fun z => Pker_nonneg y z) hmin
  -- (c/T)·|S| ≥ (c/T)·(T/2) = c/2
  refine le_trans ?_ hov
  have hcard2 : (c / (T : ℝ)) * ((1 / 2 : ℝ) * (T : ℝ))
      ≤ (c / (T : ℝ)) * ((commonValueWindow T).card : ℝ) := by
    apply mul_le_mul_of_nonneg_left hcard
    positivity
  have hsimp : (c / (T : ℝ)) * ((1 / 2 : ℝ) * (T : ℝ)) = c / 2 := by
    field_simp
  rw [hsimp] at hcard2
  exact hcard2

#print axioms Pker_same_ceiling_oneStep_overlap

/-! ## Brick 8 — lift to the first-entrance overlap (this is L4). -/

set_option maxHeartbeats 800000 in
/-- **L4 — same-ceiling first-entrance value overlap.**  There is `β > 0` so that eventually in `R`,
any two values `x, y` of the ceiling rank `T = R + A R` have *first-entrance* overlap `≥ β` on the
in-band slice into the band `ceilBand R (A R)`.  Lifts the one-step overlap (brick 7) via the banked
`min_Pker_le_min_enterBandKer_sum` (`Pker x z ≤ enterBandKer Pker B x z` on in-band targets). -/
lemma same_ceiling_enterBand_overlap (A : ℕ → ℕ) (hA : Tendsto A atTop atTop) :
    ∃ β : ℝ, 0 < β ∧
      ∀ᶠ R in atTop, ∀ x y, rnk x = R + A R → rnk y = R + A R →
        β ≤ ∑ z ∈ (ceilBand R (A R)).filter (fun z => R ≤ rnk z),
              min (enterBandKer Pker (ceilBand R (A R)) x z)
                  (enterBandKer Pker (ceilBand R (A R)) y z) := by
  obtain ⟨β, hβpos, hβev⟩ := Pker_same_ceiling_oneStep_overlap A hA
  refine ⟨β, hβpos, ?_⟩
  filter_upwards [hβev] with R hβR
  intro x y hx hy
  set B := ceilBand R (A R) with hBdef
  set slice := B.filter (fun z => R ≤ rnk z) with hslicedef
  -- x, y are off the band (rank = R + A R, band is {rnk < R + A R})
  have hxB : x ∉ B := by rw [hBdef, mem_ceilBand_iff]; omega
  have hyB : y ∉ B := by rw [hBdef, mem_ceilBand_iff]; omega
  -- in-band slice targets z satisfy z ∈ B, z < x, z < y (rnk z < rnk x = rnk y ⟹ z < x via rnk_mono)
  have hsliceH : ∀ z ∈ slice, z ∈ B ∧ z < x ∧ z < y := by
    intro z hz
    rw [hslicedef, Finset.mem_filter] at hz
    obtain ⟨hzB, _hzR⟩ := hz
    have hzrnk : rnk z < R + A R := mem_ceilBand_iff.mp hzB
    refine ⟨hzB, ?_, ?_⟩
    · -- z < x : else rnk x ≤ rnk z < R+A R = rnk x, contradiction
      by_contra hxz
      push_neg at hxz
      have : rnk x ≤ rnk z := rnk_mono hxz
      omega
    · by_contra hyz
      push_neg at hyz
      have : rnk y ≤ rnk z := rnk_mono hyz
      omega
  have hlift := min_Pker_le_min_enterBandKer_sum (B := B) (slice := slice)
    (x := x) (y := y) hxB hyB hsliceH
  exact le_trans (hβR x y hx hy) hlift

#print axioms same_ceiling_enterBand_overlap

end AnalyticCombinatorics.Ch8.Partitions.Erdos
