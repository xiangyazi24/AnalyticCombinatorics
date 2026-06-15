import AnalyticCombinatorics.Ch8.Partitions.ErdosMinorization
import AnalyticCombinatorics.Ch8.Partitions.VarianceLower
import AnalyticCombinatorics.Ch8.Partitions.KhatRes

/-!
# Concrete `v0`: single-chain jump-window mass for the Erdős kernel (renewal route B)

Builds toward the positive local-variance input `v0 > 0`.  `Pker_subwindow_mass` lower-bounds the
single-chain `Pker x ·` mass on a jump sub-window `[a, b] ⊆ [⌊√x⌋, 2⌊√x⌋]` via the banked per-term
`Pker_lower`.  Splitting the window into a LOW and a HIGH jump sub-window gives two separated
ρ-decrement clumps, which `product_locVar_ge` (VarianceLower) turns into `v0 > 0`.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Single-chain mass on a jump sub-window `[a,b] ⊆ [s, 2s]` (`s = ⌊√x⌋`), via `Pker_lower`:
each term is `≥ a·e^{-2C}/(2x)`, and there are `b−a+1` of them. -/
lemma Pker_subwindow_mass {x : ℕ} (hx16 : 16 ≤ x)
    (hkmx : kernelMass x ≤ 2) (hkmx0 : 0 < kernelMass x)
    {a b : ℕ} (ha : Nat.sqrt x ≤ a) (hab : a ≤ b) (hb2 : b ≤ 2 * Nat.sqrt x) :
    ((b - a + 1 : ℕ) : ℝ) * ((a : ℝ) * Real.exp (-C * 2) / (2 * (x:ℝ)))
      ≤ ∑ k ∈ Finset.Icc (x - b) (x - a), Pker x k := by
  have hCpos := C_pos
  set s := Nat.sqrt x with hs
  have hs4 : 4 ≤ s := by
    rw [hs]; calc 4 = Nat.sqrt 16 := by norm_num
      _ ≤ Nat.sqrt x := Nat.sqrt_le_sqrt hx16
  have hssx : s * s ≤ x := by rw [hs, ← pow_two]; exact Nat.sqrt_le' x
  have h2sx : 2 * s ≤ x := by nlinarith [hssx, hs4]
  have h2s1x : 2 * s + 1 ≤ x := by nlinarith [hssx, hs4]
  have hbx : b ≤ x := le_trans hb2 h2sx
  have hax : a ≤ x := le_trans hab hbx
  have ha1 : 1 ≤ a := le_trans (by omega) ha
  have hxpos : (0 : ℝ) < (x : ℝ) := by positivity
  have hsqrtx : (0 : ℝ) < Real.sqrt (x : ℝ) := Real.sqrt_pos.mpr hxpos
  have hsx2 : (s : ℝ) * (s : ℝ) ≤ (x : ℝ) := by exact_mod_cast hssx
  have hsle_sqrt : (s : ℝ) ≤ Real.sqrt (x : ℝ) := by
    rw [show (s : ℝ) = Real.sqrt ((s : ℝ) * (s : ℝ)) from (Real.sqrt_mul_self (by positivity)).symm]
    exact Real.sqrt_le_sqrt hsx2
  -- per-term lower bound, uniform over the window
  have hperterm : ∀ k ∈ Finset.Icc (x - b) (x - a),
      (a : ℝ) * Real.exp (-C * 2) / (2 * (x:ℝ)) ≤ Pker x k := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    obtain ⟨hk1', hk2'⟩ := hk
    have hk_lt_x : k < x := by omega
    have hk_ge1 : 1 ≤ k := by omega
    have hxk_cast : ((x - k : ℕ) : ℝ) = (x : ℝ) - (k : ℝ) := by rw [Nat.cast_sub hk_lt_x.le]
    -- jump bounds: a ≤ x - k ≤ b
    have hjlo : a ≤ x - k := by omega
    have hjhi : x - k ≤ b := by omega
    -- J = a ≤ (x-k)
    have hJ : (a : ℝ) ≤ ((x - k : ℕ) : ℝ) := by exact_mod_cast hjlo
    -- T = 2 : √x − √k ≤ 2
    have hT : Real.sqrt (x : ℝ) - Real.sqrt (k : ℝ) ≤ 2 := by
      refine le_trans (sqrt_sub_le hk_ge1 hk_lt_x.le) ?_
      rw [div_le_iff₀ hsqrtx]
      have hxk2s : ((x : ℝ) - (k : ℝ)) ≤ 2 * (s : ℝ) := by
        rw [← hxk_cast]; exact_mod_cast le_trans hjhi hb2
      nlinarith [hxk2s, hsle_sqrt, hsqrtx]
    exact Pker_lower hk_ge1 hk_lt_x hkmx hkmx0 (by positivity) hJ hT
  -- sum ≥ card • perterm
  have hcard : (Finset.Icc (x - b) (x - a)).card = b - a + 1 := by
    rw [Nat.card_Icc]
    omega
  calc ((b - a + 1 : ℕ) : ℝ) * ((a : ℝ) * Real.exp (-C * 2) / (2 * (x:ℝ)))
      = ((Finset.Icc (x - b) (x - a)).card : ℝ) * ((a : ℝ) * Real.exp (-C * 2) / (2 * (x:ℝ))) := by
        rw [hcard]
    _ ≤ ∑ k ∈ Finset.Icc (x - b) (x - a), Pker x k := by
        rw [← nsmul_eq_mul]
        exact Finset.card_nsmul_le_sum _ _ _ hperterm

/-- Lower bound on the √-decrement: `√x − √k ≥ (x−k)/(2√x)`. -/
lemma sqrt_decrement_lower {x k : ℕ} (hk : k < x) :
    ((x - k : ℕ) : ℝ) / (2 * Real.sqrt x) ≤ Real.sqrt (x : ℝ) - Real.sqrt (k : ℝ) := by
  have hxk : ((x - k : ℕ) : ℝ) = (x : ℝ) - (k : ℝ) := Nat.cast_sub hk.le
  have hkx : (k : ℝ) ≤ (x : ℝ) := by exact_mod_cast hk.le
  have hsk : Real.sqrt (k : ℝ) ≤ Real.sqrt (x : ℝ) := Real.sqrt_le_sqrt hkx
  have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le k) hk)
  have hsx : 0 < Real.sqrt (x : ℝ) := Real.sqrt_pos.mpr hx0
  rw [hxk, div_le_iff₀ (by positivity)]
  have hid : ((x : ℝ) - (k : ℝ))
      = (Real.sqrt (x : ℝ) - Real.sqrt (k : ℝ)) * (Real.sqrt (x : ℝ) + Real.sqrt (k : ℝ)) := by
    have h1 : Real.sqrt (x : ℝ) ^ 2 = (x : ℝ) := Real.sq_sqrt (by positivity)
    have h2 : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt (by positivity)
    nlinarith [h1, h2]
  rw [hid]
  exact mul_le_mul_of_nonneg_left (by linarith [hsk]) (by linarith [hsk])

/-- Upper bound on the √-decrement when `√k ≥ ρ√x` (`0 ≤ ρ`):
`√x − √k ≤ (1/(1+ρ))(x−k)/√x`. -/
lemma sqrt_decrement_upper {x k : ℕ} {ρ : ℝ} (hk : k < x) (hρ0 : 0 ≤ ρ)
    (hkge : ρ * Real.sqrt (x : ℝ) ≤ Real.sqrt (k : ℝ)) :
    Real.sqrt (x : ℝ) - Real.sqrt (k : ℝ) ≤ 1 / (1 + ρ) * ((x - k : ℕ) : ℝ) / Real.sqrt (x : ℝ) := by
  have hxk : ((x - k : ℕ) : ℝ) = (x : ℝ) - (k : ℝ) := Nat.cast_sub hk.le
  have hkx : (k : ℝ) ≤ (x : ℝ) := by exact_mod_cast hk.le
  have hsk : Real.sqrt (k : ℝ) ≤ Real.sqrt (x : ℝ) := Real.sqrt_le_sqrt hkx
  have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le k) hk)
  have hsx : 0 < Real.sqrt (x : ℝ) := Real.sqrt_pos.mpr hx0
  have h1ρ : 0 < 1 + ρ := by linarith
  have hid : ((x : ℝ) - (k : ℝ))
      = (Real.sqrt (x : ℝ) - Real.sqrt (k : ℝ)) * (Real.sqrt (x : ℝ) + Real.sqrt (k : ℝ)) := by
    have h1 : Real.sqrt (x : ℝ) ^ 2 = (x : ℝ) := Real.sq_sqrt (by positivity)
    have h2 : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt (by positivity)
    nlinarith [h1, h2]
  rw [hxk, hid, le_div_iff₀ hsx,
    show (1 : ℝ) / (1 + ρ) * ((Real.sqrt (x : ℝ) - Real.sqrt (k : ℝ)) *
      (Real.sqrt (x : ℝ) + Real.sqrt (k : ℝ)))
      = ((Real.sqrt (x : ℝ) - Real.sqrt (k : ℝ)) *
          (Real.sqrt (x : ℝ) + Real.sqrt (k : ℝ))) / (1 + ρ) by ring,
    le_div_iff₀ h1ρ]
  -- (√x-√k)·√x·(1+ρ) ≤ (√x-√k)(√x+√k)
  nlinarith [mul_nonneg (sub_nonneg.mpr hsk) (sub_nonneg.mpr hkge), hsx, hρ0]

/-- `⌊√x⌋ ≥ (4/5)√x` for `x ≥ 25`. -/
lemma sqrt_floor_lower {x : ℕ} (hx : 25 ≤ x) :
    (4 : ℝ) / 5 * Real.sqrt (x : ℝ) ≤ (Nat.sqrt x : ℝ) := by
  have hlt : Real.sqrt (x : ℝ) < (Nat.sqrt x : ℝ) + 1 := by
    rw [Real.sqrt_lt' (by positivity), sq]
    exact_mod_cast Nat.lt_succ_sqrt x
  have h5 : (5 : ℝ) ≤ Real.sqrt (x : ℝ) := by
    rw [show (5 : ℝ) = Real.sqrt 25 by
      rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hx)
  linarith

/-- For `b ≥ y − 5⌊√y⌋/4` with `y ≥ 25`, the predecessor satisfies `√b ≥ (5/6)√y`. -/
lemma sqrt_ge_low {y b : ℕ} (hy : 25 ≤ y) (hb : y - 5 * Nat.sqrt y / 4 ≤ b) :
    (5 : ℝ) / 6 * Real.sqrt (y : ℝ) ≤ Real.sqrt (b : ℝ) := by
  set t := Nat.sqrt y with ht
  have ht5 : 5 ≤ t := by
    rw [ht]; calc 5 = Nat.sqrt 25 := by norm_num
      _ ≤ Nat.sqrt y := Nat.sqrt_le_sqrt hy
  have ht1 : 1 ≤ t := by omega
  have htty : t * t ≤ y := by rw [ht, ← pow_two]; exact Nat.sqrt_le' y
  have h5ty : 5 * t / 4 ≤ y := by
    have h5t : 5 * t ≤ y := le_trans (by nlinarith [ht5]) htty
    omega
  have htroot : (t : ℝ) ≤ Real.sqrt (y : ℝ) := by
    rw [show (t : ℝ) = Real.sqrt ((t : ℝ) * (t : ℝ)) from (Real.sqrt_mul_self (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast htty)
  -- 25y/36 ≤ b
  have hbig : (25 : ℝ) / 36 * (y : ℝ) ≤ (b : ℝ) := by
    have hyb : (y : ℝ) - 5 / 4 * (t : ℝ) ≤ (b : ℝ) := by
      have hcast : ((y - 5 * t / 4 : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
      have hle : ((y - 5 * t / 4 : ℕ) : ℝ) = (y : ℝ) - ((5 * t / 4 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega)]
      have hdiv : ((5 * t / 4 : ℕ) : ℝ) ≤ 5 / 4 * (t : ℝ) := by
        have : (5 * t / 4 : ℕ) ≤ 5 * t / 4 + 0 := by omega
        have h2 : ((5 * t / 4 : ℕ) : ℝ) * 4 ≤ 5 * (t : ℝ) := by
          have := Nat.div_mul_le_self (5 * t) 4
          have : ((5 * t / 4 * 4 : ℕ) : ℝ) ≤ ((5 * t : ℕ) : ℝ) := by exact_mod_cast this
          push_cast at this; linarith
        linarith
      rw [hle] at hcast; linarith
    -- y - 5/4 t ≥ y - 5/4 √y ≥ 25/36 y  (since √y ≥ 5, y ≥ 25 ⟹ (11/36)y ≥ 5/4 √y)
    have hsqy : Real.sqrt (y : ℝ) ≤ (y : ℝ) / 5 := by
      have h5 : (5 : ℝ) ≤ Real.sqrt (y : ℝ) := by
        rw [show (5 : ℝ) = Real.sqrt 25 by
          rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hy)
      have hsq : Real.sqrt (y : ℝ) ^ 2 = (y : ℝ) := Real.sq_sqrt (by positivity)
      nlinarith [hsq, h5, Real.sqrt_nonneg (y : ℝ)]
    have htle : (t : ℝ) ≤ (y : ℝ) / 5 := le_trans htroot hsqy
    nlinarith [hyb, htle]
  -- √b ≥ √(25y/36) = 5/6 √y
  have hsqrt : Real.sqrt ((25 : ℝ) / 36 * (y : ℝ)) ≤ Real.sqrt (b : ℝ) := Real.sqrt_le_sqrt hbig
  rw [show (25 : ℝ) / 36 * (y : ℝ) = (5 / 6) ^ 2 * (y : ℝ) by norm_num,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)] at hsqrt
  exact hsqrt

/-- For `k ≥ x − 2⌊√x⌋` with `x ≥ 16`, the predecessor satisfies `√k ≥ (7/10)√x`. -/
lemma sqrt_ge_of_window {x k : ℕ} (hx16 : 16 ≤ x) (hk : x - 2 * Nat.sqrt x ≤ k) :
    (7 : ℝ) / 10 * Real.sqrt (x : ℝ) ≤ Real.sqrt (k : ℝ) := by
  set s := Nat.sqrt x with hs
  have hs4 : 4 ≤ s := by
    rw [hs]; calc 4 = Nat.sqrt 16 := by norm_num
      _ ≤ Nat.sqrt x := Nat.sqrt_le_sqrt hx16
  have hssx : s * s ≤ x := by rw [hs, ← pow_two]; exact Nat.sqrt_le' x
  have hsqrtle : Real.sqrt ((s : ℝ) * (s : ℝ)) ≤ Real.sqrt (x : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hssx)
  have hsroot : (s : ℝ) ≤ Real.sqrt (x : ℝ) := by
    rwa [Real.sqrt_mul_self (by positivity)] at hsqrtle
  -- x/2 ≤ k : from x - 2s ≤ k and 2s ≤ x/2 (since s ≤ √x and 4s ≤ x... use 4s≤x)
  have h4sx : 4 * s ≤ x := by nlinarith [hssx, hs4]
  have hxhalf : (x : ℝ) / 2 ≤ (k : ℝ) := by
    have hks : x - 2 * s ≤ k := hk
    have : (x : ℝ) - 2 * (s : ℝ) ≤ (k : ℝ) := by
      have hcast : ((x - 2 * s : ℕ) : ℝ) = (x : ℝ) - 2 * (s : ℝ) := by
        rw [Nat.cast_sub (by omega), Nat.cast_mul]; norm_num
      rw [← hcast]; exact_mod_cast hks
    have h4sxr : 4 * (s : ℝ) ≤ (x : ℝ) := by exact_mod_cast h4sx
    linarith
  -- √k ≥ √(x/2) ≥ (7/10)√x
  have hsqrt_half : Real.sqrt ((x : ℝ) / 2) ≤ Real.sqrt (k : ℝ) := Real.sqrt_le_sqrt hxhalf
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hhalf_ge : (7 : ℝ) / 10 * Real.sqrt (x : ℝ) ≤ Real.sqrt ((x : ℝ) / 2) := by
    rw [show (x : ℝ) / 2 = (x : ℝ) * (1 / 2) by ring, Real.sqrt_mul hx0]
    have hsqrt2 : (7 : ℝ) / 10 ≤ Real.sqrt (1 / 2) := by
      rw [show (1 : ℝ) / 2 = (1 / 2) by rfl]
      have : ((7 : ℝ) / 10) ^ 2 ≤ 1 / 2 := by norm_num
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/2), Real.sqrt_nonneg (1/2 : ℝ), this]
    nlinarith [hsqrt2, Real.sqrt_nonneg (x : ℝ)]
  linarith [hsqrt_half, hhalf_ge]

/-- `s² ≥ (16/25)x` for `x ≥ 25` (from `s ≥ (4/5)√x`). -/
lemma sq_floor_lower {x : ℕ} (hx : 25 ≤ x) :
    (16 : ℝ) / 25 * (x : ℝ) ≤ (Nat.sqrt x : ℝ) ^ 2 := by
  have h := sqrt_floor_lower hx
  have hsq : Real.sqrt (x : ℝ) ^ 2 = (x : ℝ) := Real.sq_sqrt (by positivity)
  nlinarith [h, hsq, Real.sqrt_nonneg (x : ℝ), (Nat.cast_nonneg (Nat.sqrt x) : (0:ℝ) ≤ (Nat.sqrt x : ℝ))]

/-- **High clump**: mass `≥ e^{-2C}/13` and ρ-decrement `≥ 21/10` on the high jump window
`[7s/4, 2s]` (`s = ⌊√x⌋`), for `x ≥ 25`. -/
lemma Pker_highclump {x : ℕ} (hx : 100 ≤ x) (hkmx : kernelMass x ≤ 2) (hkmx0 : 0 < kernelMass x) :
    (Real.exp (-C * 2) / 13
        ≤ ∑ a ∈ Finset.Icc (x - 2 * Nat.sqrt x) (x - 7 * Nat.sqrt x / 4), Pker x a)
      ∧ (∀ a ∈ Finset.Icc (x - 2 * Nat.sqrt x) (x - 7 * Nat.sqrt x / 4),
          (21 : ℝ) / 10 ≤ 3 * (Real.sqrt (x : ℝ) - Real.sqrt (a : ℝ))) := by
  have hx25 : 25 ≤ x := by omega
  set s := Nat.sqrt x with hs
  have hs5 : 5 ≤ s := by
    rw [hs]; calc 5 = Nat.sqrt 25 := by norm_num
      _ ≤ Nat.sqrt x := Nat.sqrt_le_sqrt hx25
  have hss : s * s ≤ x := by rw [hs]; have h := Nat.sqrt_le' x; rwa [pow_two] at h
  have hsx : 2 * s ≤ x := le_trans (by nlinarith [hs5]) hss
  have hxpos : (0 : ℝ) < (x : ℝ) := by positivity
  have hsqrtx : (0 : ℝ) < Real.sqrt (x : ℝ) := Real.sqrt_pos.mpr hxpos
  have hsfloor : (4 : ℝ) / 5 * Real.sqrt (x : ℝ) ≤ (s : ℝ) := sqrt_floor_lower hx25
  have hsq16 : (16 : ℝ) / 25 * (x : ℝ) ≤ (s : ℝ) ^ 2 := sq_floor_lower hx25
  -- tight floor bound `√x < s + 1` and `10 ≤ √x` (from `x ≥ 100`)
  have hsx1 : Real.sqrt (x : ℝ) < (s : ℝ) + 1 := by
    rw [Real.sqrt_lt' (by positivity), sq]
    exact_mod_cast Nat.lt_succ_sqrt x
  have hsqrt10 : (10 : ℝ) ≤ Real.sqrt (x : ℝ) := by
    rw [show (10 : ℝ) = Real.sqrt 100 by
      rw [show (100 : ℝ) = 10 ^ 2 by norm_num]; exact (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hx)
  -- bounds on window endpoints (Nat)
  have hab : 7 * s / 4 ≤ 2 * s := by omega
  have hsa : s ≤ 7 * s / 4 := by omega
  have hb2 : 2 * s ≤ 2 * s := le_refl _
  refine ⟨?_, ?_⟩
  · -- mass
    have hmass := Pker_subwindow_mass (x := x) (by omega) hkmx hkmx0 hsa hab hb2
    refine le_trans ?_ hmass
    have hexp : 0 < Real.exp (-C * 2) := Real.exp_pos _
    have hwidth : (s : ℝ) ≤ 4 * ((2 * s - 7 * s / 4 + 1 : ℕ) : ℝ) := by
      have : s ≤ 4 * (2 * s - 7 * s / 4 + 1) := by omega
      exact_mod_cast this
    have ha7 : (s : ℝ) ≤ ((7 * s / 4 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : s ≤ 7 * s / 4)
    have hWnn : (0 : ℝ) ≤ ((2 * s - 7 * s / 4 + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have ha7nn : (0 : ℝ) ≤ ((7 * s / 4 : ℕ) : ℝ) := Nat.cast_nonneg _
    -- key: 2x ≤ 13·W·(7s/4)
    have hprod : (s : ℝ) / 4 * (s : ℝ)
        ≤ ((2 * s - 7 * s / 4 + 1 : ℕ) : ℝ) * ((7 * s / 4 : ℕ) : ℝ) :=
      mul_le_mul (by linarith [hwidth]) ha7 (by positivity) hWnn
    have key : 2 * (x : ℝ) ≤ 13 * (((2 * s - 7 * s / 4 + 1 : ℕ) : ℝ) * ((7 * s / 4 : ℕ) : ℝ)) := by
      nlinarith [hprod, hsq16, hxpos]
    show Real.exp (-C * 2) / 13 ≤
      ((2 * s - 7 * s / 4 + 1 : ℕ) : ℝ) * (((7 * s / 4 : ℕ) : ℝ) * Real.exp (-C * 2) / (2 * (x : ℝ)))
    have hLHSeq : ((2 * s - 7 * s / 4 + 1 : ℕ) : ℝ)
        * (((7 * s / 4 : ℕ) : ℝ) * Real.exp (-C * 2) / (2 * (x : ℝ)))
        = ((2 * s - 7 * s / 4 + 1 : ℕ) : ℝ) * ((7 * s / 4 : ℕ) : ℝ) * Real.exp (-C * 2)
            / (2 * (x : ℝ)) := by ring
    rw [hLHSeq, le_div_iff₀ (mul_pos (by norm_num : (0:ℝ) < 2) hxpos),
        div_mul_eq_mul_div, div_le_iff₀ (by norm_num : (0:ℝ) < 13)]
    nlinarith [mul_le_mul_of_nonneg_left key hexp.le, hexp]
  · -- decrement ≥ 21/10
    intro a ha
    rw [Finset.mem_Icc] at ha
    have haxlt : a < x := by omega
    have hjump : 7 * s / 4 ≤ x - a := by omega
    have hjr : ((7 * s / 4 : ℕ) : ℝ) ≤ ((x - a : ℕ) : ℝ) := by exact_mod_cast hjump
    have hlow := sqrt_decrement_lower (x := x) (k := a) haxlt
    -- √x − √a ≥ (x−a)/(2√x); and 4(x−a) ≥ 7s−3 > 7√x−10 ≥ 2.8√x (since √x ≥ 10) ⟹ (x−a) ≥ 0.7·2√x
    have hbound : (7 : ℝ) / 10 ≤ Real.sqrt (x : ℝ) - Real.sqrt (a : ℝ) := by
      have hge : ((x - a : ℕ) : ℝ) / (2 * Real.sqrt (x : ℝ)) ≤ Real.sqrt (x : ℝ) - Real.sqrt (a : ℝ) :=
        hlow
      -- nat floor fact `7s ≤ 4(x−a) + 3`, cast to ℝ
      have hnat : 7 * s ≤ 4 * (x - a) + 3 := by omega
      have hnatR : 7 * (s : ℝ) ≤ 4 * ((x - a : ℕ) : ℝ) + 3 := by exact_mod_cast hnat
      have hnum : (7 : ℝ) / 10 * (2 * Real.sqrt (x : ℝ)) ≤ ((x - a : ℕ) : ℝ) := by
        nlinarith [hnatR, hsx1, hsqrt10]
      have h710 : (7 : ℝ) / 10 ≤ ((x - a : ℕ) : ℝ) / (2 * Real.sqrt (x : ℝ)) :=
        (le_div_iff₀ (by positivity)).mpr hnum
      linarith [h710, hge]
    linarith [hbound]

/-- Off the coalescence window, the conditioned pair kernel `KhatResPair` IS the product kernel, so
their local variances agree.  Bridges the abstract `product_locVar_ge` to the concrete `KhatRes`. -/
lemma khatResPair_locVar_eq_of_not_GoodW {α : Type*} [Fintype α] [DecidableEq α]
    (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ) (D : α × α → ℝ) {x y : α}
    (hxy : ¬ GoodW rnk W x y) :
    locVar (KhatResPair P rnk W) D (x, y)
      = locVar (fun p q : α × α => P p.1 q.1 * P p.2 q.2) D (x, y) := by
  unfold locVar
  refine Finset.sum_congr rfl (fun zw _ => ?_)
  rw [show KhatResPair P rnk W (x, y) zw = P x zw.1 * P y zw.2 from
    KhatRes_eq_prod_of_not_GoodW P rnk W hxy]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
