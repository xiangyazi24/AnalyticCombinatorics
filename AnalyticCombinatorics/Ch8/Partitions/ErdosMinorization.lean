import AnalyticCombinatorics.Ch8.Partitions.PartitionRenewal
import AnalyticCombinatorics.Ch8.Partitions.OverlapL1

/-!
# R7 Fact B via Doeblin: the comparable-rank minorization is ELEMENTARY (via σ(m) ≥ m)

The windowed Doeblin minorization `δ ≤ ∑_k min(Pker x k, Pker y k)` for comparable starts does NOT need
σ-averaging / a local-limit theorem.  The key is `σ(m) ≥ m` (since `m ∣ m`): on the jump window
`m ∈ [a√x, b√x]` this gives `σ(m) ≥ a√x`, so `∑ min(σ(jump_x), σ(jump_y))` over the `~(b−a)√x` common
landings is `Θ(x)`, and the smooth factor `(1/k)·exp(−C(√x−√k))/kernelMass x` is `Θ(1)/x` there, yielding
`δ > 0`.  Purely elementary.  Opus-authored (attack vector found after ChatGPT framed the block route).
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `σ(m) ≥ m` for `m ≥ 1` (since `m ∣ m`). -/
lemma sigmaR_ge_self {m : ℕ} (hm : 1 ≤ m) : (m : ℝ) ≤ Sigma.sigmaR m := by
  rw [Sigma.sigmaR_eq_sum_divisors]
  have hmem : m ∈ m.divisors := Nat.mem_divisors_self m (by omega)
  calc (m : ℝ) = ∑ d ∈ ({m} : Finset ℕ), (d : ℝ) := by simp
    _ ≤ ∑ d ∈ m.divisors, (d : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro a ha
          rw [Finset.mem_singleton] at ha; subst ha; exact hmem
        · intro d _ _; exact_mod_cast Nat.zero_le d

/-- `min(σ a, σ b) ≥ min(a, b)` for `a, b ≥ 1`. -/
lemma min_sigmaR_ge_min {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (min a b : ℝ) ≤ min (Sigma.sigmaR a) (Sigma.sigmaR b) := by
  rw [le_min_iff]
  refine ⟨le_trans ?_ (sigmaR_ge_self ha), ?_⟩
  · exact_mod_cast Nat.min_le_left a b
  · exact le_trans (by exact_mod_cast Nat.min_le_right a b) (sigmaR_ge_self hb)

/-- Per-entry lower bound on `Pker n k`: jump `n−k` with `σ(n−k) ≥ J` and `√n − √k ≤ T` gives
`Pker n k ≥ J·e^{−CT}/(2n)`. -/
lemma Pker_lower {n k : ℕ} {J T : ℝ} (hk1 : 1 ≤ k) (hkn : k < n)
    (hkm : kernelMass n ≤ 2) (hkm0 : 0 < kernelMass n) (hJ0 : 0 ≤ J)
    (hJ : J ≤ ((n - k : ℕ) : ℝ)) (hT : Real.sqrt (n : ℝ) - Real.sqrt (k : ℝ) ≤ T) :
    J * Real.exp (-C * T) / (2 * (n : ℝ)) ≤ Pker n k := by
  have hCpos := C_pos
  have hnk : n - (n - k) = k := Nat.sub_sub_self hkn.le
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le hk1 hkn.le)
  have hsig : J ≤ Sigma.sigmaR (n - k) := le_trans hJ (sigmaR_ge_self (by omega))
  have hexpr : Pker n k
      = Sigma.sigmaR (n - k) * Real.exp (-C * (Real.sqrt (n : ℝ) - Real.sqrt (k : ℝ)))
          / ((k : ℝ) * kernelMass n) := by
    unfold Pker
    rw [if_pos ⟨hk1, hkn⟩]
    unfold erdosWeight
    rw [hnk]
    ring
  rw [hexpr]
  have hexp_le : Real.exp (-C * T)
      ≤ Real.exp (-C * (Real.sqrt (n : ℝ) - Real.sqrt (k : ℝ))) :=
    Real.exp_le_exp.mpr (by nlinarith [hT, hCpos])
  have hnum : J * Real.exp (-C * T)
      ≤ Sigma.sigmaR (n - k) * Real.exp (-C * (Real.sqrt (n : ℝ) - Real.sqrt (k : ℝ))) :=
    mul_le_mul hsig hexp_le (Real.exp_pos _).le (le_trans hJ0 hsig)
  have hden : (k : ℝ) * kernelMass n ≤ 2 * (n : ℝ) := by
    have : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn.le
    nlinarith [this, hkm, hkm0, hn0]
  have hden0 : (0 : ℝ) < (k : ℝ) * kernelMass n := mul_pos hk0 hkm0
  rw [div_le_div_iff₀ (mul_pos two_pos hn0) hden0]
  exact mul_le_mul hnum hden hden0.le (mul_nonneg (sigmaR_nonneg _) (Real.exp_pos _).le)

/-- `√n − √k ≤ (n − k)/√n` for `1 ≤ k ≤ n`. -/
lemma sqrt_sub_le {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    Real.sqrt (n : ℝ) - Real.sqrt (k : ℝ) ≤ ((n : ℝ) - (k : ℝ)) / Real.sqrt (n : ℝ) := by
  have hn0 : (0 : ℝ) < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast lt_of_lt_of_le hk1 hkn)
  rw [le_div_iff₀ hn0]
  have hsn : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hsk : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt (by positivity)
  have hkle : Real.sqrt (k : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hkn)
  nlinarith [hsn, hsk, hkle, Real.sqrt_nonneg (k : ℝ), Real.sqrt_nonneg (n : ℝ)]

set_option maxHeartbeats 2000000 in
/-- **Windowed Doeblin minorization** (the comparable-rank overlap is bounded below).  For `x ≤ y` with
`y ≤ x + D√x` and `x` large, the kernels overlap on the standard jump window by `≥ e^{−C(2+D)}/8`. -/
theorem Pker_window_minor {D : ℝ} (hD0 : 0 ≤ D) {x y : ℕ}
    (hx16 : 16 ≤ x) (hxD2 : (D : ℝ) ^ 2 ≤ (x : ℝ)) (hxy : x ≤ y)
    (hyD : (y : ℝ) ≤ (x : ℝ) + D * Real.sqrt (x : ℝ))
    (hkmx : kernelMass x ≤ 2) (hkmx0 : 0 < kernelMass x)
    (hkmy : kernelMass y ≤ 2) (hkmy0 : 0 < kernelMass y) :
    Real.exp (-C * (2 + D)) / 8
      ≤ ∑ k ∈ Finset.Icc (x - 2 * Nat.sqrt x) (x - Nat.sqrt x), min (Pker x k) (Pker y k) := by
  classical
  have hCpos := C_pos
  set s := Nat.sqrt x with hs
  have hxpos : (0 : ℝ) < (x : ℝ) := by positivity
  have hsqrtx : (0 : ℝ) < Real.sqrt (x : ℝ) := Real.sqrt_pos.mpr hxpos
  have hs4 : 4 ≤ s := by
    rw [hs]; calc 4 = Nat.sqrt 16 := by norm_num
      _ ≤ Nat.sqrt x := Nat.sqrt_le_sqrt hx16
  have hs1 : 1 ≤ s := by omega
  have hssx : s * s ≤ x := by rw [hs, ← pow_two]; exact Nat.sqrt_le' x
  have h2sx : 2 * s ≤ x := by nlinarith [hssx, hs4]
  have hsx2 : (s : ℝ) * (s : ℝ) ≤ (x : ℝ) := by exact_mod_cast hssx
  have hsxlt : (x : ℝ) < ((s : ℝ) + 1) * ((s : ℝ) + 1) := by
    have hnat : x < (s + 1) * (s + 1) := by rw [hs]; exact Nat.lt_succ_sqrt x
    exact_mod_cast hnat
  have hsle_sqrt : (s : ℝ) ≤ Real.sqrt (x : ℝ) := by
    rw [show (s : ℝ) = Real.sqrt ((s : ℝ) * (s : ℝ)) from (Real.sqrt_mul_self (by positivity)).symm]
    exact Real.sqrt_le_sqrt hsx2
  have hDsx : D ≤ Real.sqrt (x : ℝ) := by
    rw [show D = Real.sqrt ((D : ℝ) ^ 2) from (Real.sqrt_sq hD0).symm]
    exact Real.sqrt_le_sqrt hxD2
  have hx2s1 : 2 * s + 1 ≤ x := by nlinarith [hssx, hs4]
  -- per-term lower bound  L  on the window
  set L : ℝ := (s : ℝ) * Real.exp (-C * (2 + D)) / (4 * (x : ℝ)) with hL
  have hperterm : ∀ k ∈ Finset.Icc (x - 2 * s) (x - s), L ≤ min (Pker x k) (Pker y k) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    obtain ⟨hk1', hk2'⟩ := hk
    -- window arithmetic
    have hjump_lo : s ≤ x - k := by omega
    have hk_lt_x : k < x := by omega
    have hk_ge1 : 1 ≤ k := by omega
    have hk_lt_y : k < y := lt_of_lt_of_le hk_lt_x hxy
    have hjump_hi : x - k ≤ 2 * s := by omega
    -- real casts
    have hxk_cast : ((x - k : ℕ) : ℝ) = (x : ℝ) - (k : ℝ) := by
      rw [Nat.cast_sub hk_lt_x.le]
    have hyk_cast : ((y - k : ℕ) : ℝ) = (y : ℝ) - (k : ℝ) := by
      rw [Nat.cast_sub hk_lt_y.le]
    -- √x − √k ≤ 2
    have hTx : Real.sqrt (x : ℝ) - Real.sqrt (k : ℝ) ≤ 2 := by
      refine le_trans (sqrt_sub_le hk_ge1 hk_lt_x.le) ?_
      rw [div_le_iff₀ hsqrtx]
      have : ((x : ℝ) - (k : ℝ)) ≤ 2 * (s : ℝ) := by
        rw [← hxk_cast]; exact_mod_cast hjump_hi
      nlinarith [this, hsle_sqrt, hsqrtx]
    -- √y − √k ≤ 2 + D
    have hsqrty : (0 : ℝ) < Real.sqrt (y : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast lt_of_lt_of_le (by omega : 0 < x) hxy)
    have hsqrtxy : Real.sqrt (x : ℝ) ≤ Real.sqrt (y : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hxy)
    have hTy : Real.sqrt (y : ℝ) - Real.sqrt (k : ℝ) ≤ 2 + D := by
      refine le_trans (sqrt_sub_le hk_ge1 hk_lt_y.le) ?_
      rw [div_le_iff₀ hsqrty]
      have hykle : (y : ℝ) - (k : ℝ) ≤ 2 * (s : ℝ) + D * Real.sqrt (x : ℝ) := by
        have h1 : (y : ℝ) - (x : ℝ) ≤ D * Real.sqrt (x : ℝ) := by linarith [hyD]
        have h2 : (x : ℝ) - (k : ℝ) ≤ 2 * (s : ℝ) := by rw [← hxk_cast]; exact_mod_cast hjump_hi
        linarith
      nlinarith [hykle, hsle_sqrt, hsqrtxy, hsqrtx, hsqrty, Real.sqrt_nonneg (x:ℝ), hD0]
    -- jump lower bounds for σ
    have hJx : (s : ℝ) ≤ ((x - k : ℕ) : ℝ) := by exact_mod_cast hjump_lo
    have hJy : (s : ℝ) ≤ ((y - k : ℕ) : ℝ) := by
      have : s ≤ y - k := by omega
      exact_mod_cast this
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := by positivity
    -- Pker x k ≥ s·e^{−2C}/(2x)
    have hPx := Pker_lower (n := x) (k := k) (J := (s : ℝ)) (T := 2)
      hk_ge1 hk_lt_x hkmx hkmx0 hs0 hJx hTx
    have hPy := Pker_lower (n := y) (k := k) (J := (s : ℝ)) (T := 2 + D)
      hk_ge1 hk_lt_y hkmy hkmy0 hs0 hJy hTy
    -- L ≤ Pker x k  and  L ≤ Pker y k
    have hy2x : (y : ℝ) ≤ 2 * (x : ℝ) := by
      nlinarith [hyD, hDsx, Real.mul_self_sqrt hxpos.le, hsqrtx, Real.sqrt_nonneg (x : ℝ)]
    have h2x0 : (0 : ℝ) < 2 * (x : ℝ) := by linarith [hxpos]
    have h4x0 : (0 : ℝ) < 4 * (x : ℝ) := by linarith [hxpos]
    have hypos : (0 : ℝ) < (y : ℝ) := lt_of_lt_of_le hxpos (by exact_mod_cast hxy)
    have h2y0 : (0 : ℝ) < 2 * (y : ℝ) := by linarith [hypos]
    have hexp_nn : (0 : ℝ) ≤ Real.exp (-C * 2) := (Real.exp_pos _).le
    have hexpD_nn : (0 : ℝ) ≤ Real.exp (-C * (2 + D)) := (Real.exp_pos _).le
    have he : Real.exp (-C * (2 + D)) ≤ Real.exp (-C * 2) :=
      Real.exp_le_exp.mpr (by nlinarith [hCpos, hD0])
    have hLx : L ≤ (s : ℝ) * Real.exp (-C * 2) / (2 * (x : ℝ)) := by
      rw [hL, div_le_div_iff₀ h4x0 h2x0]
      have hkey : (s : ℝ) * Real.exp (-C * (2 + D)) * (2 * (x : ℝ))
          ≤ (s : ℝ) * Real.exp (-C * 2) * (2 * (x : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hs0) h2x0.le
      nlinarith [hkey, mul_nonneg (mul_nonneg hs0 hexp_nn) hxpos.le]
    have hLy : L ≤ (s : ℝ) * Real.exp (-C * (2 + D)) / (2 * (y : ℝ)) := by
      rw [hL, div_le_div_iff₀ h4x0 h2y0]
      nlinarith [hy2x, mul_nonneg hs0 hexpD_nn]
    exact le_min (le_trans hLx hPx) (le_trans hLy hPy)
  -- sum ≥ card • L ≥ δ
  have hcard := Finset.card_nsmul_le_sum (Finset.Icc (x - 2 * s) (x - s))
    (fun k => min (Pker x k) (Pker y k)) L hperterm
  refine le_trans ?_ hcard
  rw [Nat.card_Icc, nsmul_eq_mul]
  have hcardval : (x - s) + 1 - (x - 2 * s) = s + 1 := by omega
  rw [hcardval, hL]
  have hs4r : (4 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs4
  have hs2 : (x : ℝ) ≤ 2 * ((s : ℝ) * (s : ℝ)) := by
    nlinarith [hsxlt, hs4r, sq_nonneg ((s : ℝ) - 4)]
  have he0 : (0 : ℝ) < Real.exp (-C * (2 + D)) := Real.exp_pos _
  have hrw : ((s : ℝ) + 1) * ((s : ℝ) * Real.exp (-C * (2 + D)) / (4 * (x : ℝ)))
      = ((s : ℝ) + 1) * (s : ℝ) * Real.exp (-C * (2 + D)) / (4 * (x : ℝ)) := by ring
  push_cast
  rw [hrw, div_le_div_iff₀ (by norm_num) (mul_pos (by norm_num : (0 : ℝ) < 4) hxpos)]
  have hsnn : (0 : ℝ) ≤ (s : ℝ) := by positivity
  have hfac : (0 : ℝ) ≤ 8 * (((s : ℝ) + 1) * (s : ℝ)) - 4 * (x : ℝ) := by nlinarith [hs2, hsnn]
  nlinarith [mul_nonneg he0.le hfac]
