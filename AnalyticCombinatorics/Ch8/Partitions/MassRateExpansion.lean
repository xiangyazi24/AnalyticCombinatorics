import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateMoments

/-!
# Mass-rate campaign: second-order kernel expansions (R8 §3.2–3.3)

Second-order expansions of the square-root drop and the reciprocal, with explicit
error constants:

* `sqrt_drop_second_order` — `|（√n−√(n−m)) − (m/(2s) + m²/(8s³))| ≤ m³/s⁵` for `m ≤ n`,
  via the purely algebraic identity `8s³E = (s−q)³(q+3s)` (`s=√n`, `q=√(n−m)`,
  `linear_combination` on `q² = s²−m`) — no calculus, no smallness hypothesis;
* `inv_sub_second_order` — `|1/(n−m) − (1/n + m/n²)| = m²/(n²(n−m)) ≤ 2m²/n³` for `2m ≤ n`.

Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/--
**Square-root drop, second order**: for `m ≤ n`, `1 ≤ n`,

  `|（√n − √(n−m)) − (m/(2√n) + m²/(8√n³))| ≤ m³/√n⁵`.
-/
lemma sqrt_drop_second_order {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n) :
    |(Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))
        - ((m : ℝ) / (2 * Real.sqrt (n : ℝ))
          + (m : ℝ) ^ 2 / (8 * Real.sqrt (n : ℝ) ^ 3))|
      ≤ (m : ℝ) ^ 3 / Real.sqrt (n : ℝ) ^ 5 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set s : ℝ := Real.sqrt (n : ℝ) with hsdef
  set q : ℝ := Real.sqrt ((n - m : ℕ) : ℝ) with hqdef
  have hs : 0 < s := Real.sqrt_pos.mpr hnpos
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
    push_cast [Nat.cast_sub hm]
    ring
  have hq2 : q ^ 2 = s ^ 2 - (m : ℝ) := by
    rw [hqdef, Real.sq_sqrt (Nat.cast_nonneg _), hcast, hs2]
  have hqs : q ≤ s := by
    have h1 : q ^ 2 ≤ s ^ 2 := by
      rw [hq2]
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    nlinarith [hq0, hs.le]
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  -- the key polynomial identity: 8s⁴ − 8s³q − 4s²m − m² = (s−q)³(q+3s)
  have hkey : 8 * s ^ 4 - 8 * s ^ 3 * q - 4 * s ^ 2 * (m : ℝ) - (m : ℝ) ^ 2
      = (s - q) ^ 3 * (q + 3 * s) := by
    linear_combination (q ^ 2 - 5 * s ^ 2 - (m : ℝ)) * hq2
  -- the expression E in closed form
  have hE_eq : (s - q) - ((m : ℝ) / (2 * s) + (m : ℝ) ^ 2 / (8 * s ^ 3))
      = (s - q) ^ 3 * (q + 3 * s) / (8 * s ^ 3) := by
    rw [← hkey]
    field_simp
    ring
  -- nonnegativity and the bound
  have hsq_nonneg : 0 ≤ s - q := by linarith
  have hE_nonneg : 0 ≤ (s - q) ^ 3 * (q + 3 * s) / (8 * s ^ 3) := by
    have h1 : 0 ≤ (s - q) ^ 3 := by positivity
    have h2 : 0 ≤ q + 3 * s := by linarith
    positivity
  rw [hE_eq, abs_of_nonneg hE_nonneg]
  -- (s−q)(s+q) = m so s−q ≤ m/s; q+3s ≤ 4s
  have hprod : (s - q) * (s + q) = (m : ℝ) := by
    have : (s - q) * (s + q) = s ^ 2 - q ^ 2 := by ring
    rw [this, hq2]
    ring
  have hsq_le : s - q ≤ (m : ℝ) / s := by
    rw [le_div_iff₀ hs]
    calc (s - q) * s ≤ (s - q) * (s + q) :=
          mul_le_mul_of_nonneg_left (by linarith) hsq_nonneg
      _ = (m : ℝ) := hprod
  have hq3s : q + 3 * s ≤ 4 * s := by linarith
  calc (s - q) ^ 3 * (q + 3 * s) / (8 * s ^ 3)
      ≤ ((m : ℝ) / s) ^ 3 * (4 * s) / (8 * s ^ 3) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul _ hq3s (by linarith) (by positivity)
        exact pow_le_pow_left₀ hsq_nonneg hsq_le 3
    _ = (m : ℝ) ^ 3 / (2 * s ^ 5) := by
        field_simp
        ring
    _ ≤ (m : ℝ) ^ 3 / s ^ 5 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith [pow_pos hs 5]

/-- The sqrt-drop second-order remainder is nonnegative (same identity, factors `≥ 0`). -/
lemma sqrt_drop_second_order_nonneg {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n) :
    0 ≤ (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))
        - ((m : ℝ) / (2 * Real.sqrt (n : ℝ))
          + (m : ℝ) ^ 2 / (8 * Real.sqrt (n : ℝ) ^ 3)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set s : ℝ := Real.sqrt (n : ℝ) with hsdef
  set q : ℝ := Real.sqrt ((n - m : ℕ) : ℝ) with hqdef
  have hs : 0 < s := Real.sqrt_pos.mpr hnpos
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
    push_cast [Nat.cast_sub hm]
    ring
  have hq2 : q ^ 2 = s ^ 2 - (m : ℝ) := by
    rw [hqdef, Real.sq_sqrt (Nat.cast_nonneg _), hcast, hs2]
  have hqs : q ≤ s := by
    have h1 : q ^ 2 ≤ s ^ 2 := by
      rw [hq2]
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    nlinarith [hq0, hs.le]
  have hkey : 8 * s ^ 4 - 8 * s ^ 3 * q - 4 * s ^ 2 * (m : ℝ) - (m : ℝ) ^ 2
      = (s - q) ^ 3 * (q + 3 * s) := by
    linear_combination (q ^ 2 - 5 * s ^ 2 - (m : ℝ)) * hq2
  have hE_eq : (s - q) - ((m : ℝ) / (2 * s) + (m : ℝ) ^ 2 / (8 * s ^ 3))
      = (s - q) ^ 3 * (q + 3 * s) / (8 * s ^ 3) := by
    rw [← hkey]
    field_simp
    ring
  rw [hE_eq]
  have h1 : 0 ≤ (s - q) ^ 3 := by
    have : 0 ≤ s - q := by linarith
    positivity
  have h2 : 0 ≤ q + 3 * s := by linarith
  positivity

/--
**Reciprocal, second order**: for `2m ≤ n`, `1 ≤ n`,

  `|1/(n−m) − (1/n + m/n²)| ≤ 2m²/n³`  (exactly `m²/(n²(n−m))`).
-/
lemma inv_sub_second_order {n m : ℕ} (hn : 1 ≤ n) (h2m : 2 * m ≤ n) :
    |1 / (((n - m : ℕ) : ℝ)) - (1 / (n : ℝ) + (m : ℝ) / (n : ℝ) ^ 2)|
      ≤ 2 * (m : ℝ) ^ 2 / (n : ℝ) ^ 3 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hm_le : m ≤ n := by omega
  have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
    push_cast [Nat.cast_sub hm_le]
    ring
  have h2mR : 2 * (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2m
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hnm_half : (n : ℝ) / 2 ≤ ((n - m : ℕ) : ℝ) := by
    rw [hcast]
    linarith
  have hnm_pos : (0 : ℝ) < ((n - m : ℕ) : ℝ) := by linarith
  -- exact identity
  have hexact : 1 / (((n - m : ℕ) : ℝ)) - (1 / (n : ℝ) + (m : ℝ) / (n : ℝ) ^ 2)
      = (m : ℝ) ^ 2 / ((n : ℝ) ^ 2 * ((n - m : ℕ) : ℝ)) := by
    have hne2 : (n : ℝ) - (m : ℝ) ≠ 0 := by
      rw [← hcast]
      exact hnm_pos.ne'
    rw [hcast]
    field_simp
    ring
  rw [hexact, abs_of_nonneg (by positivity)]
  -- m²/(n²(n−m)) ≤ m²/(n²·n/2) = 2m²/n³
  calc (m : ℝ) ^ 2 / ((n : ℝ) ^ 2 * ((n - m : ℕ) : ℝ))
      ≤ (m : ℝ) ^ 2 / ((n : ℝ) ^ 2 * ((n : ℝ) / 2)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        apply mul_le_mul_of_nonneg_left hnm_half (by positivity)
    _ = 2 * (m : ℝ) ^ 2 / (n : ℝ) ^ 3 := by
        field_simp

/--
**Exponential drop, second order** (R8 §3.4): for `m ≤ n` with `4C·m² ≤ √n³`,

  `|e^{−C·drop} − e^{−(C/2)m/√n}·(1 − C·m²/(8√n³))|
      ≤ (C² + 2C)·e^{−(C/2)m/√n}·(m³/√n⁵ + m⁴/√n⁶)`.
-/
lemma exp_sqrt_drop_second_order {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n)
    (hsmall : 4 * C * (m : ℝ) ^ 2 ≤ Real.sqrt (n : ℝ) ^ 3) :
    |Real.exp (-C * (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ)))
        - Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ)) *
            (1 - C * (m : ℝ) ^ 2 / (8 * Real.sqrt (n : ℝ) ^ 3))|
      ≤ (C ^ 2 + 2 * C) *
          Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ)) *
          ((m : ℝ) ^ 3 / Real.sqrt (n : ℝ) ^ 5 + (m : ℝ) ^ 4 / Real.sqrt (n : ℝ) ^ 6) := by
  have hC := C_pos
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set s : ℝ := Real.sqrt (n : ℝ) with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr hnpos
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hmn : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm
  -- the remainder E and its bounds
  set E : ℝ := (s - Real.sqrt ((n - m : ℕ) : ℝ))
      - ((m : ℝ) / (2 * s) + (m : ℝ) ^ 2 / (8 * s ^ 3)) with hEdef
  have hE0 : 0 ≤ E := sqrt_drop_second_order_nonneg hn hm
  have hEle : E ≤ (m : ℝ) ^ 3 / s ^ 5 := by
    have := sqrt_drop_second_order hn hm
    rw [← hsdef, ← hEdef] at this
    calc E ≤ |E| := le_abs_self E
      _ ≤ (m : ℝ) ^ 3 / s ^ 5 := this
  -- m²/s³ ≤ 1/(4C), m/s² ≤ 1, m³/s⁵ ≤ 1/(4C)
  have hm2s3 : (m : ℝ) ^ 2 / s ^ 3 ≤ 1 / (4 * C) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hsmall]
  have hms2 : (m : ℝ) / s ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    rw [hs2]
    exact hmn
  have hm3s5 : (m : ℝ) ^ 3 / s ^ 5 ≤ 1 / (4 * C) := by
    have heq : (m : ℝ) ^ 3 / s ^ 5 = ((m : ℝ) ^ 2 / s ^ 3) * ((m : ℝ) / s ^ 2) := by
      field_simp
    rw [heq]
    calc ((m : ℝ) ^ 2 / s ^ 3) * ((m : ℝ) / s ^ 2)
        ≤ (1 / (4 * C)) * 1 := by
          apply mul_le_mul hm2s3 hms2 (by positivity) (by positivity)
      _ = 1 / (4 * C) := mul_one _
  -- δ := C(m²/(8s³) + E) ∈ [0, 9/32]
  set δ : ℝ := C * ((m : ℝ) ^ 2 / (8 * s ^ 3) + E) with hδdef
  have hδ0 : 0 ≤ δ := by
    rw [hδdef]
    have h1 : 0 ≤ (m : ℝ) ^ 2 / (8 * s ^ 3) := by positivity
    nlinarith [hE0, hC]
  have hδ_le : δ ≤ 9 / 32 := by
    rw [hδdef]
    have h1 : (m : ℝ) ^ 2 / (8 * s ^ 3) ≤ 1 / (32 * C) := by
      have heq : (m : ℝ) ^ 2 / (8 * s ^ 3) = ((m : ℝ) ^ 2 / s ^ 3) / 8 := by ring
      rw [heq]
      calc ((m : ℝ) ^ 2 / s ^ 3) / 8 ≤ (1 / (4 * C)) / 8 := by linarith [hm2s3]
        _ = 1 / (32 * C) := by ring
    have h2 : E ≤ 1 / (4 * C) := le_trans hEle hm3s5
    have h3 : (m : ℝ) ^ 2 / (8 * s ^ 3) + E ≤ 1 / (32 * C) + 1 / (4 * C) := by linarith
    calc C * ((m : ℝ) ^ 2 / (8 * s ^ 3) + E)
        ≤ C * (1 / (32 * C) + 1 / (4 * C)) :=
          mul_le_mul_of_nonneg_left h3 hC.le
      _ = 9 / 32 := by field_simp; ring
  have hδ1 : |(-δ : ℝ)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg hδ0]
    linarith
  -- exponential split: e^{−C·drop} = e^{−(C/2)m/s}·e^{−δ}
  have hsplit : Real.exp (-C * (s - Real.sqrt ((n - m : ℕ) : ℝ)))
      = Real.exp (-(C / 2) * (m : ℝ) / s) * Real.exp (-δ) := by
    rw [← Real.exp_add]
    congr 1
    rw [hδdef, hEdef]
    field_simp
    ring
  -- |e^{−δ} − 1 + δ| ≤ δ²
  have hquad : |Real.exp (-δ) - 1 - (-δ)| ≤ (-δ) ^ 2 :=
    Real.abs_exp_sub_one_sub_id_le hδ1
  -- assemble the difference
  have hbody : Real.exp (-C * (s - Real.sqrt ((n - m : ℕ) : ℝ)))
      - Real.exp (-(C / 2) * (m : ℝ) / s) * (1 - C * (m : ℝ) ^ 2 / (8 * s ^ 3))
      = Real.exp (-(C / 2) * (m : ℝ) / s) *
          ((Real.exp (-δ) - 1 + δ) - C * E) := by
    rw [hsplit, hδdef]
    ring
  rw [hbody, abs_mul, abs_of_pos (Real.exp_pos _)]
  -- bound the bracket: ≤ δ² + C·E ≤ (C²+2C)(m³/s⁵ + m⁴/s⁶)
  have hbracket : |(Real.exp (-δ) - 1 + δ) - C * E| ≤ δ ^ 2 + C * E := by
    have h1 : |Real.exp (-δ) - 1 + δ| ≤ δ ^ 2 := by
      have : Real.exp (-δ) - 1 + δ = Real.exp (-δ) - 1 - (-δ) := by ring
      rw [this]
      calc |Real.exp (-δ) - 1 - (-δ)| ≤ (-δ) ^ 2 := hquad
        _ = δ ^ 2 := by ring
    have h2 : |C * E| = C * E := abs_of_nonneg (by positivity)
    calc |(Real.exp (-δ) - 1 + δ) - C * E|
        ≤ |Real.exp (-δ) - 1 + δ| + |C * E| := abs_sub _ _
      _ ≤ δ ^ 2 + C * E := by rw [h2]; linarith
  -- δ² ≤ C²m⁴/(32s⁶) + C·m³/(2s⁵) via (a+b)² ≤ 2a²+2b² and m⁶/s¹⁰ ≤ m³/(4C·s⁵)
  have hδsq : δ ^ 2 ≤ C ^ 2 * (m : ℝ) ^ 4 / (32 * s ^ 6) + C * (m : ℝ) ^ 3 / (2 * s ^ 5) := by
    have hab : δ ^ 2 ≤ 2 * (C * ((m : ℝ) ^ 2 / (8 * s ^ 3))) ^ 2 + 2 * (C * E) ^ 2 := by
      rw [hδdef]
      nlinarith [sq_nonneg (C * ((m : ℝ) ^ 2 / (8 * s ^ 3)) - C * E)]
    have h1 : 2 * (C * ((m : ℝ) ^ 2 / (8 * s ^ 3))) ^ 2 = C ^ 2 * (m : ℝ) ^ 4 / (32 * s ^ 6) := by
      field_simp
      ring
    have h2 : 2 * (C * E) ^ 2 ≤ C * (m : ℝ) ^ 3 / (2 * s ^ 5) := by
      have hCE : C * E ≤ C * ((m : ℝ) ^ 3 / s ^ 5) := mul_le_mul_of_nonneg_left hEle hC.le
      have hCE2 : C * ((m : ℝ) ^ 3 / s ^ 5) ≤ C * (1 / (4 * C)) :=
        mul_le_mul_of_nonneg_left hm3s5 hC.le
      have hquarter : C * (1 / (4 * C)) = 1 / 4 := by field_simp
      have hCE0 : 0 ≤ C * E := by positivity
      calc 2 * (C * E) ^ 2 = 2 * (C * E) * (C * E) := by ring
        _ ≤ 2 * (1 / 4) * (C * ((m : ℝ) ^ 3 / s ^ 5)) := by
            apply mul_le_mul _ hCE hCE0 (by positivity)
            rw [← hquarter] at *
            nlinarith [hCE, hCE2, hCE0]
        _ = C * (m : ℝ) ^ 3 / (2 * s ^ 5) := by field_simp; ring
    linarith
  -- final assembly
  calc Real.exp (-(C / 2) * (m : ℝ) / s) * |(Real.exp (-δ) - 1 + δ) - C * E|
      ≤ Real.exp (-(C / 2) * (m : ℝ) / s) * (δ ^ 2 + C * E) :=
        mul_le_mul_of_nonneg_left hbracket (Real.exp_pos _).le
    _ ≤ Real.exp (-(C / 2) * (m : ℝ) / s) *
          ((C ^ 2 + 2 * C) * ((m : ℝ) ^ 3 / s ^ 5 + (m : ℝ) ^ 4 / s ^ 6)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        have hCE_le : C * E ≤ C * ((m : ℝ) ^ 3 / s ^ 5) :=
          mul_le_mul_of_nonneg_left hEle hC.le
        have h2 : C ^ 2 * (m : ℝ) ^ 4 / (32 * s ^ 6) ≤ C ^ 2 * ((m : ℝ) ^ 4 / s ^ 6) := by
          rw [show C ^ 2 * (m : ℝ) ^ 4 / (32 * s ^ 6)
              = (C ^ 2 * (m : ℝ) ^ 4) / (32 * s ^ 6) by ring,
            show C ^ 2 * ((m : ℝ) ^ 4 / s ^ 6) = (C ^ 2 * (m : ℝ) ^ 4) / s ^ 6 by ring]
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          nlinarith [pow_pos hs 6]
        have h3 : C * (m : ℝ) ^ 3 / (2 * s ^ 5) ≤ C * ((m : ℝ) ^ 3 / s ^ 5) := by
          rw [show C * (m : ℝ) ^ 3 / (2 * s ^ 5) = (C * (m : ℝ) ^ 3) / (2 * s ^ 5) by ring,
            show C * ((m : ℝ) ^ 3 / s ^ 5) = (C * (m : ℝ) ^ 3) / s ^ 5 by ring]
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          nlinarith [pow_pos hs 5]
        have hpos1 : 0 ≤ C ^ 2 * ((m : ℝ) ^ 3 / s ^ 5) := by positivity
        have hpos2 : 0 ≤ 2 * C * ((m : ℝ) ^ 4 / s ^ 6) := by positivity
        have hfinal : δ ^ 2 + C * E
            ≤ C ^ 2 * ((m : ℝ) ^ 4 / s ^ 6) + 2 * C * ((m : ℝ) ^ 3 / s ^ 5) := by
          linarith [hδsq, hCE_le, h2, h3]
        have hexpand : (C ^ 2 + 2 * C) * ((m : ℝ) ^ 3 / s ^ 5 + (m : ℝ) ^ 4 / s ^ 6)
            = C ^ 2 * ((m : ℝ) ^ 4 / s ^ 6) + 2 * C * ((m : ℝ) ^ 3 / s ^ 5)
              + (C ^ 2 * ((m : ℝ) ^ 3 / s ^ 5) + 2 * C * ((m : ℝ) ^ 4 / s ^ 6)) := by
          ring
        linarith [hfinal, hpos1, hpos2, le_of_eq hexpand]
    _ = (C ^ 2 + 2 * C) *
          Real.exp (-(C / 2) * (m : ℝ) / s) *
          ((m : ℝ) ^ 3 / s ^ 5 + (m : ℝ) ^ 4 / s ^ 6) := by ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
