import AnalyticCombinatorics.Ch8.Partitions.RankDropMinor

/-!
# TASK T2-ceiling, L5-escape core: the per-drop GEOMETRIC minorant

The banked `Pker_rankDrop_minorization` only minorizes drops `1` and `2`
(`rankDropKer v 1, v 2 ≥ η`).  The escape super-solution (L5) needs a **geometric lower bound on the
rank-drop tail at every threshold** `g`:

  `∑_{d > g} rankDropKer v d ≥ c · e^{−γ' g}`  (eventually in `v`),

so that the conditional overshoot ratio `tail(g + A R)/tail(g)` is uniformly `≤ e R → 0`.  It suffices
to minorize each *single* drop `d` geometrically: `rankDropKer v d ≥ η_d` with `η_d ≳ d e^{−C d/3}`.

This file banks the reusable **integral lower bound**
`modelIntegral C a b ≥ (b − a) · (π²/6) · a · e^{−(C/2) b}` for `0 ≤ a < b` — the geometric-rate
ingredient (`e^{−(C/2) b}` with `b ≈ (2/3) d` ⟹ `e^{−C d/3}`) for the eventual per-drop minorant.

The full per-drop window minorant `rankDropKer v d ≥ η_d` (for each `d`, via a phase cover of `[0,1)`
by four windows whose `t`-bands scale with `d`, applied through `rankDropKer_ge_const_of_tband`) still
requires making that lemma's eventual-in-`v` threshold EXPLICIT in `(a,b,d)`, so that for a fixed
large `v` all drops `d ≲ √v` are simultaneously minorized (needed for the tail lower bound
`tail(g) ≥ c e^{−γ' g}` at a single `v`).

NEW file; imports the banked minorization/window bricks, does not modify them.  Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open AnalyticCombinatorics.Ch8.Partitions.Erdos.Model

/-- **Integral lower bound.**  For `0 ≤ a < b`, the Erdős density integral over `[a,b]` is at least
`(b − a) · (π²/6) · a · e^{−(C/2) b}`: the integrand `(π²/6) y e^{−(C/2) y}` is
`≥ (π²/6) a e^{−(C/2) b}` on `[a,b]` (minorize `y ≥ a` and `e^{−(C/2) y} ≥ e^{−(C/2) b}`). -/
lemma modelIntegral_ge {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    (b - a) * ((Real.pi ^ 2 / 6) * a * Real.exp (-(C / 2) * b)) ≤ Model.modelIntegral C a b := by
  have hC := C_pos
  rw [Model.modelIntegral]
  -- ∫_a^b const ≤ ∫_a^b integrand
  have hconst_eq : (b - a) * ((Real.pi ^ 2 / 6) * a * Real.exp (-(C / 2) * b))
      = ∫ _y in a..b, (Real.pi ^ 2 / 6) * a * Real.exp (-(C / 2) * b) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  rw [hconst_eq]
  apply intervalIntegral.integral_mono_on hab.le
  · exact intervalIntegrable_const
  · -- integrability of the true integrand
    have hc : Continuous fun y : ℝ => (Real.pi ^ 2 / 6) * y * Real.exp (-(C / 2) * y) := by
      have h1 : Continuous fun y : ℝ => (Real.pi ^ 2 / 6) * y :=
        continuous_const.mul continuous_id
      have h2 : Continuous fun y : ℝ => Real.exp (-(C / 2) * y) :=
        Real.continuous_exp.comp (continuous_const.mul continuous_id)
      exact h1.mul h2
    exact hc.intervalIntegrable _ _
  · intro y hy
    have hya : a ≤ y := hy.1
    have hyb : y ≤ b := hy.2
    have hy0 : (0 : ℝ) ≤ y := le_trans ha hya
    have hπ : (0 : ℝ) ≤ Real.pi ^ 2 / 6 := by positivity
    -- (π²/6) a e^{−(C/2)b} ≤ (π²/6) y e^{−(C/2)y}
    have hexp : Real.exp (-(C / 2) * b) ≤ Real.exp (-(C / 2) * y) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hyb, hC]
    have hey : (0 : ℝ) ≤ Real.exp (-(C / 2) * y) := (Real.exp_pos _).le
    have heb : (0 : ℝ) ≤ Real.exp (-(C / 2) * b) := (Real.exp_pos _).le
    calc (Real.pi ^ 2 / 6) * a * Real.exp (-(C / 2) * b)
        ≤ (Real.pi ^ 2 / 6) * y * Real.exp (-(C / 2) * b) := by
          apply mul_le_mul_of_nonneg_right _ heb
          exact mul_le_mul_of_nonneg_left hya hπ
      _ ≤ (Real.pi ^ 2 / 6) * y * Real.exp (-(C / 2) * y) := by
          apply mul_le_mul_of_nonneg_left hexp
          positivity

#print axioms modelIntegral_ge

end AnalyticCombinatorics.Ch8.Partitions.Erdos
