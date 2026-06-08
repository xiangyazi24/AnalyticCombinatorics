import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentTwo

/-!
# The order-4 Bose kernel `boseKernel4 = ∑_d d⁴ e^{−dz}`

Closed form via Eulerian numbers `⟨4,k⟩ = 1, 11, 11, 1`:

  `boseKernel4 z = e^{−z}(1 + 11e^{−z} + 11e^{−2z} + e^{−3z}) / (1 − e^{−z})⁵ ~ 24/z⁵`.

`boseKernel3` has derivative `−boseKernel4` on `(0,∞)` (the differentiation step that yields the
`M₃` Lambert identity from the `M₂` one).  Opus-authored.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `Σ_d d⁴ e^{−dz}` in closed form (Eulerian numbers `1,11,11,1`). -/
noncomputable def boseKernel4 (z : ℝ) : ℝ :=
  Real.exp (-z) * (1 + 11 * Real.exp (-z) + 11 * Real.exp (-z) ^ 2 + Real.exp (-z) ^ 3)
    / (1 - Real.exp (-z)) ^ 5

/-- `boseKernel3` has derivative `−boseKernel4` on `(0,∞)` (quotient rule). -/
lemma boseKernel3_hasDerivAt {z : ℝ} (hz : 0 < z) :
    HasDerivAt boseKernel3 (-boseKernel4 z) z := by
  have hy1 : Real.exp (-z) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  have hd0 : (0 : ℝ) < 1 - Real.exp (-z) := by linarith
  have hy : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-z)) z := by
    have hinner : HasDerivAt (fun u : ℝ => -u) (-1 : ℝ) z := by
      simpa using (hasDerivAt_id z).neg
    simpa using (Real.hasDerivAt_exp (-z)).comp z hinner
  -- numerator  N(u) = e^{−u}·(1 + 4 e^{−u} + (e^{−u})²)  (matching boseKernel3's parenthesization)
  have hone := ((hy.const_mul (4 : ℝ)).const_add (1 : ℝ)).add (hy.pow 2)
  have hN := hy.mul hone
  -- denominator  D(u) = (1 − e^{−u})⁴
  have hbase : HasDerivAt (fun u : ℝ => 1 - Real.exp (-u)) (Real.exp (-z)) z := by
    simpa using hy.const_sub 1
  have hD := hbase.pow 4
  have hQ := hN.div hD (pow_ne_zero 4 hd0.ne')
  have hshape : boseKernel3
      = fun u : ℝ => Real.exp (-u) * (1 + 4 * Real.exp (-u) + Real.exp (-u) ^ 2)
          / (1 - Real.exp (-u)) ^ 4 := rfl
  rw [hshape]
  convert hQ using 1
  simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply, Pi.div_apply]
  rw [boseKernel4]
  field_simp
  ring

/-- `boseKernel4 ≥ 0` on `(0,∞)`. -/
lemma boseKernel4_nonneg {z : ℝ} (hz : 0 < z) : 0 ≤ boseKernel4 z := by
  have h1 : Real.exp (-z) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have h2 : 0 < 1 - Real.exp (-z) := by linarith
  rw [boseKernel4]
  positivity

end AnalyticCombinatorics.Ch8.Partitions.Erdos
