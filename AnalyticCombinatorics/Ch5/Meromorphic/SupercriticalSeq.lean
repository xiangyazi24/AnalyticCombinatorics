import Mathlib
import AnalyticCombinatorics.Ch5.Meromorphic.Transfer

open Filter Asymptotics
open scoped ENNReal NNReal PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics
namespace Ch5
namespace Meromorphic

/-- The principal-part scalar for `1/(1-C)` at a simple dominant zero:
`c = 1 / C'(rho)` and `c / rho = 1 / (rho * C'(rho))`. -/
theorem supercriticalSeq_principalPartScalar
    (ρ Cderiv : ℂ) :
    Cderiv⁻¹ * ρ⁻¹ = 1 / (ρ * Cderiv) := by
  rw [one_div, mul_inv_rev]

/-- Coefficient normalization for the supercritical-sequence principal part. -/
theorem supercriticalSeq_mainTerm_eq
    {ρ Cderiv : ℂ} (n : ℕ) :
    Cderiv⁻¹ * ρ⁻¹ ^ (n + 1) =
      (1 / (ρ * Cderiv)) * ρ⁻¹ ^ n := by
  calc
    Cderiv⁻¹ * ρ⁻¹ ^ (n + 1) =
        (Cderiv⁻¹ * ρ⁻¹) * ρ⁻¹ ^ n := by
      rw [pow_succ]
      ring
    _ = (1 / (ρ * Cderiv)) * ρ⁻¹ ^ n := by
      rw [supercriticalSeq_principalPartScalar]

/-- Supercritical-sequence dominant-pole transfer, in the SEQ-form constant `c = 1/C'(ρ)`.

Honest scope: this is the dominant simple-pole transfer (`dominant_simplePole_isEquivalent`)
specialized to the principal-part constant `c = 1/Cderiv` that arises for `F = 1/(1 - C)` at a simple
dominant zero of `1 - C` (where `Cderiv = C'(ρ)`); see `supercriticalSeq_principalPartScalar`. It takes
the principal-part-plus-analytic-remainder DECOMPOSITION (`hfg`, `hgR`) as input — exactly as the
meromorphic transfer does. The genuine F&S V.2 step of DERIVING that decomposition from the supercritical
data (`F·(1-C)=1`, `C(ρ)=1`, `C'(ρ)≠0`, next singularity past `R`) is NOT proved here and is flagged as
future work; the prior decorative `C`-hypotheses were removed to keep the statement faithful to what is
proved. Consistency checks (constant matches the proved surjections `c=1/2` and alignments `c=1/e`
instances) are recorded in `RUN_LOG`/`AUDIT_STATUS`. -/
theorem supercriticalSeq_isEquivalent
    (F g : PowerSeries ℂ) {ρ Cderiv : ℂ} {R : ℝ}
    (hρ : 0 < ‖ρ‖) (hρR : ‖ρ‖ < R)
    (hCderiv_ne : Cderiv ≠ 0)
    (hgR : ENNReal.ofReal R < (PowerSeries.toFMLS g).radius)
    (hfg :
      F =
        PowerSeries.C (Cderiv⁻¹ * ρ⁻¹) *
          PowerSeries.rescale ρ⁻¹ (PowerSeries.invUnitsSub (1 : ℂˣ)) + g) :
    (fun n : ℕ => PowerSeries.coeff (R := ℂ) n F) ~[atTop]
      (fun n : ℕ => (1 / (ρ * Cderiv)) * ρ⁻¹ ^ n) := by
  have hmain :
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n F) ~[atTop]
        (fun n : ℕ => Cderiv⁻¹ * ρ⁻¹ ^ (n + 1)) :=
    dominant_simplePole_isEquivalent
      F g (ρ := ρ) (c := Cderiv⁻¹) (R := R)
      hρ hρR (inv_ne_zero hCderiv_ne) hgR hfg
  exact hmain.trans_eventuallyEq
    (Eventually.of_forall fun n => supercriticalSeq_mainTerm_eq (ρ := ρ) (Cderiv := Cderiv) n)

end Meromorphic
end Ch5
end AnalyticCombinatorics
