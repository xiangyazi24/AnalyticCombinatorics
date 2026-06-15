import AnalyticCombinatorics.Ch8.Partitions.CeilingEscapeClose
import AnalyticCombinatorics.Ch8.Partitions.ErdosRiemannError

/-!
# The complete Hardy–Ramanujan partition limit (with the exact constant)

`Erdos.erdos_partition_limit_exists` (CeilingEscapeClose) proves the normalized partition sequence
`u n = n · p(n) · exp(−C√n)` (`C = π√(2/3)`) converges to *some* positive limit.
`erdos_limit_constant_of_renewal` (ErdosRiemannError) forces that limit to equal `1/(4√3)`,
unconditionally (the mesh-1 Riemann error is negligible, `riemannError_negligible`).

This file assembles the two into the full Hardy–Ramanujan statement
`u n → 1/(4√3)`, the leading-order partition asymptotic `p(n) ~ exp(π√(2n/3)) / (4n√3)`.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions

/-- **The complete Hardy–Ramanujan partition limit.**  The normalized partition sequence
`u n = n · p(n) · exp(−C√n)` (`C = π√(2/3)`) converges to the exact constant `1/(4√3)` — equivalently
`p(n) ~ exp(π√(2n/3)) / (4 n √3)`.  Combines the unconditional positive-limit theorem
`erdos_partition_limit_exists` with the renewal constant identification `erdos_limit_constant_of_renewal`. -/
theorem erdos_partition_limit_constant :
    Tendsto Erdos.u atTop (𝓝 (1 / (4 * Real.sqrt 3))) := by
  obtain ⟨a, ha, hlim⟩ := Erdos.erdos_partition_limit_exists
  rwa [erdos_limit_constant_of_renewal ha hlim] at hlim

end AnalyticCombinatorics.Ch8.Partitions
