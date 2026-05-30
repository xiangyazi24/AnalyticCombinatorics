import AnalyticCombinatorics.Ch1.OGF.Defs
import Mathlib.Combinatorics.Enumerative.Partition.GenFun

/-!
# Ch1 §I.3 — Integer partitions and Euler's product (MSET flagship)

Flajolet & Sedgewick, Part A, Chapter I, §I.3. An integer partition of `n` is a
multiset of positive integers summing to `n` — i.e. an object of `MSET(ℙ)` of size
`n`. Its generating function is Euler's product

  `P(z) = ∏_{m≥1} 1/(1 - z^m) = ∏_{m≥1} ∑_{j≥0} z^{m j}`.

We model the partition class with Mathlib's `Nat.Partition` (a `Fintype`), connect
its OGF to Mathlib's `Nat.Partition.genFun`, and push it to the explicit infinite
product. The literal Euler product is an explicit TODO in Mathlib's `GenFun`, so
this is genuinely new content; it is anchored on `#(Nat.Partition n)`. The infinite
product/sums use the X-adic (coefficientwise) topology on `ℚ⟦X⟧`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The class of integer partitions (F&S §I.3): an object of size `n` is a
partition of `n` (a multiset of positive integers summing to `n`). This is
Mathlib's `Nat.Partition n`. -/
def CombClass.partitions : CombClass where
  Obj n := Nat.Partition n
  finObj _ := inferInstance

@[simp] lemma CombClass.counts_partitions (n : ℕ) :
    CombClass.partitions.counts n = Fintype.card (Nat.Partition n) := rfl

/-- The partition OGF is Mathlib's `genFun` of the constant family `1` (both are
`∑ₙ #(Partition n) zⁿ`). -/
theorem CombClass.ogf_partitions_eq_genFun :
    CombClass.partitions.ogf = Nat.Partition.genFun (R := ℚ) (fun _ _ => 1) := by
  ext n
  rw [CombClass.coeff_ogf, CombClass.counts_partitions, Nat.Partition.coeff_genFun]
  simp [Finsupp.prod]

section EulerProduct

open scoped PowerSeries.WithPiTopology
open PowerSeries.WithPiTopology

local instance instTopRatPartitions : TopologicalSpace ℚ := ⊥
local instance instDiscRatPartitions : DiscreteTopology ℚ := ⟨rfl⟩

/-- **The partition generating function as an infinite product** (F&S §I.3,
Euler): `P(z) = ∏_{i} (∑_{j} z^{(i+1) j})`, i.e. `∏_{m≥1} 1/(1 - z^m)`. -/
theorem CombClass.ogf_partitions :
    CombClass.partitions.ogf
      = ∏' i, ∑' j, (X : ℚ⟦X⟧) ^ ((i + 1) * j) := by
  rw [CombClass.ogf_partitions_eq_genFun, Nat.Partition.genFun_eq_tprod]
  refine tprod_congr fun i => ?_
  have hcc : constantCoeff (R := ℚ) (X ^ (i + 1)) = 0 := by
    rw [map_pow, PowerSeries.constantCoeff_X, zero_pow (Nat.succ_ne_zero i)]
  have hsumm : Summable fun j => (X : ℚ⟦X⟧) ^ ((i + 1) * j) := by
    simpa [pow_mul] using summable_pow_of_constantCoeff_eq_zero hcc
  rw [hsumm.tsum_eq_zero_add]
  simp [one_smul]

end EulerProduct

end AnalyticCombinatorics.Ch1
