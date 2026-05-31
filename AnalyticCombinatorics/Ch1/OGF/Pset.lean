import AnalyticCombinatorics.Ch1.OGF.Defs
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Data.Fintype.Powerset

/-!
# Ch1 §I.2 — The powerset construction PSET(C)

Flajolet & Sedgewick, Part A, Chapter I, §I.2. `PSET(C)` forms finite *sets* of
C-objects (each object used at most once, `C₀=∅`). Grouping a set by object size, a
size-`n` object is a partition `p` of `n` together with, for each size `m`, a
*subset* of card `(mult m)` of the `Cₘ` objects of that size. The number of size-`k`
subsets of a `c`-set is `choose(c,k)`, so

  `PSET(C)ₙ = ∑_{p:Partition n} ∏_m choose(Cₘ, mult_m p)
            = genFun (fun m j => choose(Cₘ, j)) |>.coeff n`,

and the OGF is `PSET(C)(z) = ∏_{m≥1} (1 + z^m)^{Cₘ}` (since `∑_k choose(c,k) x^k =
(1+x)^c`). The construction mirrors `MSET` with subsets/`choose` in place of
multisets/`multichoose`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The powerset construction `PSET(C)` (F&S §I.2): a partition `p` of `n` together
with, for each size `m`, a card-`(p.parts.count m)` subset of the size-`m` objects of
`C`. Faithful when `C₀=∅`. -/
noncomputable def CombClass.pset (C : CombClass) : CombClass where
  Obj n := Σ p : Nat.Partition n,
    ∀ m : Fin (n + 1), { s : Finset (C.Obj m.val) // s.card = p.parts.count m.val }
  finObj _ := by classical infer_instance

/-- The counting identity for `PSET(C)`: `PSET(C)ₙ = ∑_{p:Partition n} ∏_m
choose(Cₘ, mult_m p)`, from `card_sigma`/`card_pi`/`card_finset_len`. -/
lemma CombClass.counts_pset (C : CombClass) (n : ℕ) :
    C.pset.counts n
      = ∑ p : Nat.Partition n, ∏ m : Fin (n + 1),
          (C.counts m.val).choose (p.parts.count m.val) := by
  classical
  change Fintype.card
      (Σ p : Nat.Partition n,
        ∀ m : Fin (n + 1), { s : Finset (C.Obj m.val) // s.card = p.parts.count m.val }) = _
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Fintype.card_pi]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [Fintype.card_finset_len]
  rfl

/-- The `PSET(C)` OGF is Mathlib's `genFun` of the binomial family. -/
theorem CombClass.ogf_pset_eq_genFun (C : CombClass) :
    C.pset.ogf
      = Nat.Partition.genFun (R := ℚ) (fun m j => ((C.counts m).choose j : ℚ)) := by
  ext n
  rw [CombClass.coeff_ogf, CombClass.counts_pset, Nat.Partition.coeff_genFun, Nat.cast_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hsub : (p.parts.toFinsupp).support ⊆ Finset.range (n + 1) := by
    intro m hm
    rw [Multiset.toFinsupp_support, Multiset.mem_toFinset] at hm
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.Partition.le_of_mem_parts hm))
  rw [Nat.cast_prod,
    Finsupp.prod_of_support_subset (p.parts.toFinsupp) hsub
      (fun m j => ((C.counts m).choose j : ℚ))
      (fun m _ => by simp),
    Fin.prod_univ_eq_prod_range
      (fun m => ((C.counts m).choose (p.parts.count m) : ℚ)) (n + 1)]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [Multiset.toFinsupp_apply]

section EulerProduct

open scoped PowerSeries.WithPiTopology
open PowerSeries.WithPiTopology

local instance instTopRatPset : TopologicalSpace ℚ := ⊥
local instance instDiscRatPset : DiscreteTopology ℚ := ⟨rfl⟩

/-- **The powerset construction as an infinite product** (F&S Theorem I.1): for a
class `C` with `C₀=∅`, `PSET(C)(z) = ∏_{i} (∑_{k} choose(Cᵢ₊₁, k) z^{(i+1)k})`,
i.e. `∏_{m≥1} (1 + z^m)^{Cₘ}`. -/
theorem CombClass.ogf_pset (C : CombClass) :
    C.pset.ogf
      = ∏' i, ∑' k, ((C.counts (i + 1)).choose k : ℚ) • (X : ℚ⟦X⟧) ^ ((i + 1) * k) := by
  rw [CombClass.ogf_pset_eq_genFun, Nat.Partition.genFun_eq_tprod]
  refine tprod_congr fun i => ?_
  have hshift : Summable
      (fun j => ((C.counts (i + 1)).choose (j + 1) : ℚ) • (X : ℚ⟦X⟧) ^ ((i + 1) * (j + 1))) :=
    Nat.Partition.summable_genFun_term (fun m j => ((C.counts m).choose j : ℚ)) i
  have hsumm : Summable
      (fun k => ((C.counts (i + 1)).choose k : ℚ) • (X : ℚ⟦X⟧) ^ ((i + 1) * k)) :=
    (summable_nat_add_iff 1).mp hshift
  rw [hsumm.tsum_eq_zero_add]
  simp

end EulerProduct

end AnalyticCombinatorics.Ch1
