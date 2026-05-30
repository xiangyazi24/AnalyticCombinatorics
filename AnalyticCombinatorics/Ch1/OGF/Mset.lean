import AnalyticCombinatorics.Ch1.OGF.Defs
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Data.Sym.Card

/-!
# Ch1 §I.2 — The multiset construction MSET(C): counts layer

Flajolet & Sedgewick, Part A, Chapter I, §I.2. `MSET(C)` forms finite multisets of
C-objects (`C₀=∅`). Grouping a multiset by object size, a size-`n` object is a
partition `p` of `n` (recording the multiplicities of each size) together with, for
each size `m`, a size-`(mult m)` multiset of the `Cₘ` objects of that size (a `Sym`).

This file builds the graded `Fintype` model and the counting identity, and connects
it to Mathlib's `Nat.Partition.genFun`:

  `MSET(C)ₙ = ∑_{p:Partition n} ∏_m multichoose(Cₘ, mult_m p)
            = genFun (fun m j => multichoose(Cₘ, j)) |>.coeff n`.

The Euler product OGF `∏_m (1 - z^m)^{-Cₘ}` is proved in the OGF layer. (For `C = ℙ`,
`multichoose 1 k = 1`, recovering the partition flagship.)
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The multiset construction `MSET(C)` (F&S §I.2), modelled by grouping a multiset
of C-objects by size: a partition `p` of `n` together with, for each size `m`, a
size-`(p.parts.count m)` multiset (`Sym`) of the size-`m` objects of `C`. Faithful
when `C₀=∅`. -/
noncomputable def CombClass.mset (C : CombClass) : CombClass where
  Obj n := Σ p : Nat.Partition n, ∀ m : Fin (n + 1), Sym (C.Obj m.val) (p.parts.count m.val)
  finObj _ := by classical infer_instance

/-- The counting identity for `MSET(C)`: `MSET(C)ₙ = ∑_{p:Partition n} ∏_m
multichoose(Cₘ, mult_m p)`, from `card_sigma`/`card_pi`/`card_sym_eq_multichoose`. -/
lemma CombClass.counts_mset (C : CombClass) (n : ℕ) :
    C.mset.counts n
      = ∑ p : Nat.Partition n, ∏ m : Fin (n + 1),
          (C.counts m.val).multichoose (p.parts.count m.val) := by
  classical
  change Fintype.card
      (Σ p : Nat.Partition n, ∀ m : Fin (n + 1), Sym (C.Obj m.val) (p.parts.count m.val)) = _
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Fintype.card_pi]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [Sym.card_sym_eq_multichoose]
  rfl

/-- The `MSET(C)` OGF is Mathlib's `genFun` of the multichoose family. -/
theorem CombClass.ogf_mset_eq_genFun (C : CombClass) :
    C.mset.ogf
      = Nat.Partition.genFun (R := ℚ) (fun m j => ((C.counts m).multichoose j : ℚ)) := by
  ext n
  rw [CombClass.coeff_ogf, CombClass.counts_mset, Nat.Partition.coeff_genFun, Nat.cast_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hsub : (p.parts.toFinsupp).support ⊆ Finset.range (n + 1) := by
    intro m hm
    rw [Multiset.toFinsupp_support, Multiset.mem_toFinset] at hm
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.Partition.le_of_mem_parts hm))
  rw [Nat.cast_prod,
    Finsupp.prod_of_support_subset (p.parts.toFinsupp) hsub
      (fun m j => ((C.counts m).multichoose j : ℚ))
      (fun m _ => by simp),
    Fin.prod_univ_eq_prod_range
      (fun m => ((C.counts m).multichoose (p.parts.count m) : ℚ)) (n + 1)]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [Multiset.toFinsupp_apply]

end AnalyticCombinatorics.Ch1
