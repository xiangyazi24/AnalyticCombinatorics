import AnalyticCombinatorics.Ch1.OGF.Defs
import Mathlib.Combinatorics.Enumerative.Composition

/-!
# Ch1 §I.2 / §I.3 — The sequence construction and integer compositions

Flajolet & Sedgewick, Part A, Chapter I. The sequence construction `SEQ(C)` forms
all finite sequences `(γ₁, …, γₘ)` of `C`-objects, with size the sum of the
component sizes. For this to give a (finite) combinatorial class one needs `C` to
have no object of size `0` (F&S's standing side-condition); the positive
component sizes of a size-`n` sequence then form a *composition* of `n`, so we
model `SEQ(C)` over Mathlib's `Composition n`.

This file proves, at the level of counting sequences, the genuine combinatorial
content:

* `counts_seq` — `(SEQ C)ₙ = ∑_{compositions c of n} ∏ᵢ C_{cᵢ}`.
* `counts_seq_posInt` — **integer compositions are sequences of positive
  integers** (F&S §I.3): `(SEQ ℙ)ₙ = #(Composition n) = 2^{n-1}`.

The closed-form generating function of compositions lives in `Compositions.lean`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

/-- The sequence construction `SEQ(C)` (F&S §I.2): a size-`n` object is a
composition `c` of `n` together with a choice of a `C`-object for each (positive)
part. Faithful to `SEQ(C)` exactly when `C` has no size-`0` object. -/
def CombClass.seq (C : CombClass) : CombClass where
  Obj n := Σ c : Composition n, ∀ i : Fin c.length, C.Obj (c.blocksFun i)
  finObj _ := inferInstance

/-- Counting sequence of `SEQ(C)`: `(SEQ C)ₙ = ∑_{compositions c of n} ∏ᵢ C_{cᵢ}`.
The genuine combinatorial content, from `Fintype.card_sigma` and
`Fintype.card_pi`. -/
lemma CombClass.counts_seq (C : CombClass) (n : ℕ) :
    C.seq.counts n
      = ∑ c : Composition n, ∏ i : Fin c.length, C.counts (c.blocksFun i) := by
  change Fintype.card (Σ c : Composition n, ∀ i : Fin c.length, C.Obj (c.blocksFun i)) = _
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Fintype.card_pi]
  rfl

/-- The class `ℙ` of positive integers: one object of each size `n ≥ 1`
(F&S §I.3, the parts of a composition). -/
def CombClass.posInt : CombClass where
  Obj n := Fin (if 0 < n then 1 else 0)
  finObj _ := inferInstance

@[simp] lemma CombClass.counts_posInt (n : ℕ) :
    CombClass.posInt.counts n = if 0 < n then 1 else 0 :=
  Fintype.card_fin _

/-- The class of integer compositions (F&S §I.3): a size-`n` object is a
composition of `n`. This is Mathlib's `Composition n`. -/
def CombClass.compositions : CombClass where
  Obj n := Composition n
  finObj _ := inferInstance

@[simp] lemma CombClass.counts_compositions (n : ℕ) :
    CombClass.compositions.counts n = 2 ^ (n - 1) :=
  composition_card n

/-- **Compositions are sequences of positive integers** (F&S §I.3): the counting
sequences of `SEQ(ℙ)` and of the composition class agree, both equal to
`#(Composition n) = 2^{n-1}`. Each part of a composition is `≥ 1`, so every
factor `ℙ_{cᵢ} = 1`, and the product collapses to a count of compositions. -/
theorem CombClass.counts_seq_posInt (n : ℕ) :
    CombClass.posInt.seq.counts n = 2 ^ (n - 1) := by
  rw [CombClass.counts_seq]
  have h : ∀ c : Composition n,
      ∏ i : Fin c.length, CombClass.posInt.counts (c.blocksFun i) = 1 := by
    intro c
    refine Finset.prod_eq_one fun i _ => ?_
    rw [CombClass.counts_posInt, if_pos (show 0 < c.blocksFun i from c.one_le_blocksFun i)]
  simp only [h, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  rw [composition_card]

/-- `SEQ(ℙ)` and the composition class are literally the same counting sequence. -/
theorem CombClass.counts_seq_posInt_eq_compositions (n : ℕ) :
    CombClass.posInt.seq.counts n = CombClass.compositions.counts n := by
  rw [CombClass.counts_seq_posInt, CombClass.counts_compositions]

end AnalyticCombinatorics.Ch1
