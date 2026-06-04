# SET ODE hard step: verdict and Lean plan

## 1. Finpartition API verdict

Use `Finpartition.avoid` plus `Finpartition.extend`.  There is no grepped ready-made
`erase/remove part` operation and no existing equivalence
`Finpartition s ≃ Σ B, Finpartition (s \ B)`.

Verified useful names:

* block containing a label: `Finpartition.part`
* membership/control: `Finpartition.part_mem`, `Finpartition.mem_part_self`,
  alias `P.mem_part`, `Finpartition.part_eq_iff_mem`,
  `Finpartition.part_eq_of_mem`, `Finpartition.eq_of_mem_parts`,
  `Finpartition.ne_empty`, `Finpartition.subset`
* constructors/maps: `Finpartition.map`, `Finpartition.parts_map`,
  `Finpartition.restrict`, `Finpartition.sum_restrict`,
  `Finpartition.extend`, `Finpartition.card_extend`,
  `Finpartition.avoid`, `Finpartition.mem_avoid`
* other useful API: `Finpartition.ofExistsUnique`, `Finpartition.equivSigmaParts`,
  `Finpartition.sum_card_parts`

For

```lean
P : Finpartition (Finset.univ : Finset (Fin (n+1)))
B := P.part (Fin.last n)
```

we get

```lean
hBmem : B ∈ P.parts := by simpa [B] using P.part_mem.2 (by simp)
hlast : Fin.last n ∈ B := by simpa [B] using P.mem_part (by simp)
P.avoid B : Finpartition ((Finset.univ : Finset (Fin (n+1))) \ B)
```

## 2. Recommended strategy

Do not first build the full decorated object equivalence.  Prove the recurrence
from the `counts_set` weighted sum:

```lean
noncomputable def setWeight (C : CombClass) {α : Type*}
    [DecidableEq α] (s : Finset α) : ℕ :=
  ∑ P : Finpartition s, ∏ B : P.parts, C.counts B.val.card
```

Main reusable relabel lemma:

```lean
lemma setWeight_card {α : Type*} [Fintype α] [DecidableEq α]
    (R : Finset α) :
    setWeight C R = C.set.counts R.card
```

For relabeling, `Finpartition.map` needs an order isomorphism on `Finset` lattices.
Build it from a label equivalence:

```lean
noncomputable def finsetOrderIsoOfEquiv (e : α ≃ β) :
    Finset α ≃o Finset β :=
  e.finsetCongr.toOrderIso
    (by intro s t h; simpa [Equiv.finsetCongr_apply]
      using (Finset.map_subset_map.mpr h :
        s.map e.toEmbedding ⊆ t.map e.toEmbedding))
    (by intro s t h; simpa [Equiv.finsetCongr_apply, Equiv.finsetCongr_symm]
      using (Finset.map_subset_map.mpr h :
        s.map e.symm.toEmbedding ⊆ t.map e.symm.toEmbedding))
```

Verified relabel names: `Equiv.finsetCongr`, `Equiv.toOrderIso`,
`Finset.map_subset_map`, `Finset.map_univ_equiv`, `Fintype.sum_equiv`,
`Equiv.sum_comp`, `Finset.equivFinOfCardEq`, `Fintype.equivFinOfCardEq`,
`Fintype.card_coe`.  `Finset.orderIsoOfFin` is available, but still needs this
wrapper before `Finpartition.map`.

Now prove the fixed-block fiber:

```lean
{P : Finpartition univ // P.part (Fin.last n) = B}
  ≃ Finpartition (univ \ B)
```

with `toFun P := P.val.avoid B` and
`invFun Q := Q.extend hBne Finset.disjoint_sdiff hc`, where
`hc` is from `Finset.sdiff_union_self_eq_union` and `B ⊆ univ`.
For products use `Finset.prod_coe_sort`, `Finset.prod_insert`,
`Finset.sdiff_eq_self_of_disjoint`, and `Finpartition.mem_avoid`.

Split the total partition sum by the block map using:

* `Equiv.sigmaFiberEquiv`
* `Fintype.sum_equiv`
* `Fintype.sum_sigma`

Count blocks containing `Fin.last n` by the equivalence

```lean
S ↦ insert (Fin.last n) (S.map Fin.castSuccEmb)
```

from `i`-subsets of `Fin n` to `(i+1)`-blocks containing the last label.  Verified
names: `Fin.castSuccEmb`, `Fin.castSucc_ne_last`, `Fin.eq_castSucc_of_ne_last`,
`Fin.castPred`, `Fin.castPred_castSucc`, `Fin.castSucc_castPred`,
`Finset.mem_powersetCard`, `Finset.card_powersetCard`,
`Finset.powersetCard_succ_insert`, `Finset.card_insert_of_notMem`,
`Finset.card_map`.

Target recurrence:

```lean
lemma counts_set_succ (C : CombClass) (n : ℕ) :
    C.set.counts (n+1)
      = ∑ i : Fin (n+1),
          n.choose (i : ℕ) * C.counts ((i : ℕ) + 1) *
            C.set.counts (n - (i : ℕ))
```

Collapse constant sums over `i`-subsets with `Finset.sum_eq_card_nsmul` and
`Finset.card_powersetCard`.

## 3. Hardest sub-step

Hardest proof is the inverse law for the fixed-block equivalence.  Key local lemma:

```lean
A ∈ (P.avoid B).parts ↔ A ∈ P.parts ∧ A ≠ B
```

when `B ∈ P.parts`.  Prove it from `Finpartition.mem_avoid`; for `A ≠ B`, use
`P.disjoint`, `Finset.sdiff_eq_self_of_disjoint`; for the impossible case
`A ≤ B`, use `P.ne_empty` plus disjointness.

Then `extend (avoid P B) B = P` follows by `ext A` and membership in
`insert B (P.avoid B).parts`.  The other direction is easier by
`simp [Finpartition.mem_avoid, Finpartition.extend]`.

## 4. Simpler route check

Differentiating the `counts_set` sum directly does not avoid pointing; it just
rephrases the same distinguished-block split.

`SET(C) = 1 + C ⋆ SET(C)` is false: it chooses a distinguished block and
overcounts by the number of blocks.  The correct rooted identity is

```text
(SET(C))' = C' ⋆ SET(C)
```

It is worth adding `CombClass.deriv` and using existing `CombClass.egf_lprod` as
the final wrapper, but the core proof remains the fixed-last-label decomposition.
