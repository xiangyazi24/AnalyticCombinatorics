import AnalyticCombinatorics.Ch1.OGF.Sequence
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-!
# Ch1 §I.2 — The sequence construction: `SEQ(C)(z) = 1/(1 - C(z))`

Flajolet & Sedgewick, Part A, Chapter I, §I.2, the sequence construction, for a
general class `C` with no object of size `0` (`C.counts 0 = 0`). A sequence
decomposes as `SEQ(C) = ε + C × SEQ(C)` (empty, or first component × rest), so the
counting sequence satisfies a convolution recursion and the OGF satisfies the
functional equation `S(z) = 1 + C(z)·S(z)`, hence

  **`(seq C).ogf · (1 - C.ogf) = 1`**, i.e. `SEQ(C)(z) = 1/(1 - C(z))`.

The combinatorial core is the first-part decomposition of compositions, built from
Mathlib's `Composition.append`/`single`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

variable {C : CombClass}

/-- Assemble a composition of `n+1` from a first part of size `k+1` and a
composition of the remaining `n - k`. -/
private def consSeq (n : ℕ) (k : Fin (n + 1)) (c : Composition (n - (k : ℕ))) :
    Composition (n + 1) :=
  (Composition.append (Composition.single ((k : ℕ) + 1) (Nat.succ_pos _)) c).cast
    (by have := k.is_le; omega)

private lemma consSeq_blocks (n : ℕ) (k : Fin (n + 1)) (c : Composition (n - (k : ℕ))) :
    (consSeq n k c).blocks = ((k : ℕ) + 1) :: c.blocks := by
  simp [consSeq, Composition.single_blocks]

private lemma prod_consSeq (n : ℕ) (k : Fin (n + 1)) (c : Composition (n - (k : ℕ))) :
    ((consSeq n k c).blocks.map C.counts).prod
      = C.counts ((k : ℕ) + 1) * (c.blocks.map C.counts).prod := by
  rw [consSeq_blocks, List.map_cons, List.prod_cons]

/-- `counts_seq` rewritten as a sum of products over the blocks list. -/
private lemma counts_seq_eq_listProd (m : ℕ) :
    C.seq.counts m = ∑ c : Composition m, (c.blocks.map C.counts).prod := by
  rw [C.counts_seq]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Composition.ofFn_blocksFun c, List.map_ofFn, List.prod_ofFn]
  simp only [Function.comp_apply]

private lemma consSeq_bijective (n : ℕ) :
    Function.Bijective
      (fun p : Σ k : Fin (n + 1), Composition (n - (k : ℕ)) => consSeq n p.1 p.2) := by
  constructor
  · rintro ⟨k, cp⟩ ⟨k', cq⟩ hpq
    simp only at hpq
    have hb : ((k : ℕ) + 1) :: cp.blocks = ((k' : ℕ) + 1) :: cq.blocks := by
      rw [← consSeq_blocks, ← consSeq_blocks, hpq]
    rw [List.cons.injEq] at hb
    obtain ⟨hk, hblocks⟩ := hb
    have hkk : k = k' := Fin.ext (by omega)
    subst hkk
    have : cp = cq := Composition.ext hblocks
    subst this
    rfl
  · intro c
    have hne : c.blocks ≠ [] := by rw [Ne, Composition.blocks_eq_nil]; omega
    obtain ⟨b, rest, hbr⟩ := List.exists_cons_of_ne_nil hne
    have hb1 : 1 ≤ b := c.one_le_blocks (by rw [hbr]; exact List.mem_cons_self ..)
    have hsum : b + rest.sum = n + 1 := by
      have hs := c.blocks_sum; rw [hbr, List.sum_cons] at hs; omega
    refine ⟨⟨⟨b - 1, by omega⟩, ⟨rest, ?_, ?_⟩⟩, ?_⟩
    · intro i hi
      exact c.blocks_pos (by rw [hbr]; exact List.mem_cons_of_mem _ hi)
    · change rest.sum = n - (b - 1); omega
    · apply Composition.ext
      rw [consSeq_blocks]
      change (b - 1 + 1) :: rest = c.blocks
      rw [Nat.sub_add_cancel hb1]
      exact hbr.symm

/-- The convolution recursion: a nonempty sequence is a first component (size
`k+1`) followed by a sequence of the remaining size. -/
lemma counts_seq_succ (n : ℕ) :
    C.seq.counts (n + 1)
      = ∑ k : Fin (n + 1), C.counts ((k : ℕ) + 1) * C.seq.counts (n - (k : ℕ)) := by
  rw [counts_seq_eq_listProd,
    ← Fintype.sum_bijective _ (consSeq_bijective n)
        (fun p => ((consSeq n p.1 p.2).blocks.map C.counts).prod)
        (fun c => (c.blocks.map C.counts).prod) (fun _ => rfl),
    Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp_rw [prod_consSeq]
  rw [← Finset.mul_sum, ← counts_seq_eq_listProd]

lemma counts_seq_zero : C.seq.counts 0 = 1 := by
  rw [counts_seq_eq_listProd]
  have h : ∀ c : Composition 0, (c.blocks.map C.counts).prod = 1 := by
    intro c
    have hnil : c.blocks = [] := by simp
    simp [hnil]
  simp [h, Finset.card_univ, composition_card]

private lemma constantCoeff_ogf (hC0 : C.counts 0 = 0) :
    constantCoeff (R := ℚ) C.ogf = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, CombClass.coeff_ogf, hC0, Nat.cast_zero]

/-- **The sequence functional equation** (F&S §I.2): `S(z) = 1 + C(z)·S(z)` for a
class `C` with `C₀ = ∅`. -/
theorem CombClass.ogf_seq_functional_eq (hC0 : C.counts 0 = 0) :
    C.seq.ogf = 1 + C.ogf * C.seq.ogf := by
  ext m
  rcases m with _ | n
  · rw [CombClass.coeff_ogf, counts_seq_zero]
    simp [coeff_zero_eq_constantCoeff, constantCoeff_ogf hC0]
  · rw [CombClass.coeff_ogf, counts_seq_succ, map_add, coeff_one,
      if_neg (Nat.succ_ne_zero n), zero_add, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ']
    push_cast
    rw [CombClass.coeff_ogf, hC0,
      Fin.sum_univ_eq_sum_range
        (fun k => (C.counts (k + 1) : ℚ) * (C.seq.counts (n - k) : ℚ)) (n + 1)]
    simp [CombClass.coeff_ogf]

/-- **The sequence construction** (F&S Theorem I.1): for a class `C` with `C₀ = ∅`,
`(seq C)(z)·(1 - C(z)) = 1`, i.e. `SEQ(C)(z) = 1/(1 - C(z))`. -/
theorem CombClass.ogf_seq_mul (hC0 : C.counts 0 = 0) :
    C.seq.ogf * (1 - C.ogf) = 1 := by
  linear_combination CombClass.ogf_seq_functional_eq hC0

end AnalyticCombinatorics.Ch1
