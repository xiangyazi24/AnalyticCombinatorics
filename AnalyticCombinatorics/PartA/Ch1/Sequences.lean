/-
  Chapter I § I.2 — Sequences (SEQ construction)

  SEQ(B) is the set of all finite sequences of objects from B (including empty).
  If B has OGF B(z) with B(0) = 0, then SEQ(B) has OGF 1/(1 - B(z)),
  equivalently: (1 - B(z)) · SEQ(B)(z) = 1.

  Reference: F&S Proposition I.1.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Set.Finite.List
import Mathlib.Algebra.Order.BigOperators.Group.List
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass

open PowerSeries CombinatorialClass

/-- SEQ(B): finite sequences of objects from B, including the empty sequence.
    Requires B(0) = 0 to ensure level sets are finite. -/
def seqClass (B : CombinatorialClass) (hB : B.count 0 = 0) : CombinatorialClass where
  Obj := List B.Obj
  size := fun xs => xs.foldr (fun b acc => B.size b + acc) 0
  finite_level n := by
    -- Local replacement for private level_mem_iff
    have mem_level : ∀ (m : ℕ) (x : B.Obj), x ∈ B.level m ↔ B.size x = m := fun m x => by
      change x ∈ (B.finite_level m).toFinset ↔ B.size x = m
      exact (B.finite_level m).mem_toFinset.trans (by simp)
    -- All elements have size ≥ 1, since hB rules out size-0 objects
    have hpos : ∀ b : B.Obj, 1 ≤ B.size b := by
      intro b
      rcases Nat.eq_zero_or_pos (B.size b) with h0 | h
      · exfalso
        have := Finset.card_pos.mpr ⟨b, (mem_level 0 b).mpr h0⟩
        simp only [count] at hB; omega
      · omega
    -- A list of total size n has length ≤ n
    have hlen_bound : ∀ ys : List B.Obj,
        ys.length ≤ ys.foldr (fun b acc => B.size b + acc) 0 := by
      intro ys
      induction ys with
      | nil => simp
      | cons a t ih =>
        simp only [List.length_cons, List.foldr_cons]
        linarith [hpos a]
    -- Each member of a list of total size n has individual size ≤ that total
    have helem_le : ∀ (ys : List B.Obj) (b : B.Obj), b ∈ ys →
        B.size b ≤ ys.foldr (fun b acc => B.size b + acc) 0 := by
      intro ys
      induction ys with
      | nil => intro _ h; simp_all
      | cons a t ih =>
        intro b hb
        simp only [List.mem_cons, List.foldr_cons] at *
        rcases hb with rfl | hb
        · omega
        · linarith [ih b hb]
    -- Cover: all B.Obj with size < n+1, indexed by Fin (n+1)
    let S : Set B.Obj := ⋃ k : Fin (n + 1), ↑(B.level k.val)
    have hSfin : S.Finite := Set.finite_iUnion (fun k => (B.level k.val).finite_toSet)
    have hmemS : ∀ xs : List B.Obj, xs.foldr (fun b acc => B.size b + acc) 0 = n →
        ∀ b ∈ xs, b ∈ S := by
      intro xs hxs b hb
      simp only [S, Set.mem_iUnion, Finset.mem_coe]
      have hle := helem_le xs b hb
      exact ⟨⟨B.size b, by omega⟩, (mem_level _ b).mpr rfl⟩
    haveI : Finite {x : B.Obj // x ∈ S} := hSfin.to_subtype
    apply Set.Finite.subset
      ((List.finite_length_le {x : B.Obj // x ∈ S} n).image (List.map Subtype.val))
    intro xs hxs
    simp only [Set.mem_image, Set.mem_setOf_eq]
    have hxs' : xs.foldr (fun b acc => B.size b + acc) 0 = n := hxs
    refine ⟨xs.attachWith (· ∈ S) (hmemS xs hxs'), ?_,
            List.attachWith_map_subtype_val (hmemS xs hxs')⟩
    rw [List.length_attachWith]
    have h1 := hlen_bound xs
    omega

/-- Lift a ℕ-valued OGF to ℤ[[z]] where subtraction is available. -/
noncomputable def ogfZ (A : CombinatorialClass) : PowerSeries ℤ :=
  A.ogf.map (algebraMap ℕ ℤ)

/-- The OGF of SEQ(B) satisfies (1 - B(z)) · SEQ(z) = 1, provided B(0) = 0.
    Stated multiplicatively to avoid needing a field inverse. -/
theorem seqClass_ogf_eq (B : CombinatorialClass) (h : B.count 0 = 0) :
    (1 - ogfZ B) * ogfZ (seqClass B h) = 1 := by
  sorry

/-!
### Placeholder constructions (F&S Proposition I.2)

MSET(B): multisets — OGF is the Euler product ∏ₙ (1 - zⁿ)^{-bₙ}
PSET(B): powersets — OGF is ∏ₙ (1 + zⁿ)^{bₙ}
CYC(B):  cyclic sequences — OGF is Σₖ φ(k)/k · log(1/(1 - B(zᵏ)))

Full statements require multivariate / EGF machinery; deferred.
-/
