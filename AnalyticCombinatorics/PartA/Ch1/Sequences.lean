/-
  Chapter I § I.2 — Sequences (SEQ construction)

  SEQ(B) is the set of all finite sequences of objects from B (including empty).
  If B has OGF B(z) with B(0) = 0, then SEQ(B) has OGF 1/(1 - B(z)),
  equivalently: (1 - B(z)) · SEQ(B)(z) = 1.

  Reference: F&S Proposition I.1.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass

open PowerSeries CombinatorialClass

/-- SEQ(B): finite sequences of objects from B, including the empty sequence. -/
def seqClass (B : CombinatorialClass) : CombinatorialClass where
  Obj := List B.Obj
  size := fun xs => xs.foldr (fun b acc => B.size b + acc) 0
  finite_level n := by
    sorry -- finite level sets: bounded-length sequences with bounded total size

/-- Lift a ℕ-valued OGF to ℤ[[z]] where subtraction is available. -/
noncomputable def ogfZ (A : CombinatorialClass) : PowerSeries ℤ :=
  A.ogf.map (algebraMap ℕ ℤ)

/-- The OGF of SEQ(B) satisfies (1 - B(z)) · SEQ(z) = 1, provided B(0) = 0.
    Stated multiplicatively to avoid needing a field inverse. -/
theorem seqClass_ogf_eq (B : CombinatorialClass) (h : B.count 0 = 0) :
    (1 - ogfZ B) * ogfZ (seqClass B) = 1 := by
  sorry

/-!
### Placeholder constructions (F&S Proposition I.2)

MSET(B): multisets — OGF is the Euler product ∏ₙ (1 - zⁿ)^{-bₙ}
PSET(B): powersets — OGF is ∏ₙ (1 + zⁿ)^{bₙ}
CYC(B):  cyclic sequences — OGF is Σₖ φ(k)/k · log(1/(1 - B(zᵏ)))

Full statements require multivariate / EGF machinery; deferred.
-/
