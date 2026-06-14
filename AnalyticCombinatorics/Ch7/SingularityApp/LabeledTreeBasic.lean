import Mathlib

/-!
# Labelled trees on a finite vertex set

We introduce the genuine combinatorial object underlying Cayley's formula: the
type of labelled trees on `Fin n`, namely simple graphs on `Fin n` that are
trees (connected and acyclic), and the rooted version.  These are finite types.

The cardinality results (`card (LabeledTree n) = n^(n-2)`,
`card (RootedLabeledTree n) = n^(n-1)`) and the connection to the banked
`cayleyRootedTree` are established in `Prufer.lean` / `Cayley.lean`.
-/

namespace AnalyticCombinatorics.Ch7.SingularityApp.LabeledTreeNS

/-- A labelled tree on `n` vertices: a simple graph on `Fin n` that is a tree. -/
def LabeledTree (n : ℕ) : Type :=
  {G : SimpleGraph (Fin n) // G.IsTree}

/-- A rooted labelled tree on `n` vertices. -/
def RootedLabeledTree (n : ℕ) : Type :=
  LabeledTree n × Fin n

instance instFiniteLabeledTree (n : ℕ) : Finite (LabeledTree n) := by
  unfold LabeledTree; infer_instance

noncomputable instance instFintypeLabeledTree (n : ℕ) : Fintype (LabeledTree n) :=
  Fintype.ofFinite _

noncomputable instance instFintypeRootedLabeledTree (n : ℕ) :
    Fintype (RootedLabeledTree n) := by
  unfold RootedLabeledTree; infer_instance

/-- The rooted count factors as the unrooted count times `n`. -/
theorem card_rootedLabeledTree_eq (n : ℕ) :
    Fintype.card (RootedLabeledTree n) = Fintype.card (LabeledTree n) * n := by
  show Fintype.card (LabeledTree n × Fin n) = _
  rw [Fintype.card_prod, Fintype.card_fin]

end AnalyticCombinatorics.Ch7.SingularityApp.LabeledTreeNS
