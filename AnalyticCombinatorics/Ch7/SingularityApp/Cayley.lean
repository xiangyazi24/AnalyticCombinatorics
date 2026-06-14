import Mathlib
import AnalyticCombinatorics.Ch7.SingularityApp.LabeledTreeBasic
import AnalyticCombinatorics.Ch7.SingularityApp.TreeFunction

/-!
# Cayley's formula: cardinalities of labelled trees

This file collects the cardinality results for `LabeledTree` and
`RootedLabeledTree` and connects them to the banked `cayleyRootedTree`.

The base cases `n = 0` and `n = 1` are proved here directly.  The general
`n ≥ 2` case (via the Prüfer bijection) lives in `Prufer.lean`; this file
assembles the final connection.
-/

open AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS

namespace AnalyticCombinatorics.Ch7.SingularityApp.LabeledTreeNS

/-- `Fin 0` has no vertices, so no graph on it is connected, hence no tree. -/
theorem labeledTree_zero_isEmpty : IsEmpty (LabeledTree 0) := by
  constructor
  rintro ⟨G, hG⟩
  have := hG.connected.nonempty
  exact (this.elim (fun x => x.elim0))

theorem card_labeledTree_zero : Fintype.card (LabeledTree 0) = 0 := by
  haveI := labeledTree_zero_isEmpty
  exact Fintype.card_eq_zero

/-- On a single vertex, the (unique) empty graph is a tree. -/
theorem isTree_bot_fin_one : (⊥ : SimpleGraph (Fin 1)).IsTree := by
  have hconn : (⊥ : SimpleGraph (Fin 1)).Connected := by
    refine ⟨?_⟩
    intro u v
    have huv : u = v := Subsingleton.elim u v
    subst huv
    exact SimpleGraph.Reachable.refl u
  exact ⟨hconn, SimpleGraph.isAcyclic_bot⟩

theorem card_labeledTree_one : Fintype.card (LabeledTree 1) = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨⊥, isTree_bot_fin_one⟩, ?_⟩
  rintro ⟨G, hG⟩
  exact Subtype.ext (Subsingleton.elim _ _)

/-- Rooted Cayley base cases. -/
theorem card_rootedLabeledTree_one : Fintype.card (RootedLabeledTree 1) = 1 := by
  rw [card_rootedLabeledTree_eq, card_labeledTree_one]

end AnalyticCombinatorics.Ch7.SingularityApp.LabeledTreeNS

