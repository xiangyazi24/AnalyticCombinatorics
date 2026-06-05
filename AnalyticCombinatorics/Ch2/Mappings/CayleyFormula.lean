import Mathlib
import AnalyticCombinatorics.Ch2.Mappings.ForestCount
import AnalyticCombinatorics.Ch2.Mappings.ForestCountComplete

/-!
# Cayley's formula (arborescence form)

The `k = 1` instantiation of the generalized forest count `card_rootedForests`:
the number of trees on `n` labeled vertices rooted at a FIXED vertex — in the functional
formulation, parent maps on the remaining `n-1` vertices under which every vertex reaches the
root — equals `n^(n-2)`.  Since unrooted labeled trees on `[n]` correspond bijectively to
arborescences toward any fixed root, this is the classical Cayley count `n^(n-2)`.

This is an honest *instantiation corollary* of `ForestCountNS.Complete.card_rootedForests`
(banked separately); it is recorded here so the textbook-named statement is explicit.
-/

namespace AnalyticCombinatorics.Ch2.Mappings.ForestCountNS

/-- **Cayley's formula, arborescence form**: parent maps toward a fixed root `r` on `Fin n`
(every vertex reaches `r`) number exactly `n^(n-2)`. -/
theorem card_rootedForests_singleton {n : ℕ} (r : Fin n) (hn : 1 < n) :
    @Fintype.card (RootedForests ({r} : Finset (Fin n)))
        (rootedForestsFintype ({r} : Finset (Fin n))) = n ^ (n - 2) := by
  have h := Complete.card_rootedForests (k := 1) ({r} : Finset (Fin n))
    (by simp) (by norm_num) (by simpa using hn)
  have hexp : n - 1 - 1 = n - 2 := by omega
  simpa [hexp] using h

end AnalyticCombinatorics.Ch2.Mappings.ForestCountNS
