import AnalyticCombinatorics.Ch1.OGF.Defs
import AnalyticCombinatorics.Ch1.OGF.Sum
import AnalyticCombinatorics.Ch1.OGF.Product
import AnalyticCombinatorics.Ch1.OGF.Sequence
import AnalyticCombinatorics.Ch1.OGF.Compositions

/-!
# Axiom audit for the Ch1 OGF transfer layer

Every headline result must depend only on the three core axioms
`{propext, Classical.choice, Quot.sound}` — no `sorryAx`, no
`Lean.ofReduceBool`/`trustCompiler` (i.e. no `native_decide`). This file keeps
its own import list; add a `#print axioms` line here whenever a new headline
theorem is proved.
-/

namespace AnalyticCombinatorics.Ch1

#print axioms CombClass.ogf_neutral
#print axioms CombClass.ogf_atom
#print axioms CombClass.counts_sum
#print axioms CombClass.ogf_sum
#print axioms CombClass.counts_prod
#print axioms CombClass.ogf_prod
#print axioms CombClass.ogf_neutral_prod
#print axioms CombClass.counts_seq
#print axioms CombClass.counts_seq_posInt
#print axioms CombClass.counts_seq_posInt_eq_compositions
#print axioms CombClass.ogf_compositions

end AnalyticCombinatorics.Ch1
