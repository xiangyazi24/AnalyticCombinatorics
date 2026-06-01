import AnalyticCombinatorics.Ch1.OGF.Defs
import AnalyticCombinatorics.Ch1.OGF.Sum
import AnalyticCombinatorics.Ch1.OGF.Product
import AnalyticCombinatorics.Ch1.OGF.Sequence
import AnalyticCombinatorics.Ch1.OGF.Compositions
import AnalyticCombinatorics.Ch1.OGF.SeqFormula
import AnalyticCombinatorics.Ch1.OGF.ProductPower
import AnalyticCombinatorics.Ch1.OGF.SequenceInverse
import AnalyticCombinatorics.Ch1.OGF.SeqApplications
import AnalyticCombinatorics.Ch1.OGF.Fibonacci
import AnalyticCombinatorics.Ch1.OGF.Partitions
import AnalyticCombinatorics.Ch1.OGF.Mset
import AnalyticCombinatorics.Ch1.OGF.Pset
import AnalyticCombinatorics.Ch1.OGF.DistinctPartitions
import AnalyticCombinatorics.Ch1.OGF.Pointing
import AnalyticCombinatorics.Ch1.OGF.CycleOGF
import AnalyticCombinatorics.Ch2.EGF.Defs
import AnalyticCombinatorics.Ch2.EGF.LabelledProduct
import AnalyticCombinatorics.Ch2.EGF.LabelledSum
import AnalyticCombinatorics.Ch2.EGF.LabelledPower
import AnalyticCombinatorics.Ch2.EGF.LabelledSet
import AnalyticCombinatorics.Ch2.EGF.SetExp
import AnalyticCombinatorics.Ch2.EGF.LabelledSetOde
import AnalyticCombinatorics.Ch2.EGF.LabelledSetExp
import AnalyticCombinatorics.Ch2.EGF.LabelledSeq
import AnalyticCombinatorics.Ch2.EGF.Applications
import AnalyticCombinatorics.Ch2.EGF.LabelledCyc
import AnalyticCombinatorics.Ch3.BGF.Defs
import AnalyticCombinatorics.Ch3.BGF.Moments
import AnalyticCombinatorics.Ch3.BGF.Variance
import AnalyticCombinatorics.Ch3.BGF.SeqMarked
import AnalyticCombinatorics.Ch3.BGF.BinaryWords
import AnalyticCombinatorics.Ch3.BGF.LabelledSeqMarked
import AnalyticCombinatorics.Ch3.BGF.LabelledSetMarked
import AnalyticCombinatorics.Ch3.BGF.LabelledBGFApplications
import AnalyticCombinatorics.Ch3.BGF.CompositionMoments
import AnalyticCombinatorics.Ch3.BGF.BinaryWordMoments
import AnalyticCombinatorics.Ch4.Analytic.Bridge

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
#print axioms CombClass.ogf_posInt
#print axioms CombClass.ogf_compositions_eq_seq_posInt
#print axioms CombClass.ogf_prodPow
#print axioms CombClass.ogf_words
#print axioms CombClass.ogf_seq_functional_eq
#print axioms CombClass.ogf_seq_mul
#print axioms counts_seq_alphabet
#print axioms ogf_seq_alphabet
#print axioms ogf_seq_posInt
#print axioms counts_seq_parts12
#print axioms CombClass.ogf_seq_parts12
#print axioms CombClass.ogf_partitions_eq_genFun
#print axioms CombClass.ogf_partitions
#print axioms CombClass.counts_mset
#print axioms CombClass.ogf_mset_eq_genFun
#print axioms CombClass.ogf_mset
#print axioms CombClass.counts_pset
#print axioms CombClass.ogf_pset
#print axioms CombClass.ogf_pset_posInt
#print axioms CombClass.ogf_pointing
#print axioms CombClass.egf_permutations
#print axioms CombClass.egf_setClass
#print axioms CombClass.counts_lprod
#print axioms CombClass.egf_lprod
#print axioms CombClass.egf_sum
#print axioms CombClass.egf_lpow
#print axioms CombClass.counts_set
#print axioms CombClass.subst_exp_ode
#print axioms ode_unique
#print axioms CombClass.counts_set_succ
#print axioms CombClass.egf_set_ode
#print axioms CombClass.counts_set_zero
#print axioms CombClass.egf_set
#print axioms CombClass.egf_lseq
#print axioms CombClass.egf_bell
#print axioms CombClass.egf_surjections
#print axioms CombClass.egf_involutions
#print axioms ParamClass.coeff_bgf
#print axioms ParamClass.bgf_sum
#print axioms ParamClass.bgf_prod
#print axioms ParamClass.evalU1_bgf
#print axioms ParamClass.coeff_factorialMoment1
#print axioms ParamClass.mean_eq
#print axioms ParamClass.evalU1_compositionsByParts
#print axioms ParamClass.coeff_rawMoment2
#print axioms ParamClass.variance_eq
#print axioms ParamClass.bgf_compositionsByParts_closed
#print axioms CombClass.egf_lcyc_ode
#print axioms CombClass.egf_lcyc_unique
#print axioms CombClass.constantCoeff_egf_lcyc
#print axioms ParamClass.bgf_seqMarked_closed
#print axioms ParamClass.bgf_binaryWords_closed
#print axioms ParamClass.begf_lseqMarked_closed
#print axioms ParamClass.begf_surjections
#print axioms ParamClass.begf_setMarked_exp
#print axioms ParamClass.begf_setPartitionsByBlocks
#print axioms ParamClass.begf_involutionsByComponents
#print axioms ParamClass.mean_compositionsByParts
#print axioms ParamClass.variance_compositionsByParts
#print axioms ParamClass.mean_binaryWords
#print axioms ParamClass.variance_binaryWords
#print axioms PowerSeries.radius_toFMLS_inv_eq_limsup
#print axioms PowerSeries.analyticAt_analyticSum
#print axioms CombClass.ogf_cyc
#print axioms counts_necklaces_k
#print axioms card_fixedBy_rotation

end AnalyticCombinatorics.Ch1
