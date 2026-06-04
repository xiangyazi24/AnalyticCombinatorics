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
import AnalyticCombinatorics.Ch4.Analytic.Poles
import AnalyticCombinatorics.Ch4.Analytic.Rational
import AnalyticCombinatorics.Ch4.Analytic.Fibonacci
import AnalyticCombinatorics.Ch4.Analytic.SingularityInteger
import AnalyticCombinatorics.Ch4.Analytic.SingularityGeneral
import AnalyticCombinatorics.Ch4.Analytic.CentralBinomial
import AnalyticCombinatorics.Ch4.Analytic.Catalan
import AnalyticCombinatorics.Ch4.Analytic.PringsheimCore
import AnalyticCombinatorics.Ch4.Analytic.Pringsheim
import AnalyticCombinatorics.Ch4.Analytic.DeltaDomain
import AnalyticCombinatorics.Ch4.Analytic.RepeatedPole
import AnalyticCombinatorics.Ch4.Analytic.PringsheimExample
import AnalyticCombinatorics.Ch4.Analytic.RealAsymptotics
import AnalyticCombinatorics.Ch4.Analytic.Derangements
import AnalyticCombinatorics.Ch4.Analytic.GrowthRates
import AnalyticCombinatorics.Ch4.Analytic.CauchyCoeff
import AnalyticCombinatorics.Ch4.Analytic.DeltaGeometry
import AnalyticCombinatorics.Ch4.Analytic.KernelEstimate
import AnalyticCombinatorics.Ch4.Analytic.OTransfer
import AnalyticCombinatorics.Ch4.Analytic.LittleOTransfer
import AnalyticCombinatorics.Ch4.Analytic.TransferTheorem
import AnalyticCombinatorics.Ch4.Analytic.DerivEstimate
import AnalyticCombinatorics.Ch4.Analytic.CoeffDescent
import AnalyticCombinatorics.Ch4.Analytic.LittleODescent
import AnalyticCombinatorics.Ch4.Analytic.TransferGeneral
import AnalyticCombinatorics.Ch4.Analytic.SubstComp
import AnalyticCombinatorics.Ch8.SaddlePoint.Bound
import AnalyticCombinatorics.Ch8.SaddlePoint.Assembly
import AnalyticCombinatorics.Ch8.SaddlePoint.GaussianCore
import AnalyticCombinatorics.Ch8.SaddlePoint.ExpStirling
import AnalyticCombinatorics.Ch8.SaddlePoint.Exp
import AnalyticCombinatorics.Ch8.SaddlePoint.BellBridge
import AnalyticCombinatorics.Ch8.SaddlePoint.HAdmissible
import AnalyticCombinatorics.Ch5.Meromorphic.Transfer
import AnalyticCombinatorics.Ch5.Meromorphic.Surjections
import AnalyticCombinatorics.Ch7.SingularityApp.TernaryTrees
import AnalyticCombinatorics.Ch7.SingularityApp.Motzkin
import AnalyticCombinatorics.Ch7.SingularityApp.FussCatalan

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
#print axioms PowerSeries.coeff_pole2
#print axioms PowerSeries.analyticSum_pole1_of_norm_lt_one
#print axioms PowerSeries.analyticSum_pole2_of_norm_lt_one
#print axioms meromorphicOrderAt_one_sub_inv
#print axioms PowerSeries.coeff_rescale_invOneSubPow
#print axioms _root_.simplePoleSum_dominant_isEquivalent
#print axioms _root_.coeff_mapℂ_ogf_compositions_isEquivalent
#print axioms _root_.partialFraction_eq
#print axioms _root_.fib_isEquivalent
#print axioms _root_.coeff_invOneSubPow_isEquivalent_of_one_le
#print axioms _root_.choose_standard_scale_complex
#print axioms _root_.coeff_oneDivOneSubCpow_isEquivalent
#print axioms _root_.centralBinom_isEquivalent_complex_sqrt
#print axioms _root_.catalan_isEquivalent_complex_rpow
#print axioms _root_.pringsheim_not_analyticAt
#print axioms _root_.pringsheim_not_analyticContinuation
#print axioms _root_.analyticOnNhd_one_sub_cpow_deltaDomain
#print axioms _root_.coeff_repeatedPole_isEquivalent
#print axioms _root_.geometric_singularity_at_one
#print axioms _root_.centralBinom_isEquivalent_real_sqrt
#print axioms _root_.catalan_isEquivalent_real_rpow
#print axioms _root_.fib_isEquivalent_real
#print axioms _root_.choose_standard_scale_real
#print axioms _root_.numDerangements_isEquivalent
#print axioms _root_.centralBinom_ratio_tendsto
#print axioms _root_.centralBinom_isTheta
#print axioms _root_.norm_coeff_le_of_circleIntegral
#print axioms _root_.closedBall_subset_deltaDomain
#print axioms _root_.local_disk_subset_deltaDomain
#print axioms _root_.circleKernel_integral_bound_nat
#print axioms _root_.coeff_norm_isBigO_atTop_of_delta_bound_beta_gt_one
#print axioms _root_.coeff_norm_isLittleO_atTop_of_delta_littleO_beta_gt_one
#print axioms _root_.transfer_theorem_re_alpha_gt_one
#print axioms _root_.transfer_theorem
#print axioms PowerSeries.norm_coeff_le_analyticSum_of_nonneg
#print axioms _root_.inv_factorial_le_exp_nat_div_pow_self
#print axioms PowerSeries.toFMLS_subst_eq_comp
#print axioms bell_egf_coeff_le
#print axioms _root_.coeff_isEquivalent_saddle_assembly
#print axioms _root_.central_tendsto_one_of_dominated_of_aestronglyMeasurable
#print axioms ExpStirling.inv_factorial_isEquivalent_stirling
#print axioms _root_.exists_iteratedDeriv_norm_le_deltaDomain
#print axioms _root_.coeff_norm_isBigO_atTop_of_delta_bound
#print axioms _root_.coeff_norm_isLittleO_atTop_of_delta_littleO
#print axioms CombClass.ogf_cyc
#print axioms counts_necklaces_k
#print axioms card_fixedBy_rotation

-- Ch8 saddle-point: H-admissible (Hayman) coefficient asymptotics.
-- CONDITIONAL on the `HAdmissible` structure (transfer theorem); instances
-- (proving a concrete f is H-admissible) are not yet supplied.
#print axioms _root_.central_tendsto_one_of_hadmissible
#print axioms _root_.tail_tendsto_zero_of_hadmissible
#print axioms _root_.coeff_isEquivalent_saddle_of_hadmissible_limits
#print axioms _root_.coeff_isEquivalent_saddle

-- Ch5 meromorphic coefficient transfer (F&S IV.10): analytic-remainder geometric decay,
-- principal-part subtraction, dominant simple-pole asymptotic.
#print axioms AnalyticCombinatorics.Ch5.Meromorphic.coeff_norm_isBigO_of_hasFPowerSeriesAt_differentiableOn
#print axioms AnalyticCombinatorics.Ch5.Meromorphic.coeff_sub_principalPart_isBigO_of_remainder_radius
#print axioms AnalyticCombinatorics.Ch5.Meromorphic.meromorphic_coeff_transfer_simplePoleSum
#print axioms AnalyticCombinatorics.Ch5.Meromorphic.single_simplePole_principal_isEquivalent
#print axioms AnalyticCombinatorics.Ch5.Meromorphic.dominant_simplePole_isEquivalent

-- Ch5 surjections (Fubini / ordered-Bell numbers) asymptotic (F&S Ch V):
-- r_n / n! ~ 1 / (2 (log 2)^(n+1)), via dominant simple pole of 1/(2 - e^z) at log 2.
-- The hard analytic step (remainder analytic on closedBall 2) is genuinely proved.
#print axioms AnalyticCombinatorics.Ch5.Meromorphic.Surjections.analyticRemainderFun_differentiableOn_closedBall_two
#print axioms AnalyticCombinatorics.Ch5.Meromorphic.Surjections.remainder_radius_gt_one
#print axioms AnalyticCombinatorics.Ch5.Meromorphic.Surjections.coeff_surjEGFℂ_isEquivalent
#print axioms AnalyticCombinatorics.Ch5.Meromorphic.Surjections.surjectionsCount_div_factorial_isEquivalent

-- Ch7 ternary trees / Fuss-Catalan asymptotic (F&S Ch VII, simple-variety √-singularity):
-- T_n = C(3n,n)/(2n+1) ~ (27/4)^n · √3 / (4 √π · n^(3/2)).
#print axioms _root_.ternary_choose_dvd
#print axioms _root_.choose_three_mul_isEquivalent
#print axioms _root_.ternaryTreeCount_isEquivalent

-- Ch7 Motzkin numbers asymptotic (F&S Ch VII, algebraic √-singularity at z=1/3):
-- M_n ~ (3√3/(2√π)) · 3^n · n^{-3/2}. UNCONDITIONAL (no analytic hypotheses): Δ-domain analyticity
-- + denominator nonvanishing + singular expansion + power-series bridge all proved, then TransferGeneral.
#print axioms _root_.motzkinRescaledDenominator_ne_zero
#print axioms _root_.motzkinCenteredRescaledFun_hasFPowerSeriesAt_zero
#print axioms _root_.motzkin_isEquivalent

-- Ch7 general Fuss-Catalan / p-ary trees (F&S Ch VII): for p ≥ 2,
-- C(pn,n)/((p-1)n+1) ~ (√p/((p-1)^{3/2}√(2π))) · (p^p/(p-1)^{p-1})^n · n^{-3/2}.
-- Subsumes Catalan (p=2) and ternary (p=3); consistency with ternaryTreeCount proved.
#print axioms _root_.fussCatalan_choose_dvd
#print axioms _root_.fussCatalan_isEquivalent
#print axioms _root_.fussCatalan_three_eq_ternaryTreeCount

end AnalyticCombinatorics.Ch1
