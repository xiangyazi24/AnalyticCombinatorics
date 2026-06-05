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
import AnalyticCombinatorics.Ch2.Mappings.RamanujanQ
import AnalyticCombinatorics.Ch2.Mappings.RamanujanQSharp
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
import AnalyticCombinatorics.Ch4.Analytic.LogSingularity
import AnalyticCombinatorics.Ch8.SaddlePoint.Bound
import AnalyticCombinatorics.Ch8.SaddlePoint.Assembly
import AnalyticCombinatorics.Ch8.SaddlePoint.GaussianCore
import AnalyticCombinatorics.Ch8.SaddlePoint.ExpStirling
import AnalyticCombinatorics.Ch8.SaddlePoint.Exp
import AnalyticCombinatorics.Ch8.SaddlePoint.BellBridge
import AnalyticCombinatorics.Ch8.SaddlePoint.HAdmissible
import AnalyticCombinatorics.Ch8.SaddlePoint.ExpHAdmissible
import AnalyticCombinatorics.Ch8.SaddlePoint.BellHAdmissible
import AnalyticCombinatorics.Ch8.SaddlePoint.InvolutionHAdmissible
import AnalyticCombinatorics.Ch8.SaddlePoint.Blocks3HAdmissible
import AnalyticCombinatorics.Ch5.Meromorphic.Transfer
import AnalyticCombinatorics.Ch5.Meromorphic.Surjections
import AnalyticCombinatorics.Ch5.Meromorphic.Alignments
import AnalyticCombinatorics.Ch5.Meromorphic.Tangent
import AnalyticCombinatorics.Ch5.Meromorphic.Secant
import AnalyticCombinatorics.Ch5.Meromorphic.SupercriticalSeq
import AnalyticCombinatorics.Ch5.Meromorphic.SupercriticalSeqGenuine
import AnalyticCombinatorics.Ch5.Meromorphic.FibonacciCompositions
import AnalyticCombinatorics.Ch7.SingularityApp.TernaryTrees
import AnalyticCombinatorics.Ch7.SingularityApp.Motzkin
import AnalyticCombinatorics.Ch7.SingularityApp.FussCatalan
import AnalyticCombinatorics.Ch7.SingularityApp.TwoRegular
import AnalyticCombinatorics.Ch7.SingularityApp.FussCatalanInstances
import AnalyticCombinatorics.Ch7.SingularityApp.TwoRegularClass
import AnalyticCombinatorics.Ch7.SingularityApp.Schroeder
import AnalyticCombinatorics.Ch7.SingularityApp.Riordan
import AnalyticCombinatorics.Ch7.SingularityApp.TreeFunction
import AnalyticCombinatorics.Ch7.SingularityApp.Forests
import AnalyticCombinatorics.Ch9.LimitLaws.QuasiPowers
import AnalyticCombinatorics.Ch9.LimitLaws.BinaryWordCLT
import AnalyticCombinatorics.Ch9.LimitLaws.PermutationCycles
import AnalyticCombinatorics.Ch9.LimitLaws.FixedPointsPoisson
import AnalyticCombinatorics.Ch9.LimitLaws.PMFToDistribution
import AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoisson
import AnalyticCombinatorics.Ch9.LimitLaws.RCyclesFactorialMoment
import AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonComplete
import AnalyticCombinatorics.Ch9.LimitLaws.JointCycleMoments
import AnalyticCombinatorics.Ch9.LimitLaws.JointCycleMomentsGeneral
import AnalyticCombinatorics.Ch9.LimitLaws.BivariateCyclePoisson
import AnalyticCombinatorics.Ch9.LimitLaws.MultivariateCyclePoisson
import AnalyticCombinatorics.Ch9.LimitLaws.ExpectedCycles
import AnalyticCombinatorics.Ch9.LimitLaws.CycleVariance
import AnalyticCombinatorics.Ch9.LimitLaws.CompositionParts

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

-- Ch9 quasi-powers / Gaussian limit law (F&S/Hwang IX.8), characteristic-function formulation.
-- FAITHFUL framework theorem: given the quasi-powers charFun form + scaled-remainder→0 (the genuine
-- Hwang hypothesis, via Mathlib's Levy continuity theorem), (X_n - β_n u₁)/√(β_n u₂) →d N(0,1);
-- plus the mean/variance asymptotics. CONDITIONAL on the quasi-powers analytic input (no instance yet).
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.quasiPowers_tendstoInDistribution_of_continuousAt
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.expectation_sub_quasiPowerCoeff_isBigO
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.variance_sub_quasiPowerCoeff_isBigO

-- Ch9 first concrete instance of quasi-powers: number of ones in a uniform binary word is
-- asymptotically Gaussian (UNCONDITIONAL) — demonstrates the (now local-hChar, faithful) framework
-- is non-vacuous.
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.binaryWord_symbolCount_tendstoInDistribution_gaussian

-- Ch9 fixed points of a random permutation → Poisson(1) (DISCRETE limit law, not Gaussian): exact
-- factorial moments E[(F_n)_k]=1 (k≤n), and pmf P(F_n=j)=C(n,j)D_{n-j}/n! → poissonPMFReal 1 j (e^{-1}/j!).
-- Full weak-convergence blocked on a missing Mathlib pmf⟹weak bridge (honestly reported, not faked).
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.FixedPointsPoissonNS.fixedPoint_factorialMoment_eq_one
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.FixedPointsPoissonNS.fixedPointPMF_tendsto_poissonPMFReal_one

-- Ch9 reusable bridge (fills a Mathlib gap): pointwise singleton-mass convergence of ProbabilityMeasure ℕ
-- ⟹ weak convergence (portmanteau finite-subset approximation). Upgrades fixed-points → FULL Poisson(1).
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.PMFToDistribution.probabilityMeasure_nat_tendsto_of_tendsto_singleton
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.PMFToDistribution.FixedPointsPoissonNS.fixedPoints_tendstoInDistribution_poisson_one

-- Ch9 r-cycles → Poisson(1/r) (Goncharov, F&S Ch IX): UNCONDITIONAL analytic limit of the
-- inclusion-exclusion truncated-exponential pmf formula, (r^j j!)⁻¹·expPartial(-1/r, ⌊n/r⌋-j+1)
-- → e^{-1/r}(1/r)^j/j!. The moving truncation index ⌊n/r⌋→∞ is the analytic crux. (The full
-- weak-convergence for general r is reduced, via the reusable bridge, to the marginal cycle-count
-- enumeration rCyclePMF = rCyclePMFFormula — a genuine Mathlib gap, left conditional; see RCyclesPoisson.)
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.rCyclePMFFormula_tendsto_poisson

-- Ch9 r-cycle FACTORIAL-MOMENT identity (Goncharov, F&S Ch III/IX): fills the documented Mathlib gap
-- (no marginal cycle-length enumeration). Proved from FIRST PRINCIPLES via genuine Equiv bijections
-- (delete a distinguished r-cycle ↔ permute the complement) + induction. Core: r^k·Σ_σ (cycleType.count r)_k
-- = n! ⟹ E[(C_{n,r})_k] = r^{-k} (general k) over the genuine uniform permutation average; incl. the
-- classic mean E[C_{n,r}] = 1/r. (Distribution-level Poisson(1/r) still needs a factorial-moment⟹law bridge.)
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.FM.cycleType_count_factorialMoment_sum_in
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.rCycle_mean_eq_inv
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.factorialMoment_rCycle

-- Ch9 r-cycles → Poisson(1/r) COMPLETED to UNCONDITIONAL (F&S Ch IX, Goncharov, flagship). Closes the gap
-- via the finite method-of-factorial-moments: rCycleCount ≤ ⌊n/r⌋ (bounded) + finite_pmf_eq_factorial_moment_sum
-- (the general pmf-inversion for bounded ℕ-valued r.v. on a finite space, a reusable Mathlib-gap filler) +
-- the EXACT moments r^{-k} ⟹ rCyclePMF = rCyclePMFFormula (exact Goncharov pmf) ⟹ full TendstoInDistribution
-- to Poisson(1/r). The number of length-r cycles of a uniform random permutation →d Poisson(1/r), end-to-end.
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.Complete.finite_pmf_eq_factorial_moment_sum
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.Complete.rCyclePMF_eq_formula
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.Complete.rCycles_tendstoInDistribution_poisson

-- Ch9 JOINT cycle factorial moments (Goncharov–Kolchin foundation, F&S Ch IX): for two DISTINCT positive
-- lengths, the mixed factorial moment E[(C_{n,r})_a (C_{n,s})_b] = r^{-a}·s^{-b} (r·a+s·b ≤ n) — proved by
-- extending the deletion bijection with cross-length cycle DISJOINTNESS. ⟹ cycle counts of two different
-- lengths are uncorrelated/independent at the factorial-moment level; incl. covariance E[C_{n,r}C_{n,s}]=1/(rs).
-- (General >2-length family: documented remaining work — indexed-family deletion induction.)
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.JointCycleMomentsNS.factorialMoment_two_rCycle_of_pos
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.JointCycleMomentsNS.rCycleCount_mul_mean_eq_inv_mul_inv

-- Ch9 GENERAL finite-family joint factorial moments (full Goncharov–Kolchin moment characterization,
-- F&S Ch IX): for any Finset S of distinct positive lengths, E[∏_{r∈S} (C_{n,r})_{k_r}] = ∏_{r∈S} r^{-k_r}
-- (Σ r·k_r ≤ n) — proved by the indexed-family deletion induction (peel one distinguished cycle, the
-- disjointness preservation lemmas keep every other length's count intact). The joint factorial moments
-- FACTOR as the product of independent Poisson(1/r) factorial moments ⟹ asymptotic independence of cycle
-- counts at the moment level. Joint-mean corollary E[∏_{r∈S} C_{n,r}] = ∏_{r∈S} 1/r.
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.JointCycleMomentsGeneralNS.factorialMoment_rCycle_finset
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.JointCycleMomentsGeneralNS.rCycleCount_prod_mean_eq_prod_inv

-- Ch9 BIVARIATE Goncharov–Kolchin IN DISTRIBUTION (flagship, F&S Ch IX): the joint law of two cycle counts
-- (C_{n,r}, C_{n,s}) for distinct r≠s converges WEAKLY to the PRODUCT Poisson(1/r) ⊗ Poisson(1/s) — i.e.
-- cycle counts of distinct lengths are asymptotically INDEPENDENT Poissons. Closed end-to-end via: bivariate
-- pmf inversion (tensor of the 1-D factorial-moment kernel) + EXACT joint moments r^{-a}s^{-b} ⟹ joint pmf →
-- product Poisson pmf; then the reusable ℕ×ℕ pmf⟹weak bridge. The ℕ×ℕ bridge generalizes the 1-D one and
-- fills a Mathlib gap on its own.
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.Bivariate.probabilityMeasure_nat_prod_tendsto_of_tendsto_singleton
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.Bivariate.jointRCyclePMF_tendsto_poisson_product
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.Bivariate.jointLaw_tendsto_poissonProduct

-- Ch9 GENERAL MULTIVARIATE Goncharov–Kolchin IN DISTRIBUTION (THE theorem, F&S Ch IX — capstone): for ANY
-- finite family of distinct positive lengths r_1,…,r_m, the joint law of (C_{n,r_1},…,C_{n,r_m}) converges
-- WEAKLY to the product ⨂_i Poisson(1/r_i) on Fin m → ℕ. Cycle counts are asymptotically INDEPENDENT
-- Poissons — fully general, end-to-end, unconditional. Via: m-fold tensor pmf inversion + exact general
-- joint moments ∏ r_i^{-k_i} ⟹ joint pmf → product pmf; the reusable (Fin m → ℕ) pmf⟹weak bridge
-- (generalizes the 1-D and ℕ×ℕ bridges; itself fills a Mathlib gap).
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.Multivariate.probabilityMeasure_pi_nat_tendsto_of_tendsto_singleton
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.Multivariate.multivariatePMF_tendsto_poissonPiPMF
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.Multivariate.multivariateLaw_tendsto_poissonPi

-- Ch2 Ramanujan Q-function (birthday paradox / random-mappings scale, F&S II.3): PARTIAL — order-sharp
-- Θ(√n) with the sharp upper Gaussian envelope Q(n) ≤ 1 + √(πn/2) (Laplace-for-sums upper comparison) and
-- an eventual lower √n/4. The full equivalence Q ~ √(πn/2) needs the sharp lower head expansion — flagged
-- remaining work, NOT claimed. Genuine sum-of-products definition.
#print axioms AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS.ramanujanQ_le_one_add_sqrt_pi_mul_nat_div_two
#print axioms AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS.ramanujanQ_isTheta_sqrt

-- Ch2 Ramanujan Q FULL asymptotic (upgrade of the Θ result): Q(n) ~ √(πn/2) UNCONDITIONAL — the complete
-- Laplace-method-for-sums (sharp lower head expansion k=o(n^{2/3}) with exp(-k(k+1)/2n - O(k³/n²)) envelope
-- + Gaussian sum-integral comparison both sides + tails). Birthday-paradox / random-mappings scale, F&S II.3.
#print axioms AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS.Sharp.ramanujanQ_tendsto_ratio_one
#print axioms AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS.Sharp.ramanujanQ_isEquivalent

-- Ch9 expected number of cycles = harmonic number (F&S Ch IX, Goncharov; Opus-authored). By linearity of
-- the uniform-permutation expectation over the banked per-length means E[C_{n,r}]=1/r:
-- E[#cycles] = E[∑_{r=1}^n C_{n,r}] = ∑_{r=1}^n 1/r = H_n (∼ log n cycles in a random permutation).
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.expected_totalCycles_eq_harmonic

-- Ch9 variance of the r-cycle count = 1/r (Opus-authored, second-moment confirmation of Poisson(1/r)).
-- Var(C_{n,r}) = E[(C_{n,r})_2] + E[C_{n,r}] - (E[C_{n,r}])² = 1/r² + 1/r - 1/r² = 1/r (2r ≤ n),
-- from the banked factorial moments. Matches the Poisson(1/r) variance.
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.rCycle_variance_eq_inv

-- Ch9 cycle counts of two distinct lengths are UNCORRELATED (Opus-authored): Cov(C_{n,r},C_{n,s}) =
-- E[C_r C_s] - E[C_r]E[C_s] = 1/(rs) - (1/r)(1/s) = 0 (distinct positive r,s, r+s ≤ n). Second-moment
-- shadow of Goncharov–Kolchin asymptotic independence, from the banked joint moment + means.
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.rCycle_covariance_eq_zero

-- Ch9 permutation cycle-count CLT (Goncharov, F&S Ch IX): the number of cycles of a uniform random
-- permutation (Feller-coupling realization: sum of independent Bernoulli(1/k)) satisfies
-- (C_n − H_n)/√H_n →d N(0,1), UNCONDITIONAL. cycle_hChar = the local quasi-powers hypothesis, PROVED.
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.cycle_hChar
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.permutationCycles_tendstoInDistribution_gaussian

-- Ch7 2-regular labelled graphs (F&S Ch VI/VII, √-singularity): coefficients of the EGF
-- exp(-z/2-z²/4)/√(1-z) satisfy g_n/n! ~ (e^{-3/4}/√π)·n^{-1/2}, via the general transfer (α=1/2,
-- entire prefactor). NOTE: twoRegularGraphCount is DEFINED as n!·[z^n] of that EGF — a GF-coefficient
-- asymptotic; the identity "this EGF counts 2-regular graphs" is the (standard, numerically-checked)
-- combinatorial input, not proved in Lean here.
#print axioms _root_.twoRegularGraphCount_div_factorial_isEquivalent
#print axioms _root_.twoRegularAsymptoticConstant_eq

-- Ch7 named Fuss-Catalan instances (p-ary trees: quaternary/quinary/senary), specializations of the
-- general theorem with explicit growth bases. (Opus-authored during codex outage.)
#print axioms AnalyticCombinatorics.Ch7.SingularityApp.fussCatalan_four_isEquivalent
#print axioms AnalyticCombinatorics.Ch7.SingularityApp.fussCatalan_five_isEquivalent

-- Ch9 composition part-count CLT (F&S Ch IX): #parts of a uniform random composition of n is
-- asymptotically Gaussian. HIGH FIDELITY: card_compositionsWithParts_eq_choose proves the genuine
-- combinatorial count #{c : Composition n // c.length = k} = C(n-1,k-1) (via compositionAsSetEquiv).
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.card_compositionsWithParts_eq_choose
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.compositionParts_tendstoInDistribution_gaussian

-- Ch5 alignments (sequences of cycles, F&S Ch V): genuine class count alignmentClass.counts;
-- o_n/n! ~ (1/(e-1))·(e/(e-1))^n via dominant simple pole of 1/(1-log(1/(1-z))) at ρ=1-1/e.
#print axioms AnalyticCombinatorics.Ch5.Meromorphic.Alignments.alignmentEGFℂ_mul_denominator
#print axioms AnalyticCombinatorics.Ch5.Meromorphic.Alignments.alignmentCount_div_factorial_isEquivalent

-- Ch5 supercritical-sequence dominant-pole transfer (SEQ-form constant c=1/C'(ρ)). Honest thin wrapper
-- around dominant_simplePole_isEquivalent (decorative C-hypotheses removed); genuine F&S V.2 derivation
-- of the decomposition from C(ρ)=1 is flagged future work.
#print axioms AnalyticCombinatorics.Ch5.Meromorphic.supercriticalSeq_isEquivalent

-- Ch7 2-regular graphs UPGRADED to genuine combinatorial fidelity: twoRegularClass = SET of undirected
-- cycles (length ≥3, = directed cycle mod reversal, card (n-1)!/2), EGF derived, count proved equal to
-- the earlier GF-coeff count; asymptotic now holds for the genuine combinatorial count.
#print axioms _root_.TwoRegularClass.undirectedCycle_card_of_three_le
#print axioms _root_.TwoRegularClass.twoRegularClass_counts_eq_twoRegularGraphCount
#print axioms _root_.TwoRegularClass.twoRegularClass_counts_div_factorial_isEquivalent

-- Ch5 GENUINE supercritical-sequence schema (F&S V.2): the principal+remainder decomposition is now
-- DERIVED from the supercritical data (C(ρ)=1, analytic, C'(ρ)≠0, ρ dominant), not assumed —
-- closing the earlier thin-wrapper's flagged future-work. coeff(1/(1-C)) ~ (1/(ρC'(ρ)))ρ^{-n}.
#print axioms AnalyticCombinatorics.Ch5.Meromorphic.SupercriticalSeqGenuine.supercriticalSeq_decomposition_from_supercritical_data
#print axioms AnalyticCombinatorics.Ch5.Meromorphic.SupercriticalSeqGenuine.supercriticalSeq_isEquivalent_from_supercritical_data

-- Ch8 FIRST HAdmissible instance (closes the original session-start CONDITIONAL gap): expHAdmissible is a
-- fully-constructed HAdmissible Complex.exp (local_uniform + tail_uniform proved), and the exp asymptotic
-- is derived THROUGH the general Hayman interface coeff_isEquivalent_saddle — so that interface is now
-- demonstrably NON-VACUOUS.
#print axioms _root_.ExpStirling.expHAdmissible
#print axioms _root_.ExpStirling.exp_coeff_isEquivalent_saddle_from_HAdmissible

-- Ch8 Bell HAdmissible instance — the Hayman flagship (f = e^{e^z-1}, saddle r·e^r=n). Full instance
-- (local_uniform + tail_uniform proved), Bell asymptotic through the general interface, tied to the
-- genuine combinatorial Bell count (posInt.set.counts = set partitions): B_n/n! ~ saddleScale.
#print axioms _root_.bellHAdmissible
#print axioms _root_.bell_number_over_factorial_isEquivalent_saddle

-- Ch8 involutions HAdmissible instance (3rd Hayman instance; f = e^{z+z²/2}, saddle r+r²=n). Genuine
-- combinatorial count parts12.set (SET of size-1-or-2 components = fixed points + transpositions =
-- involutions, since parts12.counts = (0,1,1,0,…)). I_n/n! ~ saddleScale via the general interface.
#print axioms _root_.InvolutionHAdmissible.involHAdmissible
#print axioms _root_.InvolutionHAdmissible.involution_count_over_factorial_isEquivalent_saddle

-- Ch7 large Schröder numbers (F&S Ch VII, algebraic √-singularity): genuine recurrence
-- S(n+1)=S(n)+ΣS(k)S(n-k), OGF zS²+(z-1)S+1=0, ρ=3-2√2; S_n ~ C·(3+2√2)^n·n^{-3/2} via general transfer.
#print axioms _root_.schroeder_isEquivalent

-- Ch7 Riordan numbers (F&S Ch VII, Motzkin-sister √-singularity at 1/3): genuine first-return def
-- R_{n+2}=Σ M_k R_{n-k} (R=1+z²MR); R_n ~ (3√3/(8√π))·3^n·n^{-3/2} via general transfer.
#print axioms _root_.riordan_isEquivalent

-- Ch5 tangent numbers (F&S Ch V, NEW two-pole meromorphic transfer): tan z has dominant simple poles at
-- ±π/2 (residue −1); remainder analytic past radius 2 (next poles ±3π/2) — PROVED. UNCONDITIONAL:
-- T_n/n! ~ 2(2/π)^{n+1} (odd n). First two-dominant-pole transfer in the repo.
#print axioms AnalyticCombinatorics.Ch5.Meromorphic.Tangent.tangentRemainder_radius_gt_two
#print axioms AnalyticCombinatorics.Ch5.Meromorphic.Tangent.tangentNumber_div_factorial_odd_isEquivalent

-- Ch5 secant/Euler numbers (F&S Ch V): sec z poles ±π/2 (residues ∓1), reusing the two-pole machinery;
-- UNCONDITIONAL E_{2n}/(2n)! ~ 2(2/π)^{2k+1} (even n).
#print axioms AnalyticCombinatorics.Ch5.Meromorphic.Secant.secantNumber_div_factorial_even_isEquivalent

-- Ch5 Fibonacci OGF 1/(1-z-z²) (F&S Ch V, the textbook first rational-coefficient asymptotic):
-- partial-fraction split into the two simple poles ρ=1/φ (dominant) and 1/(-φ) (remainder radius >1),
-- coeff = Nat.fib(n+1) from the recurrence, residue -1/√5 ⟹ UNCONDITIONAL Nat.fib(n+1) ~ φ^{n+1}/√5
-- via the banked dominant_simplePole_isEquivalent. Stated for the genuine Mathlib Nat.fib.
#print axioms AnalyticCombinatorics.Ch5.Meromorphic.FibonacciCompositionsNS.natFib_succ_isEquivalent_phi

-- Ch4/VI log-singularity coefficient scale (leading order, β=1): genuine [z^n](1-z)^{-α}log(1/(1-z))
-- = Ring.choose(α+n-1,n)·Σ_{j<n}(α+j)⁻¹ ~ (n^{α-1}/Γα)·log n (α>1). Full Δ-domain log-transfer + general β
-- reported-open (honestly, not faked). α=2 instance ~ n log n.
#print axioms _root_.logSingularityCoeff_isEquivalent
#print axioms _root_.doublePoleLogCoeff_isEquivalent

-- Ch8 4th Hayman instance: set partitions with all block sizes ≤ 3, EGF e^{z+z²/2+z³/6} (= SET of the
-- genuine parts123 atom class, counts (0,1,1,1,0,…)); saddle a(r)=r+r²+r³/2=n. Count asymptotic through
-- the general Hayman interface.
#print axioms _root_.Blocks3HAdmissible.blocks3HAdmissible
#print axioms _root_.Blocks3HAdmissible.blocks3_count_over_factorial_isEquivalent_saddle

-- Ch7 tree function / Cayley (F&S VII.4 implicit-function schema): genuine cayleyRootedTree n = n^{n-1}
-- (rooted labelled trees, T=z e^T, √-singularity at 1/e); n^{n-1}/n! ~ e^n/(√(2π)·n^{3/2}) via Stirling.
#print axioms AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS.treeFunctionCoeff_isEquivalent
#print axioms AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS.cayleyRootedTree_over_factorial_isEquivalent

-- Ch7 rooted-tree forests (F&S Ch VII): genuine rootedForest n = (n+1)^{n-1} (Cayley-Prüfer), tied to the
-- tree function by the shift rootedForestCoeff n = treeFunctionCoeff (n+1); (n+1)^{n-1}/n! ~ e^{n+1}/(√(2π)n^{3/2}).
#print axioms AnalyticCombinatorics.Ch7.SingularityApp.ForestsNS.rootedForest_over_factorial_isEquivalent

end AnalyticCombinatorics.Ch1
