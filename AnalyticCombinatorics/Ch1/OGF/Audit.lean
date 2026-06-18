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
import AnalyticCombinatorics.Ch2.Mappings.ForestCount
import AnalyticCombinatorics.Ch2.Mappings.ForestCountComplete
import AnalyticCombinatorics.Ch2.Mappings.CayleyFormula
import AnalyticCombinatorics.Ch2.Mappings.ConnectedMappings
import AnalyticCombinatorics.Ch2.Mappings.CyclicPoints
import AnalyticCombinatorics.Ch2.Mappings.MappingComponents
import AnalyticCombinatorics.Ch2.Mappings.MappingComponentsSharp
import AnalyticCombinatorics.Ch1.Lagrange.ImplicitSeries
import AnalyticCombinatorics.Ch1.Lagrange.Residue
import AnalyticCombinatorics.Ch1.Lagrange.Applications
import AnalyticCombinatorics.Ch1.Polya.Enumeration
import AnalyticCombinatorics.Ch1.Polya.NecklacePhi
import AnalyticCombinatorics.Ch1.Polya.Weighted
import AnalyticCombinatorics.Ch1.Polya.Bracelets
import AnalyticCombinatorics.Ch2.SetPartitions.BellMean
import AnalyticCombinatorics.Ch2.SetPartitions.BellVariance
import AnalyticCombinatorics.Ch5.ContinuedFractions.Flajolet
import AnalyticCombinatorics.Ch5.ContinuedFractions.FlajoletPathSum
import AnalyticCombinatorics.Ch8.Partitions.UpperBound
import AnalyticCombinatorics.Ch8.Partitions.LaplaceAsymptotic
import AnalyticCombinatorics.Ch8.Partitions.EulerProduct
import AnalyticCombinatorics.Ch8.Partitions.LaplaceLimit
import AnalyticCombinatorics.Ch8.Partitions.Tauberian
import AnalyticCombinatorics.Ch8.Partitions.TauberianFull
import AnalyticCombinatorics.Ch8.Partitions.TauberianAssembly
import AnalyticCombinatorics.Ch8.Partitions.LogAsymptotic
import AnalyticCombinatorics.Ch8.Partitions.DistinctParts
import AnalyticCombinatorics.Ch8.Partitions.OddParts
import AnalyticCombinatorics.Ch8.Partitions.GlaisherAsymptotic
import AnalyticCombinatorics.Ch8.Partitions.SigmaRecurrence
import AnalyticCombinatorics.Ch8.Partitions.SigmaSummatory
import AnalyticCombinatorics.Ch8.Partitions.ErdosKernel
import AnalyticCombinatorics.Ch8.Partitions.ErdosKernelClose
import AnalyticCombinatorics.Ch8.Partitions.SummatoryWindow
import AnalyticCombinatorics.Ch8.Partitions.ErdosIntegral
import AnalyticCombinatorics.Ch8.Partitions.ErdosUniform
import AnalyticCombinatorics.Ch8.Partitions.ErdosModel
import AnalyticCombinatorics.Ch8.Partitions.SummatoryBridge
import AnalyticCombinatorics.Ch8.Partitions.BlockSqueeze
import AnalyticCombinatorics.Ch8.Partitions.ModelAssembly
import AnalyticCombinatorics.Ch8.Partitions.MeshEstimate
import AnalyticCombinatorics.Ch8.Partitions.KernelWindow
import AnalyticCombinatorics.Ch8.Partitions.KernelTotal
import AnalyticCombinatorics.Ch8.Partitions.PartMono
import AnalyticCombinatorics.Ch8.Partitions.LocalLower
import AnalyticCombinatorics.Ch8.Partitions.KernelBarriers
import AnalyticCombinatorics.Ch8.Partitions.BarrierGap
import AnalyticCombinatorics.Ch8.Partitions.BarrierHarmonic
import AnalyticCombinatorics.Ch8.Partitions.BarrierInduction
import AnalyticCombinatorics.Ch8.Partitions.RecordBasics
import AnalyticCombinatorics.Ch8.Partitions.MassRateMoments
import AnalyticCombinatorics.Ch8.Partitions.MassRateExpansion
import AnalyticCombinatorics.Ch8.Partitions.MassRateTail
import AnalyticCombinatorics.Ch8.Partitions.MassRateCoef
import AnalyticCombinatorics.Ch8.Partitions.MassRateLambert
import AnalyticCombinatorics.Ch8.Partitions.MassRateGeom2
import AnalyticCombinatorics.Ch8.Partitions.MassRateExpBounds
import AnalyticCombinatorics.Ch8.Partitions.MassRateBose
import AnalyticCombinatorics.Ch8.Partitions.MassRateAntideriv
import AnalyticCombinatorics.Ch8.Partitions.MassRateIntegral
import AnalyticCombinatorics.Ch8.Partitions.MassRateDeriv
import AnalyticCombinatorics.Ch8.Partitions.MassRateDerivZero
import AnalyticCombinatorics.Ch8.Partitions.MassRateDerivInt
import AnalyticCombinatorics.Ch8.Partitions.MassRateGeom3
import AnalyticCombinatorics.Ch8.Partitions.MassRateBasel
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentOne
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentTwo
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentBound
import AnalyticCombinatorics.Ch8.Partitions.MassRateTailInvSq
import AnalyticCombinatorics.Ch8.Partitions.MassRateWeightedSum
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentOneAsymp
import AnalyticCombinatorics.Ch8.Partitions.MassRateReg3
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentTwoAsymp
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentSharp
import AnalyticCombinatorics.Ch8.Partitions.MassRateAssembly
import AnalyticCombinatorics.Ch8.Partitions.MassRateApprox2
import AnalyticCombinatorics.Ch8.Partitions.BarrierLimit
import AnalyticCombinatorics.Ch8.Partitions.RecordPullback
import AnalyticCombinatorics.Ch8.Partitions.DefectSummable
import AnalyticCombinatorics.Ch8.Partitions.RenewalSpine
import AnalyticCombinatorics.Ch8.Partitions.RenewalHitPot
import AnalyticCombinatorics.Ch8.Partitions.PartitionRenewal
import AnalyticCombinatorics.Ch8.Partitions.ErdosLimit
import AnalyticCombinatorics.Ch8.Partitions.DoeblinOverlap
import AnalyticCombinatorics.Ch8.Partitions.StepContraction
import AnalyticCombinatorics.Ch8.Partitions.KernelPow
import AnalyticCombinatorics.Ch8.Partitions.BlockContract
import AnalyticCombinatorics.Ch8.Partitions.CenterTracking
import AnalyticCombinatorics.Ch8.Partitions.StepSummable
import AnalyticCombinatorics.Ch8.Partitions.TailSup
import AnalyticCombinatorics.Ch8.Partitions.KilledKernelPow
import AnalyticCombinatorics.Ch8.Partitions.KilledHarmonic
import AnalyticCombinatorics.Ch8.Partitions.KilledStochastic
import AnalyticCombinatorics.Ch8.Partitions.TailOscConverge
import AnalyticCombinatorics.Ch8.Partitions.DoeblinEscape
import AnalyticCombinatorics.Ch8.Partitions.TailBand
import AnalyticCombinatorics.Ch8.Partitions.RenewalAssembly
import AnalyticCombinatorics.Ch8.Partitions.ErdosConcrete
import AnalyticCombinatorics.Ch8.Partitions.HitValBound
import AnalyticCombinatorics.Ch8.Partitions.ErdosRenewalConnect
import AnalyticCombinatorics.Ch8.Partitions.StepContractionConst
import AnalyticCombinatorics.Ch8.Partitions.RenewalMultiB
import AnalyticCombinatorics.Ch8.Partitions.ErdosRenewalConnectMultiB
import AnalyticCombinatorics.Ch8.Partitions.RenewalAlign
import AnalyticCombinatorics.Ch8.Partitions.ErdosAlignConnect
import AnalyticCombinatorics.Ch8.Partitions.ScalarRecSolve
import AnalyticCombinatorics.Ch8.Partitions.ITERCoupling
import AnalyticCombinatorics.Ch8.Partitions.CompContraction
import AnalyticCombinatorics.Ch8.Partitions.OverlapL1
import AnalyticCombinatorics.Ch8.Partitions.ErdosMinorization
import AnalyticCombinatorics.Ch8.Partitions.HarmonicOverlap
import AnalyticCombinatorics.Ch8.Partitions.ITEROccupation
import AnalyticCombinatorics.Ch8.Partitions.ITERGreen
import AnalyticCombinatorics.Ch8.Partitions.ITERGreenT
import AnalyticCombinatorics.Ch8.Partitions.ProbMoments
import AnalyticCombinatorics.Ch8.Partitions.TanakaStep
import AnalyticCombinatorics.Ch8.Partitions.TanakaTelescope
import AnalyticCombinatorics.Ch8.Partitions.QVTelescope
import AnalyticCombinatorics.Ch8.Partitions.FourthMoment
import AnalyticCombinatorics.Ch8.Partitions.MomentBounds
import AnalyticCombinatorics.Ch8.Partitions.OccupationAssembly
import AnalyticCombinatorics.Ch8.Partitions.OccupationFinal
import AnalyticCombinatorics.Ch8.Partitions.TanakaEta
import AnalyticCombinatorics.Ch8.Partitions.QVEta
import AnalyticCombinatorics.Ch8.Partitions.OccupationEta
import AnalyticCombinatorics.Ch8.Partitions.CoalesceBridge
import AnalyticCombinatorics.Ch8.Partitions.SmoothScale
import AnalyticCombinatorics.Ch8.Partitions.EnergyBridge
import AnalyticCombinatorics.Ch8.Partitions.UmassZero
import AnalyticCombinatorics.Ch8.Partitions.LocalizedQV
import AnalyticCombinatorics.Ch8.Partitions.LocalizedTanaka
import AnalyticCombinatorics.Ch8.Partitions.LocalizedOccupation
import AnalyticCombinatorics.Ch8.Partitions.GoodHiRecursion
import AnalyticCombinatorics.Ch8.Partitions.TwoTermLocalLip
import AnalyticCombinatorics.Ch8.Partitions.MassRateRiemann
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
import AnalyticCombinatorics.Ch4.Analytic.ModelCoeffExplicit
import AnalyticCombinatorics.Ch4.Analytic.ModelCoeffSecondOrder
import AnalyticCombinatorics.Ch4.Analytic.TransferSecondOrder
import AnalyticCombinatorics.Ch4.Analytic.TransferSecondOrderAlphaLt1
import AnalyticCombinatorics.Ch4.Analytic.TransferSecondOrderGeneral
import AnalyticCombinatorics.Ch7.SingularityApp.TwoRegularSecondOrder
import AnalyticCombinatorics.Ch8.SaddlePoint.FragmentedPermHAdmissible
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
import AnalyticCombinatorics.Ch5.Meromorphic.CompositionsGeneral
import AnalyticCombinatorics.Ch5.Meromorphic.CompositionsGeneralClose
import AnalyticCombinatorics.Ch7.SingularityApp.TernaryTrees
import AnalyticCombinatorics.Ch7.SingularityApp.Motzkin
import AnalyticCombinatorics.Ch7.SingularityApp.FussCatalan
import AnalyticCombinatorics.Ch7.SingularityApp.TwoRegular
import AnalyticCombinatorics.Ch7.SingularityApp.FussCatalanInstances
import AnalyticCombinatorics.Ch7.SingularityApp.TwoRegularClass
import AnalyticCombinatorics.Ch7.SingularityApp.CycleMarkedPermPairs
import AnalyticCombinatorics.Ch7.SingularityApp.UndirectedCycleMarkedPermPairs
import AnalyticCombinatorics.Ch7.SingularityApp.CycleMarkedPermTuple
import AnalyticCombinatorics.Ch7.SingularityApp.UndirectedCycleMarkedPermTuple
import AnalyticCombinatorics.Ch7.SingularityApp.UndirectedCycleLogSqPermPair
import AnalyticCombinatorics.Ch7.SingularityApp.UndirectedCycleLogKPermLpow
import AnalyticCombinatorics.Ch5.Meromorphic.LabelledCycleCount
import AnalyticCombinatorics.Ch4.Analytic.LogTransferNatural
import AnalyticCombinatorics.Ch4.Analytic.OneSubCpowMul
import AnalyticCombinatorics.Ch4.Analytic.LogSqTransfer
import AnalyticCombinatorics.Ch4.Analytic.LogKCoeff
import AnalyticCombinatorics.Ch4.Analytic.LogKFaithful
import AnalyticCombinatorics.Ch4.Analytic.LogKAsymp
import AnalyticCombinatorics.Ch4.Analytic.LogKTransferNatural
import AnalyticCombinatorics.Ch4.Analytic.LogAlphaOneTransfer
import AnalyticCombinatorics.Ch7.SingularityApp.CycleMarkedPermHarmonic
import AnalyticCombinatorics.Ch7.SingularityApp.CycleMarkedPermLpow
import AnalyticCombinatorics.Ch4.Analytic.LogSqTransferNatural
import AnalyticCombinatorics.Ch7.SingularityApp.CycleMarkedPermPairBoth
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

-- EXPLICIT model-coefficient constant (1+O(1/n)) for [zⁿ](1-z)^{-α} via the exact Γ-ratio
-- [zⁿ](1-z)^{-α} = Γ(n+α)/(Γ(α)Γ(n+1)) + a Bohr–Mollerup log-convexity first-order Γ-ratio estimate
-- (no Hankel contour). Foundation for quantitative/second-order singularity analysis.
#print axioms _root_.gamma_ratio_first_order
#print axioms _root_.modelCoeff_explicit

-- A3 SECOND-ORDER (explicit subdominant term, c₁ = α(α-1)/2): the exact second-order Γ-ratio
-- Γ(n+α)/Γ(n+1) = n^{α-1}(1 + α(α-1)/(2n) + O(1/n²)) via recurrence-bootstrap from A1 (no Stirling),
-- and the two-term singularity transfer (the leading C₀ term itself contributes to the n^{α-2} coeff).
#print axioms _root_.gamma_ratio_second_order
#print axioms _root_.modelCoeff_secondOrder
#print axioms _root_.transfer_twoTerm_secondOrder

-- α<1 second-order transfer (derivative-descent reusing the α>1 transfer at β=α+1) + its capstone
-- application: the 2-regular labelled graph count to second order, aₙ/n! ~ e^{-3/4}/√(πn)·(1 - 5/(8n)).
#print axioms _root_.transfer_twoTerm_secondOrder_alpha_lt_one
#print axioms TwoRegularClass.twoRegularClass_counts_div_factorial_secondOrder

-- GENERAL-α second-order two-term transfer (all real α avoiding 1-ℕ poles), by k-fold derivative
-- descent — subsumes the α>1 and 0<α<1 versions and extends to α<0 (e.g. Motzkin/Catalan α=-1/2).
#print axioms _root_.transfer_twoTerm_secondOrder_general

-- FIRST FINITE-RADIUS H-admissible saddle-point instance: fragmented permutations exp(z/(1-z)),
-- ρ=1, saddle r→1⁻. Full Hayman local+tail estimates (finite-radius regime) ⇒ aₙ/n! saddle asymptotic.
#print axioms FragmentedPermHAdmissible.fragPerm_coeff_isEquivalent_saddle_from_HAdmissible

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

-- Ch2 generalized-Cayley forest count, PARTIAL: genuine functional formulation (absorbing step / Reaches /
-- RootedForests subtype) with base cases (k=n → 1; k+1=n → k·n^0) and the ABEL-BINOMIAL ENGINE
-- Σ_i C(m-1,i)·k^{i+1}·m^{m-1-i} = k·(m+k)^{m-1} (exactly what the depth-one decomposition needs to yield
-- k·n^{n-k-1}). The sigma-bijection (partition by first-generation children) is dispatched follow-up work;
-- the full formula is NOT yet claimed.
#print axioms AnalyticCombinatorics.Ch2.Mappings.ForestCountNS.abel_forest_reindexed_identity
#print axioms AnalyticCombinatorics.Ch2.Mappings.ForestCountNS.card_rootedForests_one_nonRoot_formula

-- Ch2 GENERALIZED CAYLEY FORMULA, COMPLETE (classic; not in Mathlib): the number of forests of k rooted
-- trees on n labeled vertices with a SPECIFIED root set (functional formulation: parent maps where every
-- vertex reaches R) equals k·n^{n-k-1} (0<k<n) — proved by strong induction over an arbitrary Fintype
-- carrier via fixed-S fiber equivalences (depth-one decomposition, no HEq needed) + the Abel-binomial
-- engine. Foundation of the random-mappings arc (c_n = n^{n-1}·Q(n) next).
#print axioms AnalyticCombinatorics.Ch2.Mappings.ForestCountNS.Complete.card_gRootedForests
#print axioms AnalyticCombinatorics.Ch2.Mappings.ForestCountNS.Complete.card_rootedForests

-- Ch2 Cayley's formula, arborescence form (named instantiation corollary, k=1 of the above):
-- parent maps toward a fixed root = n^{n-2}.
#print axioms AnalyticCombinatorics.Ch2.Mappings.ForestCountNS.card_rootedForests_singleton

-- Ch2 CONNECTED RANDOM MAPPINGS, COMPLETE ARC (F&S II.3/VIII — flagship): genuine iteration connectivity
-- (∀ x y, ∃ i j, f^[i] x = f^[j] y); periodic-core classification (core perm is a single cycle ⟺ connected,
-- fixed-core fiber ≃ rooted forests); global fiber sum ⟹ exact count c_n = Σ_k (n-1)_{k-1}·n^{n-k};
-- the EXACT identity c_n = n^{n-1}·Q(n) (Ramanujan Q); and with Q ~ √(πn/2):
-- P(a uniform random mapping on [n] is connected) ~ √(π/(2n)) — UNCONDITIONAL, end-to-end.
#print axioms AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS.card_connectedMappings
#print axioms AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS.card_connectedMappings_eq_q
#print axioms AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS.connectedProbability_isEquivalent

-- Ch2 expected number of CYCLIC points of a uniform random mapping (Knuth/F&S): per-point first-return
-- fiber count #{f : x₀ periodic} = Σ_k (n-1)_{k-1}·n^{n-k} (= the connected count!), double count ⟹
-- E[#cyclic] = Q(n) EXACTLY, hence ~ √(πn/2). Third Q-tied mapping statistic, end-to-end.
#print axioms AnalyticCombinatorics.Ch2.Mappings.CyclicPointsNS.card_periodicAt
#print axioms AnalyticCombinatorics.Ch2.Mappings.CyclicPointsNS.expected_cyclicPoints_eq_q
#print axioms AnalyticCombinatorics.Ch2.Mappings.CyclicPointsNS.expected_cyclicPoints_isEquivalent

-- Ch2 expected number of COMPONENTS of a uniform random mapping (F&S II.3/VII): EXACT formula
-- E[#components] = Σ_{k∈Icc 1 n} (n)_k/(k·n^k) via candidate-cycle linearity (component ⟺ core cycle;
-- f|_C = σ_C forced, rest free). PARTIAL asymptotic, honest: harmonic sandwich H(√n)/2 ≤ E ≤ H(n) (log
-- order pinned; the sharp ~½log n Gaussian-damped harmonic transfer is flagged remaining work, NOT claimed).
#print axioms AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS.expected_components_eq
#print axioms AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS.componentExpectationFormula_le_harmonic
#print axioms AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS.half_harmonic_sqrt_le_componentExpectationFormula

-- Ch2 SHARP components asymptotic (upgrade of the sandwich): E[#components of a uniform random mapping]
-- ~ (1/2)·log n UNCONDITIONAL — Gaussian-damped harmonic sum, L-windowed two-sided estimates (head
-- ∏(1-aⱼ)≥1-Σaⱼ envelope, tail 1/x ≤ x/(nL) trick). Completes the sharp random-mapping statistics suite:
-- P(connected)~√(π/2n), E[#cyclic]=Q(n)~√(πn/2), E[#components]~½log n.
#print axioms AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS.Sharp.componentExpectationFormula_isEquivalent
#print axioms AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS.Sharp.expected_components_isEquivalent

-- Ch1 Lagrange-inversion campaign, layer 1 (framework infra; full inversion is the documented frontier —
-- blocked precisely on formal residue infrastructure, LAG2 dispatched): the IMPLICIT SERIES T = X·φ(T) —
-- existence (coefficient recursion), uniqueness, constant term 0, the derivative identity — over any
-- CommRing; sanity φ=1+X ⟹ T = X/(1-X) with all positive coefficients 1.
#print axioms AnalyticCombinatorics.Ch1.Lagrange.ImplicitSeries.implicitSeries_spec
#print axioms AnalyticCombinatorics.Ch1.Lagrange.ImplicitSeries.implicitSeries_unique
#print axioms AnalyticCombinatorics.Ch1.Lagrange.ImplicitSeries.derivative_implicitSeries

-- Ch1 LAGRANGE INVERSION (F&S A.6 — famous Mathlib gap, CLOSED): over any ℚ-algebra R, for φ with unit
-- constant term and T = implicitSeries φ (the unique T = X·φ(T)): n·[Xⁿ]T = [X^{n-1}]φⁿ (+ divided form).
-- Proved via a self-built mini formal-residue calculus on the lightweight X^{-N}·F representation:
-- residue-of-derivative = 0, unit-kernel residues (the res(G'/G)=1 core), and the change-of-variables
-- theorem residue_subst_unit (Stanley EC2 Thm 5.4.2 route). Catalan sanity verified.
#print axioms AnalyticCombinatorics.Ch1.Lagrange.Residue.residue_subst_unit
#print axioms AnalyticCombinatorics.Ch1.Lagrange.Residue.lagrange_inversion
#print axioms AnalyticCombinatorics.Ch1.Lagrange.Residue.lagrange_inversion_divided

-- Ch1 Lagrange applications: the binary-tree equation T = X(1+T)² has Catalan coefficients (Mathlib's
-- catalan, via the choose identity n·catalan n = C(2n,n-1)); and Cayley VIA LAGRANGE — T = X·e^T has
-- coefficients n^{n-1}/n! (independent algebraic proof, cross-validating the analytic TreeFunctionNS route).
#print axioms AnalyticCombinatorics.Ch1.Lagrange.Applications.coeff_implicitSeries_one_add_X_sq
#print axioms AnalyticCombinatorics.Ch1.Lagrange.Applications.coeff_implicitSeries_exp

-- Ch1 PÓLYA ENUMERATION (unweighted; famous gap — Mathlib has only Burnside) + NECKLACES (F&S Ch I):
-- colorings fixed by g ≃ (orbits of ⟨g⟩ → C) ⟹ |C|^{#cycles(g)}; combined with Mathlib's Burnside:
-- #orbits(G on D→C)·|G| = Σ_g |C|^{#orbits ⟨g⟩}; and the binary necklace count
-- #necklaces(n)·n = Σ_{k∈ZMod n} 2^{gcd(n,k)} (rotation orbits = gcd; φ-form deferred, flagged).
#print axioms AnalyticCombinatorics.Ch1.Polya.card_fixedBy_colorings
#print axioms AnalyticCombinatorics.Ch1.Polya.polya_card_orbits_mul_card_group
#print axioms AnalyticCombinatorics.Ch1.Polya.card_binary_necklaces

-- Ch1 necklace φ-form (classical): #necklaces(n)·n = Σ_{d|n} φ(d)·2^{n/d}, via the reusable gcd-fiber
-- regrouping Σ_{a∈ZMod n} F(gcd(n,a)) = Σ_{d|n} φ(n/d)·F(d).
#print axioms AnalyticCombinatorics.Ch1.Polya.NecklacePhi.sum_zmod_by_gcd
#print axioms AnalyticCombinatorics.Ch1.Polya.NecklacePhi.card_binary_necklaces_phi_standard

-- Ch1 WEIGHTED PÓLYA (the cycle-index theorem, F&S Ch I appendix — famous): |G|·Σ_orbits W(O) =
-- Σ_g ∏_{cycles σ of g} (Σ_c w(c)^{|σ|}). Multiplicative fixed-coloring sum (product over cycles of
-- power-sums) + weighted Burnside (orbit-stabilizer double count, Quotient.lift weights). w≡1 recovers
-- the unweighted PET.
#print axioms AnalyticCombinatorics.Ch1.Polya.Weighted.sum_weight_fixedBy
#print axioms AnalyticCombinatorics.Ch1.Polya.Weighted.weighted_burnside
#print axioms AnalyticCombinatorics.Ch1.Polya.Weighted.weighted_polya

-- Ch1 BRACELETS (dihedral PET application, F&S Ch I): full DihedralGroup action on ZMod n + reflection
-- fixed-point/orbit counts (odd: (n+1)/2; even: n/2+1 / n/2 split) ⟹ the classical bracelet formula
-- #bracelets·2n = Σ_k 2^{gcd(n,k)} + (n odd: n·2^{(n+1)/2}; n even: (n/2)·2^{n/2+1} + (n/2)·2^{n/2}),
-- all n>0 (degenerate small-n covered).
#print axioms AnalyticCombinatorics.Ch1.Polya.Bracelets.card_reflection_zpowers_orbitQuotient_mul_two
#print axioms AnalyticCombinatorics.Ch1.Polya.Bracelets.card_binary_bracelets

-- Ch2 BELL NUMBERS as genuine partition counts (Mathlib gap: only multiset-shaped bell existed) + the
-- Bell recurrence B_{n+1} = Σ C(n,k)B_{n-k} (root-block fiber bijection) + the classic first-moment
-- identity Σ_P #blocks = B_{n+1} − B_n ⟹ E[#blocks of a uniform set partition] = B_{n+1}/B_n − 1.
-- First exact step toward the Bell block-count CLT frontier.
#print axioms AnalyticCombinatorics.Ch2.SetPartitions.bellNumber_succ
#print axioms AnalyticCombinatorics.Ch2.SetPartitions.bellNumber_succ_eq_sum_parts_add
#print axioms AnalyticCombinatorics.Ch2.SetPartitions.expected_blocks_eq

-- Ch2 second moment + variance of the block count (Bell frontier, exact layer complete): the weighted
-- add-element fiber identity ⟹ B_{n+2} = Σ_P #p² + 2Σ_P #p + 2B_n (sanity n=1: 5=1+2+2 ✓) ⟹ the exact
-- rational variance of #blocks of a uniform random set partition in Bell-ratio form.
#print axioms AnalyticCombinatorics.Ch2.SetPartitions.BellVariance.sum_parts_succ
#print axioms AnalyticCombinatorics.Ch2.SetPartitions.BellVariance.bellNumber_add_two_eq
#print axioms AnalyticCombinatorics.Ch2.SetPartitions.BellVariance.variance_blocks_eq

-- Ch5 FLAJOLET CONTINUED-FRACTION THEOREM, COMPLETE (F&S V.4, Flajolet 1980 — famous): the first-return
-- recursion unfolds to the finite J-fraction (flajolet_cf: W h = JFraction h), AND the path-sum bridge is
-- PROVED (FCF2): coeff_JFraction_eq_pathSum — the J-fraction coefficients equal the LITERAL Finset sums of
-- weighted Motzkin-path weights at height ≤ h. Fully combinatorial, end-to-end.
#print axioms AnalyticCombinatorics.Ch5.ContinuedFractions.W_first_return_series
#print axioms AnalyticCombinatorics.Ch5.ContinuedFractions.flajolet_cf
#print axioms AnalyticCombinatorics.Ch5.ContinuedFractions.PathSum.WpathSum_eq_Wcoeff
#print axioms AnalyticCombinatorics.Ch5.ContinuedFractions.PathSum.coeff_JFraction_eq_pathSum

-- Ch8 PARTITION CAMPAIGN Milestone A (route: HANDOFF/partition-campaign-route-R1.md): the sharp elementary
-- upper bound p(n) ≤ e^{π√(2n/3)} for the GENUINE part n = card (Nat.Partition n) — GF inequality
-- p(n)xⁿ ≤ ∏(1-x^k)⁻¹, log-bound A·x/(1-x) via 1-x^k ≥ (1-x)kx^{k-1} + Basel, optimal x. Toward the
-- log-asymptotic log p(n) ~ π√(2n/3) (Milestones B–D: Laplace asymptotic, log-Tauberian, transfer).
#print axioms AnalyticCombinatorics.Ch8.Partitions.partition_log_upper
#print axioms AnalyticCombinatorics.Ch8.Partitions.partition_upper_exp

-- Ch8 partition Milestone B, PARTIAL (honest): PartLaplace summability + the ANALYTIC half — the Euler
-- log-series Laplace limit t·Σ_j 1/(j(e^{tj}−1)) → π²/6 (termwise + domination + Basel over ℕ+).
-- BLOCKED (precise, PARTB2 dispatched): the real Euler product bridge PartLaplace = ∏'(1−e^{−tk})⁻¹
-- (K-sandwich route). The PartLaplace limit itself is NOT yet claimed.
#print axioms AnalyticCombinatorics.Ch8.Partitions.partLaplace_summable
#print axioms AnalyticCombinatorics.Ch8.Partitions.partition_laplace_series_asymptotic

-- Ch8 partition EULER PRODUCT bridge (PARTB2): genuine bounded-partition ↔ multiplicity equivalence;
-- finite Euler product ∏_{k≤K}(1−x^k)⁻¹ = Σ' partsLE K n·xⁿ (ENNReal nonneg regrouping); and the
-- K-SANDWICH: finite products → PartLaplace (tendsto). Remaining for Milestone B: log + tsum_comm
-- regrouping (PARTB3 dispatched).
#print axioms AnalyticCombinatorics.Ch8.Partitions.finite_euler_prod_eq
#print axioms AnalyticCombinatorics.Ch8.Partitions.partLaplace_eq_finprod_tendsto

-- Ch8 partition MILESTONE B COMPLETE: log PartLaplace = Σ' −log(1−e^{−tk}) (log of the K-sandwich limit),
-- the double-series regrouping, and THE LAPLACE ASYMPTOTIC t·log P(e^{−t}) → π²/6 — UNCONDITIONAL, for the
-- genuine partition counts. (Milestone C: the reusable log-Tauberian; D: monotone transfer.)
#print axioms AnalyticCombinatorics.Ch8.Partitions.log_partLaplace_eq
#print axioms AnalyticCombinatorics.Ch8.Partitions.partition_laplace_log_asymptotic

-- Ch8 Tauberian infrastructure, PARTIAL (Milestone C in progress): Abel summation F = (1−e^{−t})ΣCum·e^{−tN};
-- the inside-window gap (B = 2√K−ε full sum ≤ e^{(K−ρ)/t}); the full-sum gap for any B < 2√K; the limsup
-- core inequality. BLOCKED precisely (PARTC2): the STRONG restricted gap (B = 2√K+η outside the saddle
-- window) ⟹ localization ⟹ liminf ⟹ the full log-Tauberian. NOT yet claimed.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Tauberian.laplace_eq_abel_cum
#print axioms AnalyticCombinatorics.Ch8.Partitions.Tauberian.sqrt_laplace_bad_inside_gap
#print axioms AnalyticCombinatorics.Ch8.Partitions.Tauberian.sqrt_laplace_full_gap

-- Ch8 Tauberian STRONG restricted gap (PARTC2 — the route-critical estimate): for B = 2√K+η outside the
-- δ-saddle-window, (Σ' off-window exp(B√N−tN)) ≤ e^{(K−ρ)/t} — unimodal-boundary algebra (2√c−c = 1−(√c−1)²)
-- + concavity-of-√ tail decay + poly/geometric absorption. Assembly (localization/limsup/liminf/full
-- theorem) = PARTC3, in flight.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Tauberian.sqrt_laplace_restricted_gap_strong

-- Ch8 THE LOGARITHMIC TAUBERIAN THEOREM, COMPLETE (Milestone C — the campaign's central reusable asset):
-- for nonneg a with t·log(Σa_n e^{−tn}) → K: log(Σ_{n≤N} a_n)/√N → 2√K. Full assembly: limsup (Chernoff
-- t-choice), global eventual bound, Abel localization at the saddle window (contradiction via the strong +
-- inside gaps), liminf diagonalization. Reusable across analytic combinatorics.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Tauberian.tauberian_exists_large_cum_near_saddle
#print axioms AnalyticCombinatorics.Ch8.Partitions.Tauberian.log_tauberian_cumulative_sqrt

-- Ch8 ★ THE HARDY–RAMANUJAN LOG-ASYMPTOTIC (campaign FINALE, F&S VIII / the named hard frontier):
-- log p(n)/√n → π√(2/3), equivalently log p(n) ~ π√(2n/3), for the GENUINE p(n) = card (Nat.Partition n) —
-- fully elementary end-to-end: GF upper bound → Euler product (K-sandwich) → Laplace asymptotic
-- t·log P(e^{−t}) → π²/6 → the reusable LOG-TAUBERIAN → monotone transfer. No circle method, no modular
-- forms. (The sharp polynomial factor e^{...}/(4n√3) remains the true circle-method frontier.)
#print axioms AnalyticCombinatorics.Ch8.Partitions.partition_cum_log_asymptotic
#print axioms AnalyticCombinatorics.Ch8.Partitions.partition_log_asymptotic
#print axioms AnalyticCombinatorics.Ch8.Partitions.partition_log_isEquivalent

-- Ch8 DISTINCT-PARTS partitions (Erdős): log q(n)/√n → π√(1/3), q(n) = genuine card of Nodup partitions —
-- full pipeline REUSE (∏(1+x^k) via log(1+y) = log(1−y²)−log(1−y) reduction to the banked nonneg machinery
-- at t and 2t ⟹ K = π²/12; the same log-Tauberian; largest-part monotonicity). The Tauberian's first reuse.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Distinct.distinct_log_asymptotic
#print axioms AnalyticCombinatorics.Ch8.Partitions.Distinct.distinct_log_isEquivalent

-- Ch8 ODD-PARTS partitions (Opus-authored): via Mathlib's Euler partition theorem
-- (card_odds_eq_card_distincts), the genuine odd-parts count has the SAME asymptotic:
-- log o(n)/√n → π√(1/3).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Odd.opart_eq_qpart
#print axioms AnalyticCombinatorics.Ch8.Partitions.Odd.odd_log_asymptotic

-- Ch8 GLAISHER-m FAMILY (generalizes Erdős m=2): for every m ≥ 2, the genuine count of partitions with no
-- part divisible by m satisfies log r_m(n)/√n → π√(2(1−1/m)/3) — Euler-product split ∏_{m∤k} = ∏_all/∏_{m|k}
-- reduces to the banked Laplace limits at t and mt (K_m = (1−1/m)π²/6); the same log-Tauberian; add-a-1
-- monotonicity. m=2 cross-checked against the odd-parts count.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Glaisher.glaisher_log_asymptotic
#print axioms AnalyticCombinatorics.Ch8.Partitions.Glaisher.rpart_two_eq_opart

-- Ch8 HR-CONSTANT campaign Stage I.1 (route: HANDOFF/partition-HR-constant-route-R2.md): the classical
-- σ-RECURRENCE n·p(n) = Σ_{m≤n} σ₁(m)·p(n−m) — part-occurrence double count via the add-k-copies bijection,
-- genuine Mathlib ArithmeticFunction.sigma. Foundation of the Erdős route to p(n) ~ e^{π√(2n/3)}/(4n√3).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Sigma.partition_sigma_recurrence

-- Ch8 HR-CONSTANT Stage I.2: the divisor summatory Σ_{m≤x}σ₁(m) = π²x²/12 + O(x log x) with EXPLICIT
-- constant K = 8+π² (triangular hyperbola identity + Basel tail + harmonic absorption + floor lift).
-- Reusable elementary number theory.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Sigma.sigma_summatory_asymptotic

-- Ch8 HR-CONSTANT Stage I.3 layer 1: the NORMALIZED ERDŐS RECURRENCE u(n) = Σ erdosWeight(n,m)·u(n−m) +
-- boundary, with boundary → 0 (u = n·p(n)·e^{−C√n}). Kernel tail/window/total = PARTE4 (block decomposition
-- + Abel against the summatory), in flight.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.u_recurrence
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.boundaryTerm_negligible

-- Ch8 HR Stage I.3: KERNEL TAIL TIGHTNESS — ∀ε ∃R: the erdosWeight mass beyond R√n is eventually ≤ ε
-- (block decomposition by ⌊m/√n⌋ + per-block quadratic summatory bounds + the m>n/2 exponential kill).
-- Window limit + total mass = PARTE5 (sub-block summatory differences), in flight.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.Close.erdos_kernel_tail

-- Ch8 HR Stage I.3 infra (Opus-authored during the codex weekly-quota outage): the summatory WINDOW
-- DIFFERENCE S(β√n) − S(α√n) = (π²/12)n(β²−α²) + O((α+β)√n·log(2β√n)) — the estimate the kernel window
-- limit consumes, pure triangle algebra from the banked summatory.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Sigma.summatory_window_diff

-- Ch8 HR Stage I.3 infra (Opus): the kernel density integral — ∫₀^∞ t·e^{−rt} dt = 1/r² (via Mathlib's
-- scaled Gamma) and the normalization (π²/6)·∫₀^∞ y·e^{−(C/2)y} dy = 1 (C² = 4A). The closed form the
-- kernel total-mass theorem consumes.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.integral_id_mul_exp_neg_mul_Ioi
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.kernel_density_integral_one

-- Ch8 HR Stage I.3 infra (Opus): the UNIFORM WINDOW REPLACEMENTS — the exact rationalization
-- √n−√(n−m) = m/(√n+√(n−m)); |(√n−√(n−m)) − m/(2√n)| ≤ b²/(2√n) on m ≤ b√n; and
-- |1/(n−m) − 1/n| ≤ 2b/n^{3/2} (2m ≤ n). The erdosWeight → model-kernel conversion estimates.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.sqrt_diff_eq
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.sqrt_diff_window_approx
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.inv_window_approx

-- Ch8 HR Stage I.3 (ChatGPT-draft + Opus-fix loop, 11 rounds): the HALF-OPEN WINDOW MASS LIMIT —
-- (S(β√n)−S(α√n))/n → (π²/12)(β²−α²) (halfOpenMass_tendsto, with the α=0 first-window case), plus the
-- endpoint exponential squeeze on blocks. The model-kernel window limit's remaining piece: the
-- summatory↔windowed-sum index bridge + step assembly (next).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.Model.summatory_zero_to_beta_scaled_tendsto
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.Model.halfOpenMass_tendsto
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.Model.model_exp_endpoint_squeeze

-- Ch8 HR Stage I.3 (Opus): the SUMMATORY ↔ WINDOWED-SUM INDEX BRIDGE — S(β√n) − S(α√n) =
-- Σ_{m∈Icc 1 (n−1)} [α√n < m ≤ β√n]·σ(m) (⌊β√n⌋ ≤ n−1), the floor/filter/Ioc-telescope identity the
-- draft hand-waved. Closes the gap between half-open masses and the model-kernel windowed sums.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Sigma.window_filter_eq_Ioc
#print axioms AnalyticCombinatorics.Ch8.Partitions.Sigma.summatory_diff_eq_window_sum

-- Ch8 HR Stage I.3 (Opus): the WEIGHTED BLOCK SQUEEZE — eventually,
-- e^{−(C/2)β}·M_n(α,β) ≤ (1/n)·Σ_window σ(m)e^{−(C/2)m/√n} ≤ e^{−(C/2)α}·M_n(α,β), both sides on the
-- SAME index set via the bridge. Combined with halfOpenMass_tendsto this yields the model-kernel window
-- limit (step assembly next).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.Model.floor_beta_sqrt_le_eventually
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.Model.weighted_window_block_squeeze

-- Ch8 HR Stage I.3 (ChatGPT-draft + Opus-fix): MESH ASSEMBLY -- the half-open block (a√n,b√n] partitions
-- into N uniform mesh blocks (blockSum_add/blockSum_arith_partition), each squeezed by endpoint
-- exponentials x its half-open mass; as n -> oo the mesh sums converge to the Stieltjes endpoint sums, so
-- eventually lowerMesh - eps <= blockSum n <= upperMesh + eps for any fixed mesh.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.Model.blockSum_eventually_between_mesh_eps

-- Ch8 HR Stage I.3 (Opus): the MESH ESTIMATE -- the draft's lone axiom, now PROVED: per-block sandwich
-- by exp monotonicity, upper-lower gap <= C*Q*b*(b-a)*h via the Lipschitz bound e^{-u}-e^{-v} <= v-u;
-- then N large finishes.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.Model.mesh_endpoint_sums_approx_integral

-- Ch8 HR Stage I.3 * THE MODEL-KERNEL WINDOW LIMIT (step assembly complete, NO axioms):
-- (1/n)*Sum_{(a sqrt n, b sqrt n]} sigma(m)*e^{-(C/2)m/sqrt n} -> int_a^b (pi^2/6)*y*e^{-(C/2)y} dy.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.Model.model_kernel_window

-- Ch8 HR Stage I.3 (Opus, solo while ChatGPT capture down): the TRUE-KERNEL WINDOW LIMIT --
-- Sum_{(a sqrt n, b sqrt n]} erdosWeight n m -> int_a^b (pi^2/6) y e^{-(C/2)y} dy.  Model-to-true
-- conversion via the banked uniform replacements; per-term error sigma(m)*(2b+Cb^2/2)/n^{3/2},
-- summed against the quadratic divisor mass B b^2 n => O(1/sqrt n).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.Model.erdos_kernel_window

-- Ch8 HR Stage I.3 CAPSTONE: the ERDOS KERNEL TOTAL MASS -- Sum_{m=1}^{n-1} erdosWeight n m -> 1.
-- window(0,R) + tail(R) sandwich + int_0^R -> int_0^infty = 1 (ExpDecay integrability +
-- intervalIntegral_tendsto_integral_Ioi + kernel_density_integral_one).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.Model.erdos_kernel_total

-- Ch8 HR Stage I.5 prerequisite (Opus): partition function monotonicity p(n) <= p(n+1),
-- by the injection Partition n -> Partition (n+1) adding a part 1.
#print axioms AnalyticCombinatorics.Ch8.Partitions.part_mono

-- Ch8 HR Stage I.6 (Opus): FORWARD PROPAGATION -- u(n+r) >= ((n+r)/n)*e^{-C(sqrt(n+r)-sqrt n)}*u(n),
-- from part monotonicity; the only place p-monotonicity is essential (R6 route, lemma 14).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.u_local_lower_from_monotone

-- Ch8 HR Stage I.5 (Opus): BARRIER-PACKAGE FOUNDATIONS (R6 route lemmas 2,3,7; route audited,
-- renewal lemma 20 refuted by sin(sqrt j) counterexample -- see HANDOFF/partition-stage-I56-route-R6).
-- kernelMass/kernelWindow/upperBarrier/lowerBarrier/barrierSlack defs; positive fixed window
-- (window (1,2] mass >= I/2 > 0 eventually); barrier range bounds; boundary <= delta*slack eventually
-- (via n^5 e^{-C sqrt n} -> 0).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.erdos_kernel_fixed_window_pos
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.upperBarrier_eventually_pos_bdd
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.lowerBarrier_eventually_pos_bdd
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.boundaryTerm_le_barrierSlack

-- Ch8 HR Stage I.5 (Opus): BARRIER GAP ON THE WINDOW (R6 lemma 4, both forms) -- on a0*sqrt n < m
-- <= b0*sqrt n the barrier moves by >= (A*a0/2)*barrierSlack: log(n+E)-log(n-m+E) >= m/(n+E)
-- (log r <= r-1), denominator <= log^2(n+E).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.upperBarrier_gap_on_window
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.lowerBarrier_gap_on_window

-- Ch8 HR Stage I.5 (Opus): SUPER/SUBHARMONIC BARRIERS, CONDITIONAL on the o(slack) mass rate
-- (hypothesis-parameterized, NO axioms: the rate enters as an explicit hypothesis; it is the one
-- remaining analytic brick -- second-order cancellation, see HANDOFF/partition-stage-I5-design.md).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.upperBarrier_kernel_superharmonic_of_rate
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.lowerBarrier_kernel_subharmonic_of_rate
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.upperBarrier_mono
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.lowerBarrier_anti

-- Ch8 HR Stage I.5 (Opus): BOUNDEDNESS INDUCTIONS (R6 lemmas 8-12), CONDITIONAL on the harmonic
-- inequalities (strong induction on u_recurrence; base segment via sup'/inf'; boundary absorbed).
-- u_pos, u_zero unconditional.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.u_pos
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.u_upper_of_superharmonic
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.u_limsup_finite_of_superharmonic
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.u_lower_of_subharmonic
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.u_liminf_positive_of_subharmonic

-- Ch8 HR Stage I.6 (Opus): RECORD BASICS + CONVERGENCE ASSEMBLY (R7 route, kernel-free layers).
-- Records exist on finite intervals (with interval-wide extremality); threshold-monotone record
-- covers => CauchySeq => limit exists (and positive given the liminf bound); local monotone
-- forward fill u n - eps <= u(n+r) for r <= h*sqrt n. Remaining: record pullback/percolation
-- (kernel-dependent; needs the mass-rate brick).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.exists_highRecordFrom
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.exists_lowRecordFrom
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.u_tendsto_of_record_covers
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.erdos_limit_pos_of_tendsto
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.u_local_high_forward_fill

-- Ch8 HR MASS-RATE CAMPAIGN opening (R8 route, Opus): Lambert moments sigmaMoment, saddle
-- massLam = C/2 with massLam^2 = pi^2/6, Bose kernel + regularization + exp-form identity, and the
-- CENTRAL CANCELLATION -1/(2L) + 2Z/L^3 - (C/8)6Z/L^4 = 0 (Z = L^2, C = 2L) -- the algebra that
-- kills the n^{-1/2} term and makes |kernelMass - 1| = O(1/n) reachable.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.massLam_sq
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.boseKernel_eq_exp_form
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.mass_rate_sqrt_coeff_cancel

-- Ch8 MASS-RATE kernel-expansion side COMPLETE (R8 sect 3-4, Opus): sqrt-drop second order via the
-- algebraic identity 8s^3 E = (s-q)^3(q+3s) (linear_combination on q^2 = s^2 - m; no calculus, no
-- smallness hypothesis); reciprocal second order (exact identity m^2/(n^2(n-m))); exponential second
-- order (|e^x-1-x| <= x^2 with delta <= 9/32 under 4Cm^2 <= s^3); combined coefficient (R8 3.5,
-- only cross term -Cm^3/(8s^7) exact); explicit tail n^3 e^{-(C/2)n^{1/6}} beyond m^3 > n^2.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.sqrt_drop_second_order
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.inv_sub_second_order
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.exp_sqrt_drop_second_order
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.erdosWeight_coef_second_order
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.sqrt_drop_ge
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.kernel_tail_beyond_cube

-- Ch8 MASS-RATE: THE LAMBERT IDENTITY for M0 (R8 sect 2.1, Opus): sigmaMoment 0 t =
-- Sum_k boseKernel(tk), via Mathlib tsum_prod_pow_eq_tsum_sigma (divisors-antidiagonal machinery)
-- at k=1, r=e^{-t}; inner geometric-derivative sum + N <-> PNat support bridges.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.tsum_if_ne_zero_eq_pnat
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.tsum_pnat_coe_mul_geometric
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.sigmaMoment_zero_lambert

-- Ch8 MASS-RATE: quadratic geometric sum (M1-side ingredient, Opus): Sum d^2 y^d = y(1+y)/(1-y)^3
-- via n^2 = 2C(n+2,2) - 3C(n+1,1) + C(n,0) over Mathlib choose-geometric sums.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.tsum_nat_sq_mul_geometric
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.tsum_pnat_sq_mul_geometric

-- Ch8 MASS-RATE boseReg0 analysis core (R10 bricks 1-17, Opus): exp polynomial bounds (orders 3,4
-- via Real.exp_bound); boseReg0 rational form + |boseReg0| <= 4 near 0 (exact numerator identity
-- x^4/4 - 2x*delta - delta^2) + tail 4e^{-x} + 1/x^2; antiderivative F = 1/x - 1/(e^x-1) with F' =
-- boseReg0, F(0+) = 1/2, F(inf) = 0, finite FTC; THE INTEGRAL int boseReg0 = -1/2 (FTC anchor);
-- derivative closed form + tail bound + |boseReg0'| <= 32 near 0 (hand-computed degree-6
-- cancellation certificate B = -x^6/4 - x^7/6 - x^8/12 - x^9/54, ring-verified).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.exp_sub_one_bounds_order3
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.exp_sub_one_order4_bound
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.boseReg0_bdd_near_zero
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.boseReg0_tail_bound
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.boseAntideriv_hasDerivAt
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.boseAntideriv_tendsto_zero_right
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.integral_boseReg0_Ioi
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.boseReg0_hasDerivAt
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.boseReg0Deriv_tail_bound
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.boseReg0Deriv_bdd_near_zero
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.boseReg0_integrable_Ioi
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.boseReg0Deriv_integrable_Ioi

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

-- Ch7 first application of the UNCONDITIONAL logarithmic transfer to a genuine labelled species:
-- cycleMarkedPermPairClass = (CYC ⋆ SET(CYC)) ⋆ SET(CYC), EGF log(1/(1-z))·(1-z)^{-2} = logSingularityFun 2;
-- formal identity mapℂ A.egf = logSingularityGF 2, then transfer at α=2, C=1, zero remainder ⇒ aₙ/n! ~ n log n.
#print axioms AnalyticCombinatorics.mapℂ_cycleMarkedPermPairClass_egf
#print axioms AnalyticCombinatorics.cycleMarkedPermPairClass_counts_div_factorial_isEquivalent

-- Ch4 natural-remainder logarithmic transfer (removes the strong-remainder caveat of LogTransfer):
-- log-weighted Hankel/Cauchy contour estimate ⇒ residual o(|1-z|^{-α} log(1/|1-z|))
-- ⇒ [zⁿ]f ~ C·n^{α-1}/Γ(α)·log n.
#print axioms coeff_norm_isLittleO_atTop_of_delta_littleO_log_beta_gt_one
#print axioms log_transfer_theorem_natural_remainder
#print axioms AnalyticCombinatorics.log_transfer_theorem_natural_remainder_unconditional

-- First application that GENUINELY needs the natural remainder: (undirectedCycle ⋆ perm) ⋆ perm,
-- EGF (½log(1/(1-z)) - z/2 - z²/4)(1-z)^{-2}; residual ‖·‖·‖1-z‖²→3/4≠0 (strong transfer fails)
-- but /log(1/‖1-z‖)→0 (natural transfer applies) ⇒ aₙ/n! ~ ½·n·log n.
#print axioms AnalyticCombinatorics.mapℂ_undirectedCycleMarkedPermPairClass_egf
#print axioms AnalyticCombinatorics.undirectedCycleMarkedPermPairClass_counts_div_factorial_isEquivalent

-- Ch4 cpow exponent additivity (1-z)^{-α}(1-z)^{-β}=(1-z)^{-(α+β)} as formal series + the integer
-- family of cycle-marked perm tuples: log(1/(1-z))(1-z)^{-k} ⇒ aₙ/n! ~ n^{k-1}/(k-1)!·log n (k≥2).
#print axioms AnalyticCombinatorics.oneSubCpowGF_add
#print axioms AnalyticCombinatorics.mapℂ_cycleMarkedPermTupleClass_egf
#print axioms AnalyticCombinatorics.cycleMarkedPermTupleClass_counts_div_factorial_isEquivalent

-- Natural-remainder necessity at EVERY integer α=k≥2: undirectedCycle ⋆ perm^k,
-- residual ‖·‖‖1-z‖^k→3/4≠0 (strong fails) but /log→0 ⇒ aₙ/n! ~ ½·n^{k-1}/(k-1)!·log n.
#print axioms AnalyticCombinatorics.undirectedCycleMarkedPermTupleClass_counts_div_factorial_isEquivalent

-- Ch4 SQUARED-logarithm singularity transfer: (1-z)^{-α}log²(1/(1-z)), strong residual o(|1-z|^{-α})
-- ⇒ [zⁿ]f ~ C·n^{α-1}/Γ(α)·(log n)². Coeff identity via recurrence (2·logSingularityCoeff source).
#print axioms AnalyticCombinatorics.coeff_logSqGF_eq_logSqSingularityCoeffℂ

-- General log^k coefficient-identity layer: GF (1-z)^{-α}·(-log(1-z))^k via ODE recurrence
-- (n+1)T_k(n+1)=(α+n)T_k(n)+k·T_{k-1}(n), closed form k!·binCoeffℂ·e_k({(α+j)⁻¹}).
#print axioms AnalyticCombinatorics.logKGF_two
#print axioms AnalyticCombinatorics.coeff_logKGF_succ_recurrence
#print axioms AnalyticCombinatorics.logKCoeffℂ_succ_recurrence
#print axioms AnalyticCombinatorics.coeff_logKGF_eq_logKCoeffℂ
-- log^k faithfulness/analyticity: logKGF realizes (1-z)^{-α}(-log(1-z))^k on the unit ball + Δ-analytic.
#print axioms AnalyticCombinatorics.logKGF_hasSum
#print axioms AnalyticCombinatorics.logKSingularityFun_hasFPowerSeriesAt
#print axioms AnalyticCombinatorics.analyticOnNhd_logKSingularityFun_deltaDomain
-- log^k asymptotic scale: Newton identity (k+1)e_{k+1}=∑(-1)^r p_{r+1} e_{k-r}, k!·e_k ~ (log n)^k,
-- and the full scale logKSingularityScale α k n ~ n^{α-1}/Γ(α)·(log n)^k.
#print axioms AnalyticCombinatorics.shiftedElemSymm_newton
#print axioms AnalyticCombinatorics.logKBracket_isEquivalent_log_pow
#print axioms AnalyticCombinatorics.logKSingularityScale_isEquivalent
-- CAPSTONE: general logᵏ natural-remainder transfer + first end-to-end application.
#print axioms coeff_norm_isLittleO_atTop_of_delta_littleO_logK_beta_gt_one
#print axioms AnalyticCombinatorics.logK_transfer_theorem_natural_remainder
#print axioms AnalyticCombinatorics.logK_transfer_theorem_strong_remainder
-- BOUNDARY α=1: β=1 circle kernel (∫‖1-r·exp‖^{-1} ~ log n) ⟹ log transfer at α=1; first α≤1 result.
#print axioms coeff_norm_isLittleO_atTop_of_delta_littleO_beta_eq_one
#print axioms AnalyticCombinatorics.log_transfer_alpha_eq_one_strong_remainder
#print axioms AnalyticCombinatorics.cycleMarkedPermClass_counts_div_factorial_isEquivalent
#print axioms AnalyticCombinatorics.cycleMarkedPermLpowClass_counts_div_factorial_isEquivalent
#print axioms logSqSingularityScale_isEquivalent
#print axioms AnalyticCombinatorics.logSq_transfer_theorem_strong_remainder_unconditional

-- First log² combinatorial application: pair of perms each with a marked cycle ⇒ aₙ/n! ~ n·(log n)².
#print axioms AnalyticCombinatorics.cycleMarkedPermPairBothClass_counts_div_factorial_isEquivalent

-- Natural-remainder log² transfer (residual o(|1-z|^{-α}log²)) via the log²-weighted circle kernel.
#print axioms coeff_norm_isLittleO_atTop_of_delta_littleO_logSq_beta_gt_one
#print axioms AnalyticCombinatorics.logSq_transfer_theorem_natural_remainder

-- log²-NEEDING application: undirectedCycle ⋆ (perm-pair with marked cycle), EGF (½L-z/2-z²/4)·L·(1-z)^{-2}.
-- residual -(z/2+z²/4)·(1-z)^{-2}·L has ‖·‖‖1-z‖²≍|log(1-z)|→∞ (strong log² fails) but /log²→0
-- (natural log² applies) ⇒ aₙ/n! ~ ½·n·(log n)².
#print axioms AnalyticCombinatorics.mapℂ_undirectedCycleLogSqPermPairClass_egf
#print axioms AnalyticCombinatorics.undirectedCycleLogSqPermPairClass_counts_div_factorial_isEquivalent
-- and the certificate that this class genuinely NEEDS the natural (not strong) log² transfer:
-- along z=1-1/(n+2), ‖R‖·‖1-z‖² = ‖z/2+z²/4‖·log(n+2) → ∞, so R is not o(|1-z|^{-2}).
#print axioms AnalyticCombinatorics.logSqResidual_not_strong_remainder

-- GENERAL-k natural logᵏ⁺¹ application: undirectedCycle ⋆ (k-tuple of marked-cycle perms), EGF
-- (½L-z/2-z²/4)·(1-z)^{-k}·Lᵏ; residual -(z/2+z²/4)·(1-z)^{-k}·Lᵏ is o(|1-z|^{-k}logᵏ⁺¹) but not
-- o(|1-z|^{-k}) ⇒ natural logᵏ⁺¹ transfer ⇒ aₙ/n! ~ ½·n^{k-1}/(k-1)!·(log n)^{k+1} (general k≥2).
#print axioms AnalyticCombinatorics.mapℂ_undirectedCycleLogKPermLpowClass_egf
#print axioms AnalyticCombinatorics.undirectedCycleLogKPermLpowClass_counts_div_factorial_isEquivalent
-- and the certificate that this general-k class genuinely NEEDS the natural (not strong) transfer:
-- along z=1-1/(n+2), ‖R‖·‖1-z‖^k = ‖z/2+z²/4‖·(log(n+2))^k → ∞, so R is not o(|1-z|^{-k}).
#print axioms AnalyticCombinatorics.logKResidual_not_strong_remainder

-- Ch2 CYC combinatorial closed form: the labelled-cycle count is (n-1)! (the integer shadow of the
-- CYC logarithm log(1/(1-z)), [zⁿ] = 1/n, via [zⁿ]EGF = counts n / n!).
#print axioms AnalyticCombinatorics.atom_lcyc_counts_eq_factorial

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

-- Ch5 GENERAL COMPOSITIONS family, PARTIAL (the crux banked): for any finite alphabet S (|S|≥2, 0∉S),
-- the unique positive root ρ_S ∈ (0,1) of Σ_{s∈S} x^s = 1, and — the Perron-style theorem — STRICT
-- DOMINANCE under gcd(S)=1: every complex root with |z| ≤ ρ_S equals ρ_S (triangle-equality same-ray +
-- gcd phase argument). Genuine list count compS + first-part recurrence. Assembly (OGF identity +
-- explicit decomposition ⟹ unconditional asymptotic) = COMPGEN2, in flight.
#print axioms AnalyticCombinatorics.Ch5.Meromorphic.CompositionsGeneral.partPoly_rhoS
#print axioms AnalyticCombinatorics.Ch5.Meromorphic.CompositionsGeneral.root_eq_rhoS_of_gcd

-- Ch5 GENERAL COMPOSITIONS FAMILY, COMPLETE: for EVERY finite alphabet S (|S|≥2, 0∉S, gcd(S)=1), the
-- genuine ordered-composition count satisfies compS(n) ~ c_S·ρ_S^{−n} — OGF bridge from the first-part
-- recurrence, dominant-annulus from the Perron dominance theorem, assembled via the banked supercritical
-- decomposition machinery. Generalizes Fibonacci to all finite part-sets at once.
#print axioms AnalyticCombinatorics.Ch5.Meromorphic.CompositionsGeneral.Close.compS_isEquivalent

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

-- HR mass-rate campaign, bricks 19-20: the cubic geometric sum Σ n³yⁿ = y(1+4y+y²)/(1−y)⁴ (M₂-side
-- ingredient, via n³ = 6C(n+3,3)−12C(n+2,2)+7C(n+1,1)−C(n,0)) and the Basel split
-- boseKernel = 1/x² + boseReg0 with Σ'_{k≥1}1/(tk)² = (π²/6)/t².
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.tsum_nat_cube_mul_geometric
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.tsum_pnat_cube_mul_geometric
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.boseKernel_eq_inv_sq_add_reg
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.tsum_if_inv_sq
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.tsum_if_inv_sq_scaled

-- HR mass-rate campaign, brick 21 (M₁ Lambert): termwise differentiation of the Lambert identity on
-- Ioi(t/2) via hasDerivAt_tsum_of_isPreconnected on both the σ-side and the Bose side;
-- Σ' m·σ(m)e^{−tm} = Σ'_{k≥1} k·boseKernel2(tk), boseKernel' = −boseKernel2.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.boseKernel_hasDerivAt
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.sigmaMoment_one_lambert

-- HR mass-rate campaign, bricks 22-23: the M₂ Lambert identity (Σ' m²σ(m)e^{−tm} = Σ'_{k≥1}
-- k²·boseKernel3(tk), boseKernel2' = −boseKernel3 by quotient rule, termwise differentiation of M₁)
-- and the crude moment power bound M_r(t) ≤ (r+2)!·2^{r+3}/t^{r+3} on (0,1] (m^j ≤ j!·C(m+j,j)
-- via descFactorial + choose-geometric sum) — tail input for the §5–7 assembly.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.boseKernel2_hasDerivAt
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.sigmaMoment_two_lambert
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.tsum_pow_mul_geometric_le
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.sigmaMoment_le_power

-- HR mass-rate campaign, brick 24 (the Riemann engine + M₀ weak asymptotics): right-endpoint
-- Riemann sums of boseReg0 with mesh t differ from (1/t)∫boseReg0 = −1/(2t) by ≤ ∫|boseReg0′| (cell
-- partition + FTC per cell + hasSum_integral_iUnion); hence |M₀(t) − (π²/6)/t² + 1/(2t)| = O(1).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.cell_error
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.riemann_boseReg0_bound
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.sigmaMoment_zero_asymp_weak

-- HR mass-rate campaign, bricks 25-26 (weighted-decay keystone + M₁ weak asymptotics): the
-- reusable Σ' k^j|f(tk)| ≤ K/t^{j+1} bound (near-origin Cf + exp tail + Basel tail), and its first
-- instantiation |M₁(t) − 2(π²/6)/t³| ≤ 388/t² via boseKernel2 = 2/z³ − boseReg0′.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.tail_inv_sq_shift
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.weighted_decay_sum_bound
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.boseKernel2_eq_inv_cube_sub_deriv
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.sigmaMoment_one_asymp_weak

-- HR mass-rate campaign, bricks 27-28 (M₂ weak asymptotics): the degree-8 reg3 cancellation
-- certificate |boseKernel3 z − 6/z⁴| ≤ 3600 on (0,1] (w order-7 Taylor + δ-decomposition,
-- degree-28 ring numerator identity), and |M₂(t) − 6(π²/6)/t⁴| ≤ K/t³ via the weighted-decay
-- keystone (j=2). Completes the M₀/M₁/M₂ moment-asymptotics layer.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.reg3_bdd_near_zero
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.sigmaMoment_two_asymp_weak

-- HR mass-rate campaign, brick 29 (sharp-moment-bound foundations): the weighted divisor Fubini
-- M_r(t) = Σ_a Σ_b a^{r+1} b^r (e^{−t})^{ab} (via sigmaAntidiagonalEquivProd; Σ_{ab=e} a^{r+1}b^r
-- = e^r σ(e)) and the ℕ+×ℕ+ summability of the weighted antidiagonal summand. Input to the
-- sharp bound M_r ≤ K/t^{r+2} (two-regime, in progress) needed for §5 M₃/M₄ error terms.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.summable_weighted_antidiag
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.sigmaMoment_eq_prod_tsum
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.tsum_pnat_pow_mul_geometric_le
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.sigmaMoment_le_power_sharp

-- HR mass-rate campaign, brick 30 (§6 √n-cancellation): the second-order kernel-mass approximation
-- kernelMassApprox2 n = (1/n)M₀(t)+(1/n²)M₁(t)−(C/(8n²√n))M₂(t) at t=λ/√n, and |kernelMassApprox2 n − 1|
-- ≤ K/n eventually — the three weak moment asymptotics give leading 1, the 1/√n terms cancel exactly
-- (mass_rate_sqrt_coeff_cancel, λ²=π²/6), all remainders O(1/n). First §5-7 assembly brick.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.kernelMassApprox2_cancel_sqrt_term

-- HR mass-rate campaign, brick 31 (§5 model identity): the second-order kernel-mass approximation
-- collapses to a single divisor-weighted Lambert sum, kernelMassApprox2 n = ∑' m, modelSummand n m,
-- where modelSummand n m = σ(m)·e^{−tm}·(1/n+m/n²−Cm²/(8n²√n)) at t=λ/√n. This is the object the
-- per-term estimate erdosWeight_coef_second_order (#97, ×σ(m)≥0) is compared against in §5.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.kernelMassApprox2_eq_tsum_model

-- HR mass-rate campaign, bricks 32-33 (§5 error core): the divisor-weighted error majorant
-- (3C²+5C+2)·[(1/n³)M₂+(1/(n³√n))M₃+(1/n⁴)M₄](λ/√n) ≤ K/n (pure sharp #119 at r=2,3,4), and the
-- per-term error |erdosWeight n m − modelSummand n m| ≤ σ(m)·#97RHS on the main range (the
-- σ(m)-weighted form of erdosWeight_coef_second_order). Together: main-range error sums to O(1/n).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.model_error_moment_bound
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.erdosWeight_sub_model_le

-- HR mass-rate campaign, brick 34 (§5 main-range sum): ∑_{m=1}^{⌊n^{2/3}⌋} |erdosWeight − modelSummand|
-- ≤ K/n. Per-term #97×σ(m) (brick 33) on the cutoff range (mainCut_cond gives 2m≤n, 4Cm²≤√n³ for
-- m≤⌊n^{2/3}⌋), then the finite divisor sums ≤ the full Lambert moments (sum_le_hasSum), reducing to
-- the O(1/n) error-moment bound (brick 32). Main-range part of kernelMass_sub_approx2.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.main_range_error_le

-- HR mass-rate campaign, brick 35 (§5 model tail): the m>⌊n^{2/3}⌋ tail of |modelSummand| is O(1/n).
-- Reusable engines: poly_mul_exp_neg_sixthRoot_le_inv (n^d·exp(−a n^{1/6}) ≤ 1/n, exp beats poly),
-- sigma_geom_tail_le (m>M Lambert tail ≤ exp(−(t/2)M)·M_k(t/2)). Three moment tails (sharp #119) →
-- surviving exp(−(λ/4)n^{1/6}) ≤ 1/n. Part of kernelMass_sub_approx2.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.model_tail_le

-- HR mass-rate campaign, brick 36 (§5 far-erdosWeight tail): ∑_{m=⌊n^{2/3}⌋+1}^{n-1} erdosWeight ≤ K/n.
-- Right half (n<2m): right_half_kernel_sum_le (n³exp(−(C/10)√n)) + √n exp-beats-poly. Left far
-- (2m≤n): block majorants at index ⌊n^{1/6}⌋ + geometric tail (leftBlockMajorant_shifted_tsum_le)
-- + sixth-root exp-beats-poly. Last tail brick for kernelMass_sub_approx2.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.far_erdos_tail_le

-- HR mass-rate campaign, brick 39 (§6→§7 bridge): the kernel-mass rate in o(slack) form —
-- ∀ρ>0, ∀ᶠ n, |kernelMass n − 1| ≤ ρ·barrierSlack E n. The 1/n rate (#38) beats
-- barrierSlack = 1/(√n(log(n+E))²) since (log(n+E))²=o(√n) (isLittleO_log_rpow_rpow_atTop).
-- This is exactly the hypothesis the barrier super/subharmonic theorems consume.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.kernelMass_rate_vs_slack

-- HR mass-rate campaign, brick 40 (§7 unconditional u-bounds): u_limsup_finite (∃M, ∀ᶠ u n ≤ M) and
-- u_liminf_positive (∃c>0, ∀ᶠ c ≤ u n). The banked o(slack) mass rate (#39) discharges the barrier
-- super/subharmonic hypotheses (upperBarrier_kernel_superharmonic_of_rate now also returns the
-- ∀k upperBarrier-pos needed by u_limsup_finite_of_superharmonic). Unconditional u boundedness.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.u_limsup_finite
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.u_liminf_positive

-- HR mass-rate campaign, brick 41 (§8 R7 one-step record pullback): the exact quantitative pullback
-- exists_window_near_max — N running-max on [N₀,N] + window mass ≥μ ⟹ ∃ window predecessor within the
-- defect Δ_N=(|b(N)|+M|S_N−1|+M·prefixTail)/μ of u N. (ChatGPT consult: (1)-(5) alone are insufficient
-- — countermodel — so the honest route needs this quantitative defect, summable in t=√n.)
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.exists_window_near_max
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.exists_window_near_min
-- HR mass-rate campaign, brick 43 (§8 R7 cover summability): the chain-independent summability
-- building blocks for the rank-indexed error budget Σⱼ E(j) (ChatGPT c43aa296 cover induction):
-- Σₜ B/(t+1)² (kernel-mass 1/n rate) + Σₜ tᵏe^{−ct} (boundary & far-tail exp decay).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.summable_defect_scale
-- HR mass-rate campaign, brick 44 (§8 R7 renewal route — replaces record-cover, whose 1/μ amplification
-- is proven intrinsic): the design-independent convergence spine. tendsto_of_uniform_hit_approx (Layer 5:
-- uniform hit-approximation + vanishing J-tail ⟹ u converges) and rec_iter_bound (Layer 2: Hit/Pot
-- potential controls the hit-approximation error, strong induction over predecessors). Hard renewal core
-- (occupation bound + overshoot convergence, from the Gamma(2,C) √n-decrement law) remains open.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.tendsto_of_uniform_hit_approx
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.rec_iter_bound
-- HR mass-rate campaign, brick 45 (§8 R7 Layer 3 — Fact A occupation bound, ELEMENTARY): with
-- rank n = ⌊ρ√n⌋ (ρ>2/α) each kernel step strictly decreases rank (m>α√n ⟹ √n−√(n−m)>α/2), so the
-- backward chain visits each rank block ≤ once ⟹ Pot J e n ≤ Σ_{j=J}^{rank n} e j (≤ block tail).
-- No renewal-density theory needed; only Fact B (overshoot convergence) remains hard.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.pot_le_block_sum
-- HR mass-rate campaign, brick 46 (§8 R7 Layer 3 — Fact A for the FULL kernel, leave-probability):
-- the full normalized kernel has small steps, but each block is left downward w.p. ≥μ (window step
-- drops rank, window mass ≥μ); contraction induction gives μ·Pot ≤ block-sum. The 1/μ is a single
-- constant on the summable tail, NOT the per-step μ^{−√N} that killed the record route. Plus the tail
-- helpers (block ≤ (∑'e − partial) → 0). Fact A DONE; only Fact B (overshoot convergence) remains.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.pot_le_block_sum_of_leave
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.block_sum_le_tail
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.tail_tendsto_zero
-- HR mass-rate campaign, brick 47 (§8 R7 Hit/Pot well-founded construction): the harmonic-extension
-- and residual-potential functions built by WF recursion on n (sum over (range n).attach carries the
-- k<n membership for termination), with defining equations recovered via Finset.sum_attach. These
-- supply the Hit/Pot fixed-point hypotheses that rec_iter_bound and pot_le_block_sum_of_leave consume.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.hitVal_eq
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.potVal_eq
-- HR mass-rate campaign, brick 48 (§8 R7 Layer 1 — partition-kernel instantiation): the predecessor
-- transition kernel Pker = erdosWeight n (n−k)/kernelMass n, rank ⌊3√n⌋, residual dres, with the
-- step-reflection reindex (k↦n−k), the folding identity Pker_sum_mul, the probability normalization
-- Pker_mass (=1), and the residual formula dres_eq = u n − (u n − boundaryTerm n)/kernelMass n.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.Pker_sum_mul
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.Pker_mass
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.dres_eq
-- HR mass-rate campaign, brick 49 (§8 R7 rank-drop facts, shared by both endgame routes): the floor
-- bounds rnk n ≤ 3√n < rnk n+1, the strict rank drop from a √-gap > 1/3, and window_rank_drop — a
-- window step m>√n forces √n−√(n−m) > 1/2 > 1/3 hence rnk(n−m) < rnk n. Feeds the leave-probability
-- (hit-approx pot bound) and the support-slab / Doeblin overlap (oscillation-contraction route).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.rnk_sqrt_bounds
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.window_rank_drop
-- HR mass-rate campaign, brick 50 (§8 R7 residual summability `herr`): |dres n| ≤ errFn (rnk n)
-- eventually, errFn = 72MK/(j+1)² + (32/81)j⁴e^{−(C/3)j} (≥0, summable via DefectSummable). The
-- "small summable residual" input both endgame routes need. Scale-converted from dres_eq +
-- kernelMass_sub_one_rate + u_limsup_finite via rnk_sqrt_bounds + boundaryTerm ≤ n²e^{−C√n}.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.dres_block_bound
-- HR mass-rate campaign, brick 51 (§8 R7 leave-probability `hP_leave`, Layer 1 COMPLETE): a uniform
-- positive mass ν/2 of the normalized kernel goes to strictly lower rank — window steps m∈(√n,2√n]
-- carry mass ≥ν (kernelWindow_one_two_pos = a₀=1 instance) and drop rank (window_rank_drop), divided
-- by kernelMass n ≤ 2. With Pker_mass/dres_eq/dres_block_bound this completes all kernel hypotheses
-- of rec_iter_bound + pot_le_block_sum_of_leave; convergence now reduces to the hard core (Fact B).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.kernelWindow_one_two_pos
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.hP_leave_partition
-- HR mass-rate campaign, brick 52 (§8 R7 ASSEMBLY): erdos_partition_limit_exists_of_hit — the entire
-- Erdős convergence reduced to a single isolated hard hypothesis (Fact B: hitVal Pker rnk J u
-- converges for cofinitely many cutoffs J). Instantiates rec_iter_bound + pot_le_block_sum_of_leave +
-- block_sum_le_tail + the convergence engine with the concrete partition kernel; positivity from
-- u_liminf_positive. rnk_ge_of converts eventual-in-n facts to J≤rnk n form. All else is clean-3.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.rnk_ge_of
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.erdos_partition_limit_exists_of_hit
-- HR mass-rate campaign, brick 53 (§8 R7 Fact-B route, File A — deterministic Doeblin keystone):
-- doeblin_average_diff_bound — probability vectors with overlap ≥δ averaging an osc-≤W function differ
-- by ≤(1−δ)W (common mass cancels; residuals carry ≤1−δ mass). Pure nonnegative-sequence analysis.
-- The contraction coefficient for the oscillation-contraction route to Fact B (ChatGPT 12a957cc).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.subprob_avg_diff
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.doeblin_average_diff_bound
-- HR mass-rate campaign, brick 54 (§8 R7 Fact-B route, File C — oscillation→0 engine):
-- tendsto_zero_of_step_contraction — W(n+L) ≤ q·W(n)+e_n with 0≤q<1, e→0 ⟹ W→0 (forcing need only
-- vanish, not be summable). The convergence driver for the Doeblin block-oscillation contraction.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.tendsto_zero_of_step_contraction
-- HR mass-rate campaign, brick 55 (§8 R7 Fact-B route, File B — kernel power algebra): KComp/KPow
-- (predecessor kernel composition + L-fold power), nonnegativity, and strict predecessor-support
-- preservation (KPow_support: n<k → ·=0; KPow_succ_support: L≥1 kills n≤k). Foundation for the
-- finite-time Doeblin overlap and the P^L-harmonic identity for hitVal.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.KPow_nonneg
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.KPow_succ_support
-- HR mass-rate campaign, brick 56 (§8 R7 Fact-B route — pairwise contraction step): pair_contract —
-- two points whose iterated transition laws overlap ≥δ over a common support, each η-approximately
-- harmonic, satisfy |u i − u j| ≤ (1−δ)W + 2η (W = band width of u on the support). The deterministic
-- heart of the renewal oscillation contraction; δ supplied by the (remaining) finite-time Doeblin overlap.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.pair_contract
-- HR mass-rate campaign, brick 57 (§8 R7 Fact-B route — §9 convergence engine): tendsto_of_center_tracking
-- — summable tail-sup V of block oscillation + center links (|c(R+1)−c R|≤V R) + tracking
-- (|h n − c(rank n)|≤V(rank n)) ⟹ h converges. Resolves the far-pair obstruction via the MONOTONE
-- tail-sup (which contracts geometrically); no overlap for far ranks needed.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.tendsto_of_center_tracking
-- HR mass-rate campaign, brick 58 (§8 R7 Fact-B route — geometric summability): summable_of_step_le —
-- f≥0 with f(n+B)≤q·f(n), 0≤q<1 ⟹ Summable f (uniformly bounded partial sums: S_m ≤ S_B+q·S_m).
-- Converts the tail-sup block-osc contraction V(R)≤(1−δ)V(R−B) into Summable V for tendsto_of_center_tracking.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.summable_of_step_le
-- HR mass-rate campaign, brick 59 (§8 R7 Fact-B route — tail-sup summability): tailsup_summable —
-- bounded W≥0 with slab contraction W R ≤ q·sSup(W''{s≥R−B}) ⟹ its tail-sup V R := sSup(W''{s≥R})
-- satisfies V R ≤ q·V(R−B) (monotone domination) hence Summable V. Turns the local comparable-rank
-- contraction into a global summable bound — the resolution of the §9 far-pair obstruction.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.tailsup_summable
-- HR mass-rate campaign, brick 60 (§8 R7 killed-kernel powers): KCompK/KPowK — boundary-absorbing
-- kernel composition (sum over range(n+1), allowing the diagonal) + L-fold power; nonnegativity and
-- support n<k→0. Foundation for the P̃^L-harmonic identity of the exactly-harmonic hitVal.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.KPowK_nonneg
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.KPowK_support
-- HR mass-rate campaign, brick 61 (§8 R7 killed-kernel harmonicity): killed_harmonic_pow — a function
-- harmonic above a cutoff (h n = ∑_{k<n} P n k·h k for rank n ≥ J, = φ below) is exactly harmonic for
-- every killed power KPowK L P̃ summed over range(n+1). The η=0 exactness driving the Doeblin osc
-- contraction for hitVal. Proof by induction on L (one-step + Finset.sum_comm + support truncation).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.killed_harmonic_one
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.killed_harmonic_pow
-- HR mass-rate campaign, brick 62 (§8 R7 killed-kernel stochasticity): killedKer/KPowK row-stochastic
-- over range(n+1); the probability-vector hypothesis for the Doeblin contraction.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.killedKer_row_sum
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.KPowK_row_sum
-- HR mass-rate campaign, brick 63 (§8 R7 tail-osc → convergence): a vanishing tail-oscillation
-- dominator forces h to be Cauchy along rank→atTop, hence convergent (the §9 endgame).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.tendsto_of_tail_osc_to_zero
-- HR mass-rate campaign, brick 64 (§8 R7 escape-split Doeblin): doeblin_escape_bound — overlap δ on a
-- high-rank good band + escape mass η gives |∑p·f−∑q·f| ≤ (1−δ)·W + 3ηM (wide-support contraction).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.doeblin_escape_bound
-- HR mass-rate campaign, brick 65 (§8 R7 tail band): tailOsc sup/inf band — antitone, ≤2M, dominates
-- pairwise |h i−h j|, and is bounded above by a uniform pairwise bound (lo/W for the escape contraction).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.tailOsc_abs_le
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.tailOsc_le_of_pairwise
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.tail_band
-- HR mass-rate campaign, brick 66 (§8 R7 §9 FINAL ASSEMBLY): tendsto_of_killed_doeblin — a bounded
-- KPowK L P̃-harmonic function converges given finite-time Doeblin overlap δ>0 on the high-rank band and
-- vanishing escape mass. Reduces Hardy–Ramanujan convergence to exactly two analytic kernel facts.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.tendsto_of_killed_doeblin
-- HR mass-rate campaign, brick 67 (§8 R7 concrete kernel facts): rnk → atTop and kernelMass eventually
-- positive — the divergence + positivity facts to instantiate the abstract Doeblin theorem for Pker.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.rnk_tendsto_atTop
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.kernelMass_pos_eventually
-- HR mass-rate campaign, brick 68 (§8 R7 hitVal boundedness): Pker substochastic + bounded boundary ⟹
-- bounded hitVal — the boundedness hypothesis of tendsto_of_killed_doeblin for the concrete kernel.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.Pker_sum_le_one
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.hitVal_abs_le
-- HR mass-rate campaign, brick 69 (§8 R7 HARDY–RAMANUJAN REDUCTION): erdos_partition_limit_exists_of_walls
-- — if the Doeblin walls (finite-time overlap δ>0 on the high-rank band + vanishing escape mass) hold
-- for cofinitely many cutoffs J, the normalized partition sequence u converges to a positive limit.
-- The complete mechanical reduction; only the two analytic walls remain (Γ-convolution local limit).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.erdos_partition_limit_exists_of_walls
-- HR mass-rate campaign, brick 70 (§8 R7 multi-scale const engine): the escape mass below a FIXED band
-- is constant in R (~e^{−cB}), so the escape-split engine needs the multi-scale form — bounded forcing
-- bounds the limsup, and a null family of bounds drives the tail oscillation to 0.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.limsup_le_of_step_contraction_const
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.tendsto_zero_of_limsup_le_all
-- HR mass-rate campaign, brick 71 (§8 R7 multi-scale §9 assembly): the corrected capstone —
-- tendsto_of_killed_doeblin_multiB drives convergence from a family of band contractions (overlap δ_B on
-- band {rnk ≥ R−B} + escape ε_B with 3·ε_B·M/δ_B → 0), reusing doeblin_escape_bound per scale.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.tendsto_of_tailOsc_multiB
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.tendsto_of_killed_doeblin_multiB
-- HR mass-rate campaign, brick 72 (§8 R7 multi-scale HARDY–RAMANUJAN REDUCTION):
-- erdos_partition_limit_exists_of_walls_multiB — if the B-indexed Doeblin walls (overlap δ_B on band
-- {rnk ≥ R−B} + escape ≤ ε_B with ε_B/δ_B → 0) hold cofinitely, then u → a > 0. The SATISFIABLE form
-- of the reduction (the escape need not vanish at any fixed band width).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.erdos_partition_limit_exists_of_walls_multiB
-- HR mass-rate campaign, brick 73 (§8 R7 renewal-alignment capstone): tendsto_of_renewal_alignment —
-- the CORRECT convergence (the all-pairs single-step overlap is false for far-rank pairs). A bounded
-- function harmonic for every kernel power, whose m-step terminal laws align
-- (overlap ≥ 1−(1−δ)^m−ε for high starts), converges. Full-support overlap algebra + antitone squeeze.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.tendsto_of_renewal_alignment
-- HR mass-rate campaign, brick 74 (§8 R7 HARDY–RAMANUJAN REDUCTION, correct form):
-- erdos_partition_limit_exists_of_alignment — if the renewal-alignment (m-step terminal-law overlap
-- ≥ 1−(1−δ)^m−ε for high-rank starts) holds cofinitely, then u → a > 0. The SATISFIABLE reduction;
-- the lone remaining analytic wall is ErdosAlignment (comparable-rank overlap + descent coupling).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.erdos_partition_limit_exists_of_alignment
-- HR mass-rate campaign, brick 75 (§8 R7 scalar recursion solver): scalar_rec_solve — closed form for
-- u(t+1) ≤ q·u t + δ·e t, the engine of the windowed-coupling unmatched-mass recursion.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.scalar_rec_solve
-- HR mass-rate campaign, brick 76 (§8 R7 DETERMINISTIC WINDOWED-COUPLING ITER): iter_window_overlap —
-- finite-sum coupling (ρ_t common-minorant + U_t unmatched-pair-mass, marginal invariant ρ_t + U_t-marg
-- = P^t) gives overlap(P^m i, P^m j) ≥ 1 − (1−δ)^m − δ·∑(1−δ)^{m−t−1}·badMass_t. NO probabilistic
-- coupling library; reduces the renewal alignment to windowed minorization (B_W) + the bad-mass bound.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.left_marginal
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.iter_window_overlap
-- HR mass-rate campaign, brick 77 (§8 R7 center-tracking packaging): tendsto_of_comparable_contraction
-- — a summable vanishing block-oscillation bound tracking h to its block centers forces convergence;
-- this is the form that resolves the far-pair obstruction (only comparable-rank control needed, far
-- pairs handled by the summable center links). The interface the windowed-coupling ITER feeds.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.tendsto_of_comparable_contraction
-- HR mass-rate campaign, brick 78 (§8 R7 L¹→overlap bridge): overlap = 1 − ½·‖p−q‖₁ for prob vectors,
-- so an L¹ bound ‖p−q‖₁ ≤ 2(1−δ) gives the minorization δ ≤ ∑min(p,q). Reduces the (B_W) windowed
-- minorization to the Pker L¹-continuity estimate (C3).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.overlap_eq_one_sub_half_L1
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.overlap_ge_of_L1_le
-- HR mass-rate campaign, brick 79 (§8 R7 ELEMENTARY DOEBLIN MINORIZATION): the comparable-rank overlap
-- is bounded below WITHOUT σ-averaging. Key: σ(m) ≥ m (m ∣ m), so on the jump window [√x,2√x] the
-- σ-block mass is Θ(x); with the smooth factor Θ(1)/x and ~√x landings, the overlap ≥ e^{−C(2+D)}/8.
-- This is the harder Doeblin wall (C3) cracked elementarily — no arithmetic local-limit theorem needed.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.sigmaR_ge_self
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.Pker_lower
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.Pker_window_minor
-- HR mass-rate campaign, brick 80 (§8 R7 HARMONIC→OVERLAP BRIDGE): route-independent half of the
-- convergence engine. A bounded m-step-harmonic function has |h i − h j| ≤ 2B(1 − overlap(pᵢ,pⱼ));
-- so once the windowed coupling drives the m-step-law overlap → 1, the harmonic hit values coalesce.
-- Pure finite linear algebra (∑(p−q)h ≤ B·‖p−q‖₁ + the L¹/overlap identity), valid for ANY route by
-- which overlap→1 is obtained (single-window coupling, recurrence, or a direct renewal argument).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.weighted_diff_le_L1
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.harmonic_diff_le_overlap
-- HR mass-rate campaign, brick 81 (§8 R7 WINDOW-OCCUPATION ITER bound): the single fixed-window pass
-- is provably insufficient for C = π/√6 (self-consistency 2 ln v = c v, c ≈ ⅔C > 2/e, no solution).
-- Telescoping umass_core credits EVERY window-return of the rank-difference walk: umass m ≤
-- 1 − δ·∑_{t<m} goodMass t, hence overlap(Pᵐ i,Pᵐ j) ≥ δ·∑ goodMass t. Reduces the whole wall to the
-- lone occupation/local-time input ∑ goodMass t → 1/δ (rank-difference walk recurrence).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.umass_le_one_sub_occupation
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.overlap_ge_occupation
-- HR mass-rate campaign, brick 82 (§8 R7 GREEN-POTENTIAL occupation lower bound): the window
-- occupation is bounded BELOW by a Poisson subsolution g of the residual kernel Kres. Telescoping
-- the Green-weighted residual mass: g i j − greenMass M ≤ ∑_{t<M} goodMass t (tight form). With g the
-- occupation-before-absorption potential (g = 0 on absorbed pairs, 0 ≤ g ≤ 1/δ, g i j → 1/δ ⟺
-- recurrence), greenMass M → 0 even as umass M ↛ 0, so ∑ goodMass → 1/δ and umass M → 0 — exactly the
-- recurrence gain the single-window ITER missed. Reduces the entire wall to constructing g.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.greenMass_succ_ge
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.occupation_ge_green_tight
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.occupation_ge_green
-- HR mass-rate campaign, brick 83 (§8 R7 GREEN POTENTIAL is a SUBSOLUTION FOR FREE): the finite-horizon
-- truncated Green potential greenT T = ∑_{t<T} KresAct^[t] goodIndic satisfies the Poisson identity
-- KresAct(greenT T) = greenT T − goodIndic + KresAct^[T] goodIndic (nonneg tail), hence the subsolution
-- greenT T − 1_GoodW ≤ ∑ Kres · greenT — exactly occupation_ge_green_tight's hypothesis, with NO
-- recurrence needed. Reduces the wall to the lone expected-local-time lower bound greenT T (i,j) ≥
-- (1−ε)/δ (the √T recurrence content) + ITER instantiation to the killed Erdős kernel.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.greenT_poisson
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.greenT_subsolution
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.greenT_nonneg
-- HR mass-rate campaign, brick 84 (§8 R7 PALEY–ZYGMUND moment interpolation): (∑ p f²)³ ≤
-- (∑ p|f|)²·(∑ p f⁴) for nonneg weights, via two Cauchy–Schwarz. With ∑p=1 this is
-- E|f| ≥ (E f²)^{3/2}/√(E f⁴) — the anti-concentration lower bound on E|f| from 2nd/4th moments that
-- yields E|D_T| ≥ c√T in the deterministic-substrate Tanaka local-time route for the occupation bound.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.mean_sq_cubed_le_nonneg
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.mean_sq_cubed_le
-- HR mass-rate campaign, brick 85 (§8 R7 TANAKA single-step drift of |D|): for a mean-preserving kernel
-- with bounded increments b, |D| is a submartingale whose one-step drift ∑K|D|−|D x| is ≥ 0 (Jensen),
-- ≤ b (triangle), and = 0 when |D x| > b (same-sign). Telescoped this is the Tanaka decomposition
-- E|D_T| = E|D_0| + compensator, compensator = window local time supported on {|D|≤b}, giving
-- window-occupation ≥ (E|D_T|−E|D_0|)/b; with E|D_T| ≥ c√T (brick 84) ⟹ occupation ≥ c√T/b ≥ 1/δ.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.abs_drift_nonneg
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.abs_drift_le
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.abs_drift_eq_of_far
-- HR mass-rate campaign, brick 86 (§8 R7 TANAKA TELESCOPING): telescoping the per-step |D|-drift over the
-- evolving law distPow K μ₀ t gives E|D_T| − E|D_0| ≤ b·∑_{t<T}(window-b occupation at t), i.e.
-- window-occupation ≥ (E|D_T| − E|D_0|)/b. With E|D_T| ≥ c√T (brick 84) this is the occupation lower
-- bound. All deterministic finite-sum (distPow = law after t steps; no measure theory).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.distPow_nonneg
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.abs_drift_le_indic
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.occupation_ge_tanaka
-- HR mass-rate campaign, brick 87 (§8 R7 QUADRATIC-VARIATION telescoping, Doob for D²): for a mean-
-- preserving kernel the second-moment drift equals the local variance locVar x = ∑ K x z (D z−D x)²
-- (locVar_eq), so E[D_T²] − E[D_0²] = ∑_{t<T} ∑_x distPow t x · locVar x (sq_moment_telescope). With a
-- uniform lower bound v₀ ≤ locVar this gives E[D_T²] ≥ E[D_0²] + v₀·T (sq_moment_ge) — the lower
-- quadratic variation feeding Paley–Zygmund (brick 84) for E|D_T| ≥ c√T. Deterministic finite-sum.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.locVar_eq
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.distPow_sum
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.sq_moment_telescope
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.sq_moment_ge
-- HR mass-rate campaign, brick 88 (§8 R7 FOURTH-MOMENT per-step drift): for a mean-preserving kernel
-- with bounded increments b, ∑ K x z (D z)⁴ − (D x)⁴ ≤ 8 b² (D x)² + 3 b⁴ (binomial expansion +
-- locVar/M3/M4 ≤ b²·,b³·,b⁴ increment bounds + AM-GM). Telescoped with the upper QV E[D_t²] ≤ D₀²+b²t
-- this gives the BDG-type E[D_T⁴] ≤ C b⁴ T², the 4th moment feeding Paley–Zygmund E|D_T| ≥ c√T.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.fourth_drift_le
-- HR mass-rate campaign, brick 89 (§8 R7 telescoped moment bounds): upper QV E[D_T²] ≤ E[D_0²] + b²·T
-- (sq_moment_le, from locVar ≤ b²) and fourth-moment growth E[D_T⁴] − E[D_0⁴] ≤ ∑_{t<T}(8b²E[D_t²]+3b⁴)
-- (fourth_moment_telescope_le, from fourth_drift_le). With the lower QV (sq_moment_ge) + Paley–Zygmund
-- (mean_sq_cubed_le) these give E|D_T| ≥ c√T for the Tanaka occupation lower bound. Deterministic finite-sum.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.sq_moment_le
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.fourth_moment_telescope_le
-- HR mass-rate campaign, brick 90 (§8 R7 closed-form 4th moment): locVar_le (locVar ≤ b²) and
-- fourth_moment_le_quadratic E[D_T⁴] ≤ E[D_0⁴] + 8b²E[D_0²]·T + 8b⁴·T² + 3b⁴·T (substitute upper QV into
-- the 4th-moment telescoping). Quadratic-in-T, so (lower QV)^{3/2}/√(4th) ≥ c√T (Paley–Zygmund), giving
-- E|D_T| → ∞ and the Tanaka window occupation → ∞. Deterministic finite-sum.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.locVar_le
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.fourth_moment_le_quadratic
-- HR mass-rate campaign, brick 91 (§8 R7 OCCUPATION CAPSTONE): for a mean-preserving, bounded-increment,
-- uniformly-positive-local-variance walk, E|D_T| is UNBOUNDED in T (abs_mean_unbounded: Paley–Zygmund
-- A³ ≤ B²·Dq with A ≥ v₀T and Dq ≤ C·T² ⟹ B² ≥ M² for T ≥ M²C/v₀³), hence the cumulative window
-- occupation is unbounded (occupation_unbounded, via Tanaka brick 86). This is the abstract recurrence
-- content: the residual coupling spends arbitrarily long in the window, so coalescence exceeds any 1/δ.
-- Completes the deterministic Tanaka occupation lower bound. No measure theory, no local-CLT.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.abs_mean_unbounded
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.occupation_unbounded
-- HR mass-rate campaign, brick 92 (§8 R7 η-ROBUST Tanaka occupation): the Erdős rank-difference walk is
-- only an approximate martingale (|∑K D z − D x| ≤ η, η~1/r²→0). η-robust per-step |D|-drift (off-window
-- ≤ η not 0) telescopes to E|D_T| − E|D_0| ≤ b·(window occ) + η·T, so occ ≥ (E|D_T|−E|D_0|−η·T)/b. Since
-- η·T ≪ √T ≤ E|D_T| at the optimal horizon T~r², occupation still diverges. Launches the η-robust
-- instantiation phase (re-deriving 85-91 with drift error). Deterministic finite-sum.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.abs_drift_le_indic_eta
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.occupation_ge_tanaka_eta
-- HR mass-rate campaign, brick 93 (§8 R7 η-ROBUST lower QV): the second-moment drift is the unconditional
-- identity ∑K(D z)² − (D x)² = locVar x + 2·D x·e (sq_drift_id, e = drift error), and 2 D x e ≥ −2Rη via
-- (R+Dx)(η+e)+(R−Dx)(η−e) ≥ 0 (sq_drift_ge_eta). Telescoped: E[D_T²] ≥ E[D_0²] + (v₀−2Rη)·T
-- (sq_moment_ge_eta). With η~1/r², R~r the correction 2Rη~1/r→0, so the lower QV survives. Finite-sum.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.sq_drift_id
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.sq_drift_ge_eta
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.sq_moment_ge_eta
-- HR mass-rate campaign, brick 94 (§8 R7 η-ROBUST OCCUPATION CAPSTONE): for the η-approximate-martingale
-- walk, the window occupation is unbounded (occupation_unbounded_eta). KEY simplification: the 4th moment
-- is bounded TRIVIALLY by R⁴ (|D|≤R, fourth_moment_le_R4) — no re-derived 4th moment needed. PZ with the
-- linear lower QV E[D_T²] ≥ (v₀−2Rη)T gives (E|D_T|)² ≥ ((v₀−2Rη)T)³/R⁴ → ∞ (cubic), and via η-robust
-- Tanaka occ ≥ (E|D_T|−E|D_0|−ηT)/b with E|D_T| ~ T^{3/2} ≫ ηT, the occupation exceeds any target.
-- Completes the abstract+η-robust occupation lower bound. Only concrete Pker instantiation remains.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.fourth_moment_le_R4
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.occupation_unbounded_eta
-- HR mass-rate campaign, brick 95 (§8 R7 COALESCENCE BRIDGE): bridges the stochastic occupation lower
-- bound (occupation_unbounded_eta on the conditioned walk Ûmat=Umat/umass) to the substochastic umass.
-- umass_lt_of_occupation_unbounded: if u(t+1) ≤ u(t) − δ·u(t)·g(t) (conditioned coalescence) and ∑g is
-- unbounded, then u falls below any ε > 0 (telescoping with u≥ε gives u M ≤ 1 − δε∑g → −1, contradiction).
-- Pure real-sequence argument; consumes occupation_unbounded_eta's output. The instantiation's key bridge.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.umass_lt_of_occupation_unbounded
-- HR mass-rate campaign, brick 96 (§8 R7 SMOOTH-SCALE window transfer): the floored rnk=⌊3√n⌋ is not an
-- approx-martingale (Θ(1) fractional-phase obstruction), so the occupation/Tanaka argument runs on the
-- SMOOTH difference 3√x − 3√y; abs_smooth_sub_le_rnk_add_one: |3√x − 3√y| ≤ |rnk x − rnk y| + 1, so a
-- rnk-window of width W transfers to a smooth window of width W+1 (constant slack). Floor arithmetic.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.abs_smooth_sub_le_rnk_add_one
-- HR mass-rate campaign, brick 97 (§8 R7 D²-ENERGY BRIDGE): the cleanest coalescence route (ChatGPT R11,
-- verified). Direct energy E t = ∑ Umat t · D² on the substochastic unmatched mass; per-row drift ≥ c
-- off-window (c = v₀−2Rη), ≥ −R² on-window (trivial). Telescoped (E ≤ R²·umass ≤ R², umass_le_one):
-- c·∑ umass ≤ R² + (c+R²)·∑ goodMass. With δ·∑goodMass ≤ 1 (brick 81), ∑ umass is BOUNDED, so umass→0
-- (rate K₀/M). No conditioned walk / occupation_unbounded_eta needed — the on-window repulsion is
-- harmless (each on-window mass unit is charged to goodMass). Reuses the QV identity sq_drift_id.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.umass_le_one
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.energy_controls_goodMass
-- HR mass-rate campaign, brick 98 (§8 R7 COALESCENCE CAPSTONE — umass → 0): combining the D²-energy
-- control (97, c·∑umass ≤ R²+(c+R²)∑goodMass) with brick 81 (δ·∑goodMass ≤ 1) bounds ∑umass ≤ K₀;
-- since umass is antitone (umass_antitone), M·umass M ≤ ∑_{t<M}umass ≤ K₀, so umass M ≤ K₀/M → 0
-- (umass_tendsto_zero, with rate). This is the COALESCENCE: the two coupled killed chains' unmatched mass
-- vanishes, i.e. overlap → 1. Reduces to concrete inputs c=v₀−2Rη>0, off-window QV, minorization (brick 79).
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.umass_antitone
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.umass_tendsto_zero
-- HR mass-rate campaign, brick 99 (§8 R7 ONE-SIDED/LOCALIZED lower QV): for the conditioned residual
-- walk the drift is not uniformly small (on-window repelling), but the QV lower bound needs only the
-- one-sided D·e ≥ −Rη (off-window ≥ −Rη from product mart-eta; on-window ≥ 0 from repulsion). So
-- sq_moment_ge_onesided: E[D_T²] ≥ E[D_0²] + (v₀−2Rη)·T survives without uniform mart-eta — the
-- localization needed to run the occupation argument on the conditioned walk (R12 route). Finite-sum.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.sq_drift_ge_onesided
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.sq_moment_ge_onesided
-- HR mass-rate campaign, brick 100 (§8 R7 LOCALIZED Tanaka, off-window drift): the |D|-drift Tanaka bound
-- E|D_T| − E|D_0| ≤ b·(window occ) + η·T holds needing the drift ≤ η only OFF the window (b < |D x|);
-- on-window the per-step |D|-drift is ≤ b regardless (triangle), so the on-window repelling drift of the
-- conditioned walk is harmless. occupation_ge_tanaka_loc + abs_drift_le_indic_off. With the one-sided QV
-- (99), this localizes the occupation argument to the conditioned residual walk (R12 route). Finite-sum.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.abs_drift_le_indic_off
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.occupation_ge_tanaka_loc
-- HR mass-rate campaign, brick 101 (§8 R7 LOCALIZED OCCUPATION CAPSTONE): occupation_unbounded_loc —
-- for a kernel with one-sided QV (D·e ≥ −Rη), off-window drift ≤ η, uniform locVar ≥ v₀, |D| ≤ R,
-- 0 < v₀−2Rη, the window occupation exceeds any target. Paley–Zygmund with E[D_M²] ≥ (v₀−2Rη)M (brick 99)
-- and E[D_M⁴] ≤ R⁴ gives E|D_M| ~ M^{3/2}, then localized Tanaka (brick 100) forces occ past any target.
-- This is the conditioned-walk recurrence in abstract form; over the active phase (M ~ r → ∞) it gives
-- the killed-chain coalescence. Reduces to the concrete Erdős moments (η~1/r², v₀, b) + active-time→∞.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.occupation_unbounded_loc
-- HR mass-rate campaign, brick 102 (§8 R7 GoodHi umass recursion): the killed-chain minorization δ ≤ cmass
-- holds only on the active high-rank window GoodHi (brick 79), not on absorbed pairs. umass_succ_le_of_good
-- generalizes brick 81's per-step contraction to any sub-predicate Good with δ ≤ cmass on Good:
-- umass(t+1) ≤ umass t − δ·(Good-mass of Umat t), from umass_succ_eq (∑Umat·cmass ≥ δ·∑_{Good}Umat).
-- Feeds CoalesceBridge with g = conditioned Good-fraction. Deterministic finite-sum.
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.umass_succ_le_of_good
-- HR mass-rate campaign, brick 103 (§8 R7 two-term ⟹ local Lipschitz bridge): two_term_local_lip —
-- if f n = c₀ + c₁/√n + O(1/n) eventually, then for comparable large x,y (|√x−√y| ≤ W0),
-- |f x − f y| ≤ K'/x = O(1/r²). The bridge from the smooth-rank mean-decrement two-term expansion to the
-- approximate-martingale bound η~1/r². (Drafted during the no-build window, verified on server recovery.)
#print axioms AnalyticCombinatorics.Ch8.Partitions.Erdos.two_term_local_lip

end AnalyticCombinatorics.Ch1
