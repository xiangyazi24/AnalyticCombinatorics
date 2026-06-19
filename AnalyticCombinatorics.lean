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
import AnalyticCombinatorics.Ch1.OGF.CycleModel
import AnalyticCombinatorics.Ch1.OGF.CycleBurnside
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
import AnalyticCombinatorics.Ch2.EGF.LabelledCycExp
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
import AnalyticCombinatorics.Ch5.ContinuedFractions.FlajoletUnbounded
import AnalyticCombinatorics.Ch5.ContinuedFractions.FlajoletPathBijection
import AnalyticCombinatorics.Ch5.ContinuedFractions.FlajoletStepPath
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
import AnalyticCombinatorics.Ch8.Partitions.MassRateRiemann
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
import AnalyticCombinatorics.Ch8.Partitions.CeilingValueWindow
import AnalyticCombinatorics.Ch8.Partitions.CeilingCompose
import AnalyticCombinatorics.Ch8.Partitions.ErdosCeilingLimit
import AnalyticCombinatorics.Ch8.Partitions.StepContractionConst
import AnalyticCombinatorics.Ch8.Partitions.RenewalMultiB
import AnalyticCombinatorics.Ch8.Partitions.ErdosRenewalConnectMultiB
import AnalyticCombinatorics.Ch8.Partitions.RenewalAlign
import AnalyticCombinatorics.Ch8.Partitions.ErdosAlignConnect
import AnalyticCombinatorics.Ch8.Partitions.ScalarRecSolve
import AnalyticCombinatorics.Ch8.Partitions.ITERCoupling
import AnalyticCombinatorics.Ch8.Partitions.KhatRes
import AnalyticCombinatorics.Ch8.Partitions.FKBlockBridge
import AnalyticCombinatorics.Ch8.Partitions.FKHittingBridge
import AnalyticCombinatorics.Ch8.Partitions.FKPartitionBridge
import AnalyticCombinatorics.Ch8.Partitions.FKPartitionHitting
import AnalyticCombinatorics.Ch8.Partitions.ActiveDomain
import AnalyticCombinatorics.Ch8.Partitions.ActiveCoupling
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
import AnalyticCombinatorics.Ch4.Analytic.Bridge
import AnalyticCombinatorics.Ch4.Analytic.Poles
import AnalyticCombinatorics.Ch4.Analytic.Rational
import AnalyticCombinatorics.Ch4.Analytic.Fibonacci
import AnalyticCombinatorics.Ch4.Analytic.SingularityInteger
import AnalyticCombinatorics.Ch4.Analytic.LogTransfer
import AnalyticCombinatorics.Ch4.Analytic.ComplexLogSeries
import AnalyticCombinatorics.Ch4.Analytic.LogTransferBranch
import AnalyticCombinatorics.Ch4.Analytic.LogFaithful
import AnalyticCombinatorics.Ch4.Analytic.LogTransferNatural
import AnalyticCombinatorics.Ch4.Analytic.OneSubCpowMul
import AnalyticCombinatorics.Ch4.Analytic.LogSqSingularity
import AnalyticCombinatorics.Ch4.Analytic.LogSqCoeff
import AnalyticCombinatorics.Ch4.Analytic.LogKCoeff
import AnalyticCombinatorics.Ch4.Analytic.LogKFaithful
import AnalyticCombinatorics.Ch4.Analytic.LogKAsymp
import AnalyticCombinatorics.Ch4.Analytic.LogKTransferNatural
import AnalyticCombinatorics.Ch4.Analytic.LogAlphaOneTransfer
import AnalyticCombinatorics.Ch4.Analytic.LogSqTransfer
import AnalyticCombinatorics.Ch4.Analytic.LogSqTransferNatural
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
import AnalyticCombinatorics.Ch4.Analytic.ModelCoeffExplicit
import AnalyticCombinatorics.Ch4.Analytic.ModelCoeffSecondOrder
import AnalyticCombinatorics.Ch4.Analytic.TransferSecondOrder
import AnalyticCombinatorics.Ch4.Analytic.TransferSecondOrderAlphaLt1
import AnalyticCombinatorics.Ch4.Analytic.TransferSecondOrderGeneral
import AnalyticCombinatorics.Ch7.SingularityApp.TwoRegularSecondOrder
import AnalyticCombinatorics.Ch7.SingularityApp.MotzkinSecondOrder
import AnalyticCombinatorics.Ch7.SingularityApp.CatalanSecondOrder
import AnalyticCombinatorics.Ch7.SingularityApp.SchroederSecondOrder
import AnalyticCombinatorics.Ch7.SingularityApp.RiordanSecondOrder
import AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeSecondOrder
import AnalyticCombinatorics.Ch7.SingularityApp.CayleySecondOrder
import AnalyticCombinatorics.Ch7.SingularityApp.CayleyThirdOrder
import AnalyticCombinatorics.Ch7.SingularityApp.FussCatalanGeneralThirdOrder
import AnalyticCombinatorics.Ch7.SingularityApp.CatalanThirdOrder
import AnalyticCombinatorics.Ch7.SingularityApp.MotzkinThirdOrder
import AnalyticCombinatorics.Ch7.SingularityApp.SchroederThirdOrder
import AnalyticCombinatorics.Ch7.SingularityApp.RiordanThirdOrder
import AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeThirdOrder
import AnalyticCombinatorics.Ch4.Analytic.ModelCoeffThirdOrder
import AnalyticCombinatorics.Ch4.Analytic.SqrtSingularitySecondOrder
import AnalyticCombinatorics.Ch4.Analytic.SqrtSingularityThirdOrder
import AnalyticCombinatorics.Ch8.SaddlePoint.GaussianMoments
import AnalyticCombinatorics.Ch8.SaddlePoint.SecondOrderCore
import AnalyticCombinatorics.Ch8.SaddlePoint.SecondOrderHAdmissible
import AnalyticCombinatorics.Ch8.SaddlePoint.InvolutionSecondOrder
import AnalyticCombinatorics.Ch8.SaddlePoint.BellSecondOrder
import AnalyticCombinatorics.Ch8.SaddlePoint.Blocks3SecondOrder
import AnalyticCombinatorics.Ch8.SaddlePoint.FragmentedPermHAdmissible
import AnalyticCombinatorics.Ch8.SaddlePoint.FragmentedPermSecondOrder
import AnalyticCombinatorics.Ch8.SaddlePoint.Bound
import AnalyticCombinatorics.Ch8.SaddlePoint.Assembly
import AnalyticCombinatorics.Ch8.SaddlePoint.GaussianCore
import AnalyticCombinatorics.Ch8.SaddlePoint.ExpStirling
import AnalyticCombinatorics.Ch8.SaddlePoint.Exp
import AnalyticCombinatorics.Ch8.SaddlePoint.Bell
import AnalyticCombinatorics.Ch8.SaddlePoint.BellBridge
import AnalyticCombinatorics.Ch8.SaddlePoint.HAdmissible
import AnalyticCombinatorics.Ch8.SaddlePoint.ExpHAdmissible
import AnalyticCombinatorics.Ch8.SaddlePoint.BellHAdmissible
import AnalyticCombinatorics.Ch8.SaddlePoint.BellRealSaddle
import AnalyticCombinatorics.Ch8.SaddlePoint.InvolutionRealSaddle
import AnalyticCombinatorics.Ch8.SaddlePoint.Blocks3RealSaddle
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
import AnalyticCombinatorics.Ch7.SingularityApp.CycleMarkedPermPairBoth
import AnalyticCombinatorics.Ch7.SingularityApp.UndirectedCycleMarkedPermTuple
import AnalyticCombinatorics.Ch7.SingularityApp.UndirectedCycleLogSqPermPair
import AnalyticCombinatorics.Ch7.SingularityApp.CycleMarkedPermLpow
import AnalyticCombinatorics.Ch7.SingularityApp.CycleMarkedPermHarmonic
import AnalyticCombinatorics.Ch7.SingularityApp.UndirectedCycleLogKPermLpow
import AnalyticCombinatorics.Ch5.Meromorphic.LabelledCycleCount
import AnalyticCombinatorics.Ch7.SingularityApp.Schroeder
import AnalyticCombinatorics.Ch7.SingularityApp.Riordan
import AnalyticCombinatorics.Ch7.SingularityApp.TreeFunction
import AnalyticCombinatorics.Ch7.SingularityApp.Forests
import AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeBasic
import AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeRecurrence
import AnalyticCombinatorics.Ch7.SingularityApp.TernaryFussCatalan
import AnalyticCombinatorics.Ch7.SingularityApp.LabeledTreeBasic
import AnalyticCombinatorics.Ch7.SingularityApp.Cayley
import AnalyticCombinatorics.Ch7.SingularityApp.RootedLTree
import AnalyticCombinatorics.Ch7.SingularityApp.TernaryLagrange
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
import AnalyticCombinatorics.Ch9.LimitLaws.TotalCycleSecondMoment
import AnalyticCombinatorics.Ch9.LimitLaws.TotalCycleVariance
import AnalyticCombinatorics.Ch9.LimitLaws.PermCycleCountBridge
import AnalyticCombinatorics.Ch9.LimitLaws.CompositionParts
import AnalyticCombinatorics.Ch8.Partitions.CenterTrackingHitVal
import AnalyticCombinatorics.Ch8.Partitions.RankDropTailMaj
import AnalyticCombinatorics.Ch8.Partitions.RankDropDeepMass
import AnalyticCombinatorics.Ch8.Partitions.EnterBandAdditiveEscape
import AnalyticCombinatorics.Ch8.Partitions.CeilingEscapeClose
import AnalyticCombinatorics.Ch8.Partitions.ErdosHRConstant
-- Hardy–Ramanujan exact constant `a = 1/(4√3)` (bricks 2–5, unconditional in the Riemann error)
import AnalyticCombinatorics.Ch8.Partitions.ErdosRiemannError
import AnalyticCombinatorics.Ch8.Partitions.SoftTailDrift
import AnalyticCombinatorics.Ch8.Partitions.OccupationTransfer
import AnalyticCombinatorics.Ch8.Partitions.TentDefect
import AnalyticCombinatorics.Ch8.Partitions.VarianceLower
import AnalyticCombinatorics.Ch8.Partitions.VarianceConcrete
import AnalyticCombinatorics.Ch8.Partitions.GreenLowerWall
import AnalyticCombinatorics.Ch8.Partitions.CentralBinomSum
import AnalyticCombinatorics.Ch8.Partitions.GreenBridge
import AnalyticCombinatorics.Ch8.Partitions.TruncationTransfer
import AnalyticCombinatorics.Ch8.Partitions.GreenComparison
import AnalyticCombinatorics.Ch8.Partitions.GreenForm
import AnalyticCombinatorics.Ch8.Partitions.DirichletForm
import AnalyticCombinatorics.Ch8.Partitions.SymmetricDirichlet
import AnalyticCombinatorics.Ch8.Partitions.Ellipticity
import AnalyticCombinatorics.Ch8.Partitions.SectorPoincare
import AnalyticCombinatorics.Ch8.Partitions.SectorBound
import AnalyticCombinatorics.Ch8.Partitions.SectorBoundDivergence
import AnalyticCombinatorics.Ch8.Partitions.DProjection

/-!
# AnalyticCombinatorics

Faithful Lean 4 formalization of Flajolet & Sedgewick, *Analytic Combinatorics*.

Rebuilt from scratch (2026-05-30) after the prior auto-generated tree was found
to be an integrity failure (trivial-impostor template across all files). The old
state is archived at branch `archive/impostor-2026-05` / tag
`archive-impostor-2026-05-30`.

Discipline (formalization-playbook):
- NO `axiom`, NO `native_decide`, NO `def : Prop` to evade `sorry` counting,
  NO smuggling the conclusion into the hypotheses.
- Every theorem must faithfully state the book's theorem (statement fidelity).
- `#print axioms` must show only `{propext, Classical.choice, Quot.sound}`.

## Part A, Chapter I — Symbolic method (OGF)

- `Ch1.OGF.Defs` — counting-sequence OGF, `CombClass`, primitive classes
  (`∅`, `ε`, `Z`) with `ε(z) = 1`, `Z(z) = z`.
- `Ch1.OGF.Sum` — combinatorial sum: `(B + C)(z) = B(z) + C(z)`.
- `Ch1.OGF.Product` — Cartesian product: `(B × C)(z) = B(z) · C(z)`.
- `Ch1.OGF.Sequence` — sequence construction; `(SEQ C)ₙ = ∑_c ∏ᵢ C_{cᵢ}`;
  integer compositions as sequences of positive integers (`= 2^{n-1}`).
- `Ch1.OGF.Compositions` — OGF of integer compositions: `C(z)·(1 - 2z) = 1 - z`.
- `Ch1.OGF.SeqFormula` — `ℙ(z) = z/(1-z)`; the sequence formula for compositions
  `C(z)·(1 - ℙ(z)) = 1` (the end-to-end symbolic-method example).
- `Ch1.OGF.ProductPower` — Cartesian power `(C^k)(z) = C(z)^k`; words of length
  `k` over an `a`-letter alphabet, OGF `(a z)^k`.
- `Ch1.OGF.SequenceInverse` — the general sequence construction: for `C₀ = ∅`,
  the functional equation `S = 1 + C·S` and `(seq C)(z)·(1 - C(z)) = 1`.
- `Ch1.OGF.SeqApplications` — words over a finite alphabet (`a^n` words, OGF
  `1/(1 - a z)`); compositions as a special case of the sequence transfer.
- `Ch1.OGF.Fibonacci` — compositions into parts `1,2` are counted by `F_{n+1}`,
  with OGF `1/(1 - z - z²)`.
- `Ch1.OGF.Partitions` — integer partitions (MSET flagship): Euler's product
  `P(z) = ∏_{m≥1} 1/(1 - z^m)`, via Mathlib's `Nat.Partition.genFun`.
- `Ch1.OGF.Mset` — general multiset construction `MSET(C)`: counts layer
  `MSET(C)ₙ = ∑_p ∏_m multichoose(Cₘ, mult_m p)`, and the Euler product OGF
  `MSET(C)(z) = ∏_{m≥1} (1 - z^m)^{-Cₘ}`.
- `Ch1.OGF.Pset` — general powerset construction `PSET(C)`: sets of C-objects, with
  `PSET(C)(z) = ∏_{m≥1} (1 + z^m)^{Cₘ}`.
- `Ch1.OGF.DistinctPartitions` — partitions into distinct parts `= PSET(ℙ)`, with
  generating function `∏_{m≥1} (1 + z^m)`.
- `Ch1.OGF.Pointing` — the pointing construction `Θ(C)(z) = z·C'(z)` (counts `n·Cₙ`).

## Part A, Chapter II — Labelled structures (EGF)

- `Ch2.EGF.Defs` — exponential generating functions `A(z) = ∑ Aₙ zⁿ/n!`;
  permutations (`1/(1-z)`) and the set class (`e^z`).
- `Ch2.EGF.LabelledProduct` — the labelled product: `(A ⋆ B)(z) = A(z)·B(z)`
  (binomial convolution `(A⋆B)ₙ = ∑ₖ C(n,k)·Aₖ·B_{n-k}`).
- `Ch2.EGF.LabelledSum` — the labelled sum: `(A + B)(z) = A(z) + B(z)`.
- `Ch2.EGF.LabelledPower` — labelled power `(C^{⋆k})(z) = C(z)^k`.
- `Ch2.EGF.LabelledSet` — labelled set construction `SET(C)` (counts layer):
  `SET(C)ₙ = ∑_π ∏_{B∈π} C_{|B|}` over set partitions.
- `Ch2.EGF.SetExp` — ODE machinery toward `SET(C)(z)=exp(C(z))`: `exp(C(z))` solves
  `F'=C'·F`, and that ODE has a unique solution.
- `Ch2.EGF.LabelledSetOde` — the combinatorial ODE `SET(C)'=C'·SET(C)` (pointing
  bijection on set partitions); the recurrence `SET_{n+1}=∑ C(n,i)·C_{i+1}·SET_{n-i}`.
- `Ch2.EGF.LabelledSetExp` — **`SET(C)(z) = exp(C(z))`** (the exponential formula),
  via the ODE + uniqueness.
- `Ch2.EGF.LabelledSeq` — labelled sequence: `SEQ(C)(z)·(1 - C(z)) = 1`, i.e. `1/(1-C(z))`.
- `Ch2.EGF.Applications` — Bell `exp(e^z-1)`; surjections `1/(2-e^z)`; involutions `exp(z+z²/2)`.
- `Ch2.EGF.LabelledCyc` — the labelled cycle construction `CYC(C)' = C'·SEQ(C)`
  (= `C'(z)/(1-C(z))`, i.e. `log(1/(1-C(z)))`), with `CYC(0)=0` (ODE characterization).

## Part A, Chapter III — Combinatorial parameters (bivariate GF)

- `Ch3.BGF.Defs` — parameterized classes; bivariate GF `F(z,u)=∑ b_{n,k} z^n u^k`
  over `ℚ[u]⟦z⟧`; sum/product transfers; `evalU 1 = OGF`.
- `Ch3.BGF.Moments` — mean via `∂_u` at `u=1`; compositions-by-#parts flagship.
- `Ch3.BGF.Variance` — variance (2nd factorial/raw moment); closed bivariate GF of
  compositions by #parts `(1-z)/(1-(1+u)z)`.

Modules are added here as they are proved.
-/
