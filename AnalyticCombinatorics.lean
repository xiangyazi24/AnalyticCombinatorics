-- Analytic Combinatorics — Lean 4 Formalization
-- Flajolet & Sedgewick (2009)
-- github.com/xiangyazi24/AnalyticCombinatorics

-- ┌─────────────────────────────────────────┐
-- │  Part A: Symbolic Method                │
-- └─────────────────────────────────────────┘
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Sequences
import AnalyticCombinatorics.PartA.Ch1.Trees
import AnalyticCombinatorics.PartA.Ch1.PlaneTrees
import AnalyticCombinatorics.PartA.Ch1.MotzkinTrees
import AnalyticCombinatorics.PartA.Ch1.SchroederTheory
import AnalyticCombinatorics.PartA.Ch1.StringsTheory
import AnalyticCombinatorics.PartA.Ch1.WordPatterns
import AnalyticCombinatorics.PartA.Ch1.Newton
import AnalyticCombinatorics.PartA.Ch1.IntPartTheory
import AnalyticCombinatorics.PartA.Ch1.LatticePaths
import AnalyticCombinatorics.PartA.Ch1.Multiset
import AnalyticCombinatorics.PartA.Ch1.Powerset
import AnalyticCombinatorics.PartA.Ch1.Cycle
import AnalyticCombinatorics.PartA.Ch1.CatalanBijections
import AnalyticCombinatorics.PartA.Ch1.UnlabelledStructures
import AnalyticCombinatorics.PartA.Ch1.GeneralTrees
import AnalyticCombinatorics.PartA.Ch1.Necklaces
import AnalyticCombinatorics.PartA.Ch1.QAnalogs
import AnalyticCombinatorics.PartA.Ch1.SymbolicTransfer
import AnalyticCombinatorics.PartA.Ch1.CombinatorialIdentities
import AnalyticCombinatorics.PartA.Ch1.GFOperations
import AnalyticCombinatorics.PartA.Ch1.LagrangeInversion
import AnalyticCombinatorics.PartA.Ch1.GeneratingFunctions
import AnalyticCombinatorics.PartA.Ch1.WordsLanguages
import AnalyticCombinatorics.PartA.Ch1.PlanarMaps
import AnalyticCombinatorics.PartA.Ch1.FunctionalEquations
import AnalyticCombinatorics.PartA.Ch1.IntegerCompositions
import AnalyticCombinatorics.PartA.Ch2.LabelledClass
import AnalyticCombinatorics.PartA.Ch2.LabelledTrees
import AnalyticCombinatorics.PartA.Ch2.Surjections
import AnalyticCombinatorics.PartA.Ch2.Derangements
import AnalyticCombinatorics.PartA.Ch2.BellNumbers
import AnalyticCombinatorics.PartA.Ch2.Involutions
import AnalyticCombinatorics.PartA.Ch2.CycleIndex
import AnalyticCombinatorics.PartA.Ch2.RestrictedPerms
import AnalyticCombinatorics.PartA.Ch2.ExponentialFormula
import AnalyticCombinatorics.PartA.Ch2.SetCycleOps
import AnalyticCombinatorics.PartA.Ch2.Species
import AnalyticCombinatorics.PartA.Ch2.ParkingFunctions
import AnalyticCombinatorics.PartA.Ch2.AlternatingPerms
import AnalyticCombinatorics.PartA.Ch2.RandomMappings
import AnalyticCombinatorics.PartA.Ch2.AnalyticNumberTheory
import AnalyticCombinatorics.PartA.Ch2.SpecialNumbers
import AnalyticCombinatorics.PartA.Ch2.UrnsOccupancy
import AnalyticCombinatorics.PartA.Ch2.GraphEnumeration
import AnalyticCombinatorics.PartA.Ch3.Parameters
import AnalyticCombinatorics.PartA.Ch3.MultivariateGF
import AnalyticCombinatorics.PartA.Ch3.PermutationRuns
import AnalyticCombinatorics.PartA.Ch3.Moments
import AnalyticCombinatorics.PartA.Ch3.LimitLaws
import AnalyticCombinatorics.PartA.Ch3.PermutationStatistics
import AnalyticCombinatorics.PartA.Ch3.ProbabilityGF

-- ┌─────────────────────────────────────────┐
-- │  Part B: Complex Asymptotics            │
-- └─────────────────────────────────────────┘
import AnalyticCombinatorics.PartB.Ch4.RationalGF
import AnalyticCombinatorics.PartB.Ch4.MeromorphicCoeff
import AnalyticCombinatorics.PartB.Ch4.FormalPowerSeries
import AnalyticCombinatorics.PartB.Ch4.ComplexAnalysisBasics
import AnalyticCombinatorics.PartB.Ch4.AnalyticContinuation
import AnalyticCombinatorics.PartB.Ch5.CompositionsAsymptotics
import AnalyticCombinatorics.PartB.Ch5.AsymptoticEnumeration
import AnalyticCombinatorics.PartB.Ch5.CoefficientAsymptotics
import AnalyticCombinatorics.PartB.Ch5.DigitalTrees
import AnalyticCombinatorics.PartB.Ch6.MellinHarmonicSums
import AnalyticCombinatorics.PartB.Ch6.SingularityAnalysis
import AnalyticCombinatorics.PartB.Ch6.AlgebraicSingularity
import AnalyticCombinatorics.PartB.Ch6.Asymptotics
import AnalyticCombinatorics.PartB.Ch6.DeltaDomain
import AnalyticCombinatorics.PartB.Ch6.TransferTheorems
import AnalyticCombinatorics.PartB.Ch7.CatalanAsymptotics
import AnalyticCombinatorics.PartB.Ch8.SaddlePoint
import AnalyticCombinatorics.PartB.Ch8.SaddlePointApps
import AnalyticCombinatorics.PartB.Ch9.RandomStructures
import AnalyticCombinatorics.PartB.Ch9.RandomGraphs
import AnalyticCombinatorics.PartB.Ch9.Depoissonization
import AnalyticCombinatorics.PartB.Ch9.LargePowers

-- ┌─────────────────────────────────────────┐
-- │  Examples (build individually)          │
-- └─────────────────────────────────────────┘
-- Examples define standalone types that conflict with theory files.
-- Build with: lake build AnalyticCombinatorics.Examples.<Name>
