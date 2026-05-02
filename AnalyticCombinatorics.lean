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
import AnalyticCombinatorics.PartA.Ch1.Newton
import AnalyticCombinatorics.PartA.Ch1.IntPartTheory
import AnalyticCombinatorics.PartA.Ch1.LatticePaths
import AnalyticCombinatorics.PartA.Ch1.Multiset
import AnalyticCombinatorics.PartA.Ch1.Powerset
import AnalyticCombinatorics.PartA.Ch1.Cycle
import AnalyticCombinatorics.PartA.Ch1.CatalanBijections
import AnalyticCombinatorics.PartA.Ch1.UnlabelledStructures
import AnalyticCombinatorics.PartA.Ch1.GeneralTrees
import AnalyticCombinatorics.PartA.Ch2.LabelledClass
import AnalyticCombinatorics.PartA.Ch2.LabelledTrees
import AnalyticCombinatorics.PartA.Ch2.Surjections
import AnalyticCombinatorics.PartA.Ch2.Derangements
import AnalyticCombinatorics.PartA.Ch2.BellNumbers
import AnalyticCombinatorics.PartA.Ch2.Involutions
import AnalyticCombinatorics.PartA.Ch2.CycleIndex
import AnalyticCombinatorics.PartA.Ch2.SetCycleOps
import AnalyticCombinatorics.PartA.Ch3.Parameters
import AnalyticCombinatorics.PartA.Ch3.Moments

-- ┌─────────────────────────────────────────┐
-- │  Part B: Complex Asymptotics            │
-- └─────────────────────────────────────────┘
import AnalyticCombinatorics.PartB.Ch4.RationalGF
import AnalyticCombinatorics.PartB.Ch4.MeromorphicCoeff
-- import AnalyticCombinatorics.PartB.Ch5.Applications     -- todo
import AnalyticCombinatorics.PartB.Ch6.Asymptotics
import AnalyticCombinatorics.PartB.Ch6.DeltaDomain
import AnalyticCombinatorics.PartB.Ch6.TransferTheorems
-- import AnalyticCombinatorics.PartB.Ch7.Applications     -- todo
-- import AnalyticCombinatorics.PartB.Ch8.SaddlePoint      -- todo

-- ┌─────────────────────────────────────────┐
-- │  Examples                               │
-- └─────────────────────────────────────────┘
import AnalyticCombinatorics.Examples.BinaryTrees
import AnalyticCombinatorics.Examples.MotzkinTrees
import AnalyticCombinatorics.Examples.PlaneTrees
import AnalyticCombinatorics.Examples.DyckPaths
import AnalyticCombinatorics.Examples.Triangulations
import AnalyticCombinatorics.Examples.CatalanFamily
import AnalyticCombinatorics.Examples.Strings
import AnalyticCombinatorics.Examples.StringsNoConsecutiveOnes
import AnalyticCombinatorics.Examples.Compositions
import AnalyticCombinatorics.Examples.CompositionsOdd
import AnalyticCombinatorics.Examples.CompositionsEven
import AnalyticCombinatorics.Examples.IntegerPartitions
import AnalyticCombinatorics.Examples.Fibonacci
import AnalyticCombinatorics.Examples.Tribonacci
import AnalyticCombinatorics.Examples.Tetranacci
import AnalyticCombinatorics.Examples.Padovan
import AnalyticCombinatorics.Examples.SetPartitions
import AnalyticCombinatorics.Examples.Surjections
import AnalyticCombinatorics.Examples.Derangements
import AnalyticCombinatorics.Examples.CyclicPermutations
import AnalyticCombinatorics.Examples.SchroderTrees
