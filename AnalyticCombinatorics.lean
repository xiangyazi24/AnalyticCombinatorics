-- Analytic Combinatorics — Lean 4 Formalization
-- Flajolet & Sedgewick (2009)
-- github.com/xiangyazi24/AnalyticCombinatorics

-- ┌─────────────────────────────────────────┐
-- │  Part A: Symbolic Method                │
-- └─────────────────────────────────────────┘
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Sequences
import AnalyticCombinatorics.PartA.Ch2.LabelledClass
import AnalyticCombinatorics.PartA.Ch3.Parameters

-- ┌─────────────────────────────────────────┐
-- │  Part B: Complex Asymptotics            │
-- └─────────────────────────────────────────┘
-- import AnalyticCombinatorics.PartB.Ch4.MeromorphicGF    -- rational/meromorphic, todo
-- import AnalyticCombinatorics.PartB.Ch5.Applications     -- todo
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
import AnalyticCombinatorics.Examples.Compositions
import AnalyticCombinatorics.Examples.IntegerPartitions
import AnalyticCombinatorics.Examples.Fibonacci
import AnalyticCombinatorics.Examples.Tribonacci
import AnalyticCombinatorics.Examples.Padovan
import AnalyticCombinatorics.Examples.SetPartitions
import AnalyticCombinatorics.Examples.Derangements
import AnalyticCombinatorics.Examples.CyclicPermutations
import AnalyticCombinatorics.Examples.SchroderTrees
