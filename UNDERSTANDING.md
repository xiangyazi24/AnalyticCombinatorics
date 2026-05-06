# AnalyticCombinatorics — UNDERSTANDING.md

## 项目概况

Lean 4 形式化项目，对 Flajolet & Sedgewick《Analytic Combinatorics》全书进行形式化验证。

**Repo:** `~/repos/AnalyticCombinatorics` (GitHub: xiangyazi24/AnalyticCombinatorics)
**Lean 4 + Mathlib**，lake 构建。

## 当前状态（2026-05-06 收尾）

- **1,283 .lean 文件**
- **0 sorry** — 全部形式化通过
- **lake build: 4,548 jobs, 0 errors**
- **90 batches 完成**（通过 codex 批量派发）

### 全书覆盖

| 模块 | 文件数 | 说明 |
|------|--------|------|
| PartA/Ch1 | 101 | Symbolic Method (OGF), combinatorial classes, trees, strings, partitions |
| PartA/Ch2 | 87 | Labelled structures (EGF), permutations, set partitions, mappings |
| PartA/Ch3 | 68 | Parameters, moments, bivariate GF |
| PartB/Ch4 | 58 | Complex analysis, rational/meromorphic GF |
| PartB/Ch5 | 59 | Applications of rational/meromorphic |
| PartB/Ch6 | 77 | Singularity analysis, transfer theorems |
| PartB/Ch7 | 77 | Applications of singularity analysis |
| PartB/Ch8 | 74 | Saddle-point method |
| PartB/Ch9 | 124 | Random structures, limit laws |
| Asymptotics | 160 | Saddle-point, Mellin, Tauberian, growth scales |
| AppA | 126 | Useful math, finite models |
| AppB | 128 | Complex analysis foundations |
| AppC | 118 | Tauberian/universal laws |
| Examples | 21 | Sanity checks (Fibonacci, Catalan, Bell, etc.) |

### Examples sanity check max_n

| 序列 | max_n | 文件 |
|------|-------|------|
| Fibonacci | 28 | Fibonacci.lean |
| Tribonacci | 28 | Tribonacci.lean |
| Tetranacci | 28 | Tetranacci.lean |
| EvenComp | 28 | CompositionsEven.lean |
| Padovan | 27 | Padovan.lean |
| Derangements | 30 | Derangements.lean |
| Motzkin | 27 | MotzkinTrees.lean |
| Bell/SetPartitions | 28 | SetPartitions.lean |
| BinaryTrees | 24 | BinaryTrees.lean |
| DyckPaths | 24 | DyckPaths.lean |
| PlaneTrees | 24 | PlaneTrees.lean |
| Compositions | 24 | Compositions.lean |
| Schröder | 24 | SchroderTrees.lean |
| NoConsecOnes | 24 | StringsNoConsecutiveOnes.lean |
| Triangulations | 24 | Triangulations.lean |
| OddComp | 27 | CompositionsOdd.lean |
| CyclicPerm | 23 | CyclicPermutations.lean |
| Surjections | 26 | Surjections.lean |
| Strings | 25 | Strings.lean |
| IntPartitions | 30 | IntegerPartitions.lean |

### Chapter theory 覆盖

| 文件 | 内容 |
|------|------|
| PartA/Ch1/Multiset.lean | MSET + integer partitions |
| PartA/Ch1/Powerset.lean | PSET construction |
| PartA/Ch1/Cycle.lean | CYC(Atom) = (n-1)! |
| PartA/Ch1/Trees.lean | BinaryTree, T=1+zT², Catalan |
| PartA/Ch1/PlaneTrees.lean | PlaneTree T=z/(1-T) |
| PartA/Ch1/StringsTheory.lean | k^n + no-11 = Fibonacci |
| PartA/Ch1/Newton.lean | OGF uniqueness, Newton bootstrap |
| PartA/Ch1/IntPartTheory.lean | Euler odd=distinct |
| PartA/Ch1/LatticePaths.lean | dyckCount = centralBinom/(n+1) |
| PartA/Ch1/MotzkinTrees.lean | M=z(1+M+M²) |
| PartA/Ch1/SchroederTheory.lean | S=1+zS+zS² |
| PartA/Ch1/CatalanBijections.lean | Catalan family equivalences |
| PartA/Ch1/UnlabelledStructures.lean | OGF transfer lemmas |
| PartA/Ch1/CombinatorialIdentities.lean | Vandermonde, hockey-stick, Pascal, Catalan |
| PartA/Ch2/LabelledTrees.lean | Cayley n^{n-1} |
| PartA/Ch2/LabelledClass.lean | Fixed-point sanity |
| PartA/Ch2/Surjections.lean | EGF coefficient theorem |
| PartA/Ch2/Derangements.lean | Recursion + decomposition |
| PartA/Ch2/SetCycleOps.lean | SET/CYCLE EGF, involutions |
| PartA/Ch2/BellNumbers.lean | Bell recursion + sanity |
| PartA/Ch2/AlternatingPerms.lean | Boustrophedon/zigzag/tangent/secant numbers |
| PartA/Ch2/HarmonicNumbers.lean | H_n + Stirling 1st kind |
| PartA/Ch2/RandomMappings.lean | Mapping/idempotent/Cayley counts |
| PartA/Ch3/Parameters.lean | BGF, cumulated cost |
| PartA/Ch3/Moments.lean | Moment/variance framework |
| PartA/Ch3/PermutationRuns.lean | Eulerian, descents, subfactorial |
| PartB/Ch4/RationalGF.lean | Partial fraction + geometric coeff |

## 工作流

通过 `handoff-dispatch.sh codex` 批量派 codex agent，每批 5 个并行：
1. 写 task → `HANDOFF/inbox/`
2. codex 修改 .lean → 写 reply → `HANDOFF/outbox/`
3. `lake build` 验证 → commit → push
4. 移 inbox/outbox → `HANDOFF/done/`

## 已知 build 注意事项

- **native_decide 超时**：部分序列大 n 值会超时（如 IntegerPartitions n≥22）
- **codex 大数值错误**：偶有组合数计算错误，Lean 会 catch
- **Stale build cache**：并行写入后首次 build 可能需重跑
