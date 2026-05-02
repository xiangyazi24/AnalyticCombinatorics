# AnalyticCombinatorics — UNDERSTANDING.md

## 项目概况

Lean 4 形式化项目，对 Flajolet & Sedgewick《Analytic Combinatorics》Part A 的核心构造进行形式化验证。

**Repo:** `~/repos/AnalyticCombinatorics` (GitHub: xiangyazi24/AnalyticCombinatorics)
**Lean 4 + Mathlib**，lake 构建。

## 当前工作：Sanity Check 批量扩展

通过 `handoff-dispatch.sh codex` 批量派 codex agent，每次 5 个并行，每个负责一个序列的 sanity check 扩展。

### 工作流

1. 写 task 文件到 `HANDOFF/inbox/task-<name>.md`
2. `~/.openclaw/scripts/handoff-dispatch.sh codex HANDOFF/inbox/task-<name>.md`
3. codex 修改 .lean 文件，写 reply 到 `HANDOFF/outbox/task-<name>-reply.md`
4. 我 `lake build` 验证 → `git add` → `git commit` → `git push`
5. 移动 inbox/outbox → `HANDOFF/done/`
6. 派下一批

### 已知问题

- **codex sandbox 落盘不稳定**：codex exec --full-auto 的写入有时不持久化到实际文件系统。表现为 log 里有 diff 但 `git diff` 为空。等一会儿通常会出现（延迟落盘）。
- **Stale build cache**：并行写入后首次 `lake build` 可能报错（olean 找不到），重跑一次通常过。
- **大数值错误**：codex 给出的大组合数有时不对（Bell(23)、Derange(25-27) 等）。Lean 的 `native_decide` 会 catch 住。遇到就删掉错误条目重新跑。
- **native_decide 超时**：IntegerPartitions 在 n≥22 超时（Mathlib Nat.Partition Fintype 效率问题）。各序列超时阈值不同。

### 当前各序列 max_n（截至 batch 9 push）

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
| IntPartitions | 30 (上限) | IntegerPartitions.lean |

### Batch 9 已提交（2026-05-02）

Bell 28, OddComp 27, Surj 26, Derange 30, Strings 25 — 全部验证通过。

### Chapter Theory Batch 1 已提交（2026-05-02）

| 文件 | 行数 | 内容 |
|------|------|------|
| PartA/Ch1/Multiset.lean | 275 | MSET 构造 + 整数分拆 sanity |
| PartA/Ch1/Powerset.lean | 251 | PSET 构造 + twoAtoms sanity |
| PartA/Ch1/Cycle.lean | 144 | CYC(Atom) = (n-1)!, EGF = -log(1-z) |
| PartA/Ch1/Trees.lean | 270 | BinaryTree, T=1+zT², Catalan sanity |
| PartA/Ch2/LabelledTrees.lean | 111 | Cayley n^{n-1}, Prüfer, EGF |
| PartA/Ch3/Parameters.lean | +59 | bgf, cumulatedCost, meanParam |
| PartA/Ch2/LabelledClass.lean | +119 | permutation fixed-point sanity |

### Chapter Theory Batch 2 已提交（2026-05-02）

| 文件 | 行数 | 内容 |
|------|------|------|
| PartA/Ch1/PlaneTrees.lean | 269 | PlaneTree T=z/(1-T), shifted Catalan |
| PartA/Ch1/StringsTheory.lean | 403 | k^n strings + no-11 = Fibonacci |
| PartA/Ch1/Newton.lean | 126 | OGF uniqueness, Newton bootstrap |
| PartA/Ch1/IntPartTheory.lean | 234 | Euler odd=distinct, oddPartCount |
| PartA/Ch1/LatticePaths.lean | 249 | dyckCount = centralBinom/(n+1) |
| PartA/Ch2/Surjections.lean | +185 | EGF coefficient theorem |
| PartA/Ch2/Derangements.lean | 46 | Recursion + perm = set * derange |

### Chapter Theory Batch 3 已提交（2026-05-02）

| 文件 | 行数 | 内容 |
|------|------|------|
| PartA/Ch1/MotzkinTrees.lean | 288 | 一元-二元树 M=z(1+M+M²), sanity 1,1,2,4,9 |
| PartA/Ch1/SchroederTheory.lean | 79 | 大 Schröder 数 S=1+zS+zS², sanity 1,2,6,22,90 |
| PartA/Ch2/SetCycleOps.lean | 211 | SET/CYCLE EGF operators, involutions |

### Chapter Theory Batch 4 已提交（2026-05-02）

| 文件 | 行数 | 内容 |
|------|------|------|
| PartA/Ch1/CatalanBijections.lean | 94 | Catalan family count equivalence (binary ↔ plane ↔ Dyck) |
| PartA/Ch1/UnlabelledStructures.lean | 92 | Unlabelled OGF transfer lemmas |
| PartA/Ch2/BellNumbers.lean | 82 | Bell number recursion + sanity 1,1,2,5,15,52 |
| PartA/Ch3/Moments.lean | 117 | Moment/variance parameter framework |
| PartB/Ch4/RationalGF.lean | 72 | Partial fraction + geometric coeff |

Also fixed: SchroederTheory (subtype sum termination), TransferTheorems (motzkinNumber same fix), Surjections (EGF extension).

### Chapter Theory Batch 5 进行中（5 tasks dispatched, 2026-05-02）

- task-involutions: Ch2 involution count + recursion + EGF statement
- task-meromorphic-gf: Ch4 rational coeff formula + linear recurrence
- task-general-trees: t-ary tree Fuss-Catalan counts
- task-singularity-asymptotics: Ch6 exponential growth verification
- task-cycle-index: Unsigned Stirling 1st kind + row sums = n!
