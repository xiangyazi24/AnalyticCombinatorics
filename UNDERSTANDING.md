# AnalyticCombinatorics — UNDERSTANDING.md

## 项目概况

Lean 4 形式化项目，对 Flajolet & Sedgewick《Analytic Combinatorics》忠实形式化。
**2026-05-30 起从零重建**（旧树判为整库 IMPOSTOR，见下）。目标：完成全书，以通过
formalization-playbook 三组验收（audit）为准。

**Lean 4 v4.29.0 + Mathlib v4.29.0**，lake 构建。

## 为什么重建

旧树（1283 文件 / ~264k 行 / 自称"全书完成 0 sorry"）经 /lean playbook 三组验收审计，
判定为**整库 IMPOSTOR**：机械全绿（能编译、无 sorry），但没有一条定理忠实陈述书里的
结果。全部文件建在编造的 `Window/budget/certificate/slack/Ready` 模板上，含约 1.7 万处
`native_decide`。旧树存档于分支 `archive/impostor-2026-05` / tag `archive-impostor-2026-05-30`。

## 纪律（formalization-playbook）

- 禁 `axiom`、禁 `native_decide`、禁用 `def : Prop` 规避 sorry 计数、禁把结论塞进假设。
- 每条定理对照原书做 statement fidelity 检查。每个 headline `#print axioms` 必须只有
  `{propext, Classical.choice, Quot.sound}`。
- 每条结果标 verdict：FAITHFUL / CONDITIONAL-honest / FRAGMENT / IMPOSTOR。

## 当前真实覆盖（2026-06-03 实测，非旧 UNDERSTANDING 的"只完成 Ch I"）

74 个 .lean 文件，0 真实 sorry，全库 build green（8322 jobs）。仓库章节↔F&S 映射：

| 仓库 | F&S | 内容 | 状态 |
|------|-----|------|------|
| Ch1/OGF (19 文件) | Ch I | 符号方法 OGF：sum/prod/seq/mset/pset/cyc/compositions/partitions/pointing | 扎实 |
| Ch2/EGF (11 文件) | Ch II | labelled 结构 EGF：lprod/lsum/lset/lseq/lcyc/set-ODE/Bell/surjections/involutions | 扎实 |
| Ch3/BGF (10 文件) | Ch III | 参数/双变量 BGF：moments/variance/marked seq+set/compositions+binary-words moments | 扎实 |
| Ch4/Analytic (27 文件) | Ch IV+VI | 复分析+奇点分析：Pringsheim、Rational(partial-fraction)、Poles/RepeatedPole、Catalan/CentralBinomial/Fibonacci/Derangements 渐近、Transfer VI.3(general α)、Δ-domain/Cauchy/kernel estimates | 扎实 |
| Ch8/SaddlePoint (8 文件) | Ch VIII | saddle-point：exp/Stirling 无条件渐近(FAITHFUL)、Hayman H-admissible transfer(CONDITIONAL-honest，通用接口暂无实例) | 良好 |

### 2026-06-04 新增（本次自主 run，均 FAITHFUL、audit-clean、build-green）

- **Ch5/Meromorphic** (F&S Ch V)：`Transfer`（IV.10 通用 meromorphic coefficient transfer：解析余项
  O(R^{-n}) via Cauchy + dominant simple pole 渐近）；`Surjections`（满射/Fubini 数 `r_n/n! ~
  1/(2(log2)^{n+1})`，transcendental remainder 经 dslope 可去奇点延拓攻克）。
- **Ch7/SingularityApp** (F&S Ch VI/VII)：`TernaryTrees`、`Motzkin`（`~(3√3/2√π)3^n n^{-3/2}`，4-brick
  硬战，v1 vacuous impostor 被打回）、`FussCatalan`（通用 p-ary，含 Catalan/ternary 实例，Lean 内证
  一致性）、`FussCatalanInstances`（p=4/5/6 特化）、`TwoRegular`（`g_n/n!~e^{-3/4}/√(πn)`，**注：count
  由 EGF 定义 = GF-系数级保真，非组合定义**）。
- **Ch9/LimitLaws** (F&S Ch IX)：`QuasiPowers`（Hwang IX.8 Gaussian 极限律，**局部 hChar** = 忠实
  Hwang，经 Mathlib `ProbabilityMeasure.tendsto_iff_tendsto_charFun` Levy 连续性定理）；`BinaryWordCLT`
  （二进制词 1 数 →d N(0,1)，无条件实例）；`PermutationCycles`（环数 →d N(0,1) Goncharov，Feller 耦合
  实现）。

### 仍缺（whole-book 前沿，多 session）

- **F&S Ch V/VII 更多应用**：alignments、supercritical 序列/合成 schema、更多树族；基础（meromorphic
  + 通用 transfer 覆盖全 α）已在。
- **F&S Ch IX**：quasi-powers 框架 + 2 实例已在；缺 supercritical-composition Gaussian、连续极限律、
  多元。composition-parts CLT 已排队（codex 待恢复）。
- **硬 saddle/circle-method**：Bell/involutions/Hardy-Ramanujan 分拆渐近（各自多 brick 战役）。
- **Appendices A/B/C**：缺（多数 Mathlib 已覆盖）。

### Fidelity 纪律（本 run 教训）

- trust-but-verify 揪出 2 个保真度缺陷：Motzkin v1 = vacuous impostor（hp∧hsing 互相矛盾，永不可
  实例化）；quasi-powers v1 hChar = over-strong 全局 exp 等式（对格点分布不可满足，`charFun π=0` 反例）。
  二者均诚实降级后修复。**"0 blocked + lake env lean 通过" ≠ FAITHFUL，必检 statement fidelity。**
- 偏好真组合定义（surjections=lseq.counts、ternary/Motzkin/Fuss-Catalan=显式/递推、cycles=Feller）。
  2-regular 漂移成 GF-系数定义，已标注；后续 brick 应 re-anchor 到真 count。

### Audit 备注

- Ch8 `exp_coeff_isEquivalent_saddle` = FAITHFUL 无条件（exp/Stirling），有完整 central+tail 证明。
- Ch8 `coeff_isEquivalent_saddle`（HAdmissible 结构）= CONDITIONAL-honest 通用 transfer，
  目前无 concrete 实例（无任一函数证 H-admissible）。可选后续：把 exp 接入做首个实例。
- 通用 H-admissibility 实例验证 = 设计自标的 multi-month WALL。

## 构建与协作（git，不再 rsync）

- GitHub `xiangyazi24/AnalyticCombinatorics` 是 source of truth。本地 commit→push；uisai1
  `git pull`。uisai1 是 git checkout（.lake 7.5G 缓存保留），不再用 rsync。
- 远端构建：`ssh uisai1 'cd ~/repos/AnalyticCombinatorics && export PATH=$HOME/.elan/bin:$PATH &&
  nohup lake build <Module> > /tmp/ac-build.log 2>&1 &'`。Mathlib 源码可 grep：
  `.lake/packages/mathlib/Mathlib`。
- Codex worker（master-worker / 分头打）：`codex exec --dangerously-bypass-approvals-and-sandbox
  --skip-git-repo-check -m gpt-5.5 "<spec>"`，nohup 到 /tmp，reply 写 `HANDOFF/outbox/*-reply.md`。
  一个文件一个写者；agent 只建自己的新文件，不碰 `AnalyticCombinatorics.lean`/`Audit.lean`
  （import 图 + `#print axioms` 由 master 自己 wire）。agent 自验只用 `lake env lean <file>`，
  不在 agent 编辑期间 `lake build`。
- Audit 文件：`AnalyticCombinatorics/Ch1/OGF/Audit.lean`（规范，自带 import 列表，每个新 headline
  加一行 `#print axioms`）。

## 进行中

- Ch5/Meromorphic coefficient transfer（F&S IV.10）：codex 在建，3 sub-bricks
  （解析余项 O(R^{-n}) → 减极点 transfer → dominant simple pole 渐近）。
