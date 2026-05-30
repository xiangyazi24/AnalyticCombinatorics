# AnalyticCombinatorics — UNDERSTANDING.md

## 项目概况

Lean 4 形式化项目，对 Flajolet & Sedgewick《Analytic Combinatorics》忠实形式化。
**2026-05-30 起从零重建。**

**Lean 4 v4.29.0 + Mathlib v4.29.0**，lake 构建。

## 为什么重建

旧树（1283 文件 / ~264k 行 / 自称"全书完成 0 sorry"）经 /lean playbook 三组验收审计，
判定为**整库 IMPOSTOR**：机械全绿（能编译、无 sorry），但没有一条定理忠实陈述书里的
结果。全部文件建在编造的 `Window/budget/certificate/slack/Ready` 模板上，含约 1.7 万处
`native_decide`（注入 `ofReduceBool`/`trustCompiler` 公理），定理多为"从自身假设投影一个
合取项"。旧树已删，存档于分支 `archive/impostor-2026-05` / tag `archive-impostor-2026-05-30`。

## 纪律（formalization-playbook）

- 禁 `axiom`、禁 `native_decide`、禁用 `def : Prop` 规避 sorry 计数、禁把结论塞进假设。
- 每条定理对照原书做 statement fidelity 检查。
- `#print axioms` 必须只有 `{propext, Classical.choice, Quot.sound}`。
- 每个证明开工前三轮头脑风暴（设计存 `DESIGN_*.md`）。

## 当前状态

### 已完成

Part A, Ch I §I.1–I.2 — 符号方法 OGF transfer core（`AnalyticCombinatorics/Ch1/OGF/`）：
- `Defs` — `ogfSeq`、`CombClass`（graded Fintype 族）、`counts`、`CombClass.ogf`；
  原始类 ∅(=0)、ε(=1)、Z(=z)。
- `Sum` — 组合和 `(B+C)(z)=B(z)+C(z)`。
- `Product` — 笛卡尔积 `(B×C)(z)=B(z)·C(z)`（核心，经 `coeff_mul`+antidiagonal 重索引）。
- `Audit` — `#print axioms` 确认 7 条 headline 只依赖核心三公理。

### 待做（仅 Ch I 内）

SEQ（序列）、MSET（多重集）、PSET（幂集）、CYC（轮换）四个构造；I.3 应用
（compositions、partitions、words、trees）。全书其余章节均未开始。

## 构建（远端 uisai1）

本地 `lake` 被禁用。构建走 uisai1（32核/251GB）：`scripts/remote-build.sh`，或
`ssh uisai1 'cd ~/repos/AnalyticCombinatorics && export PATH=$HOME/.elan/bin:$PATH && lake build <Module>'`。
Mathlib 源码可 grep：`~/repos/AnalyticCombinatorics/.lake/packages/mathlib/Mathlib`（远端只有 grep）。
