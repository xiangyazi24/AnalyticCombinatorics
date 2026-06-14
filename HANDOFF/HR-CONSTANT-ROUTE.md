# HR exact constant a = 1/(4√3) — route (DOCTRINE avenue d)

`erdos_partition_limit_exists` proves ∃a>0, u_n = n·p(n)·e^{-C√n} → a (C=π√(2/3)).
The renewal/Doeblin contraction gives existence+positivity but NOT the value:
scaling u by λ leaves the kernel mass and contraction invariant, so the
architecture forces a 1-D limit space but cannot pick the amplitude. The value
needs independent second-order asymptotic input (confirmed by ChatGPT ac, R1,
repo-read @ 5ec4233). NOT a documented obstruction — provable via comparison.

## Shortest faithful route (no full circle method)

1. [HAVE] existing theorem: u_n → a > 0.
2. [MISSING — load-bearing brick] second-order Laplace/Euler-product asymptotic
   `partLaplace_second_order`:
     P(e^{-t}) = ∑ p(n) e^{-tn} ~ √(t/2π) · e^{A/t},  A = π²/6.
   Proof: Euler product ∏ 1/(1-e^{-tn}); isolate -log(1-e^{-x}) = -log x + h(x);
   Stirling / Euler–Maclaurin on ∑_{n≥1} -log(1-e^{-tn}). (Meinardus main term.)
   Upgrade of the repo's FIRST-order `partition_log_asymptotic` (t·log P → A).
3. Abelian comparison `partLaplace_asymp_from_erdos_limit`:
     from u_n → a (+ u_abs_le global bound), P(e^{-t}) ~ a · modelSaddle t,
     modelSaddle t := ∑_{n≥1} e^{C√n - tn}/n.
4. real saddle `modelSaddle_asymp`:
     modelSaddle t ~ (4√π / C) · √t · e^{A/t}   (1-D real saddle at n* = (C/2t)²).
5. compare constants `erdos_limit_constant`:
     √(t/2π) e^{A/t} ~ a·(4√π/C)√t e^{A/t}  ⟹
     a = (1/√(2π)) / (4√π/C) = C/(4π√2) = π√(2/3)/(4π√2) = 1/(4√3). ✓
   Uses repo's A=π²/6 and C²=4A.

## Repo inventory (ChatGPT-verified, re-verify before use)
- HAVE: `PartLaplace` (Partitions, `∑' n, part n * exp(-(t*n))`); finite Euler
  product + convergence to PartLaplace; `partition_log_asymptotic`
  (t·log P → A); `u_abs_le` (global Mu bound); `A = π²/6` (UpperBound.lean);
  `C^2 = 4*A` (ErdosKernel.lean); HAdmissible saddle machinery (Ch8/SaddlePoint).
- MISSING: brick 2 (second-order prefactor) — THE key. Then 3,4,5.
- No partition-product HAdmissible instance (so the abstract saddle theorem
  isn't directly reusable for the GF; the real-saddle modelSaddle route is
  shorter than building a complex HAdmissible instance).

## Suggested new files
- `Ch8/Partitions/ProductSecondOrder.lean` — `partLaplace_second_order` (brick 2).
- `Ch8/Partitions/ErdosConstant.lean` — `modelSaddle`, `modelSaddle_asymp`,
  `partLaplace_asymp_from_erdos_limit`, `erdos_limit_constant`.

Terminal: `erdos_limit_constant : (Tendsto u atTop (𝓝 a)) → 0<a → a = 1/(4√3)`
clean-3, then strengthen `erdos_partition_limit_exists` to name the constant.
Brick 2 is the hard analytic core; attack first.

## Brick 2 decomposition (ChatGPT R2 — WINNING route: singular Euler–Maclaurin, NO ζ'(0))

The 2π comes from Mathlib's **Stirling** (repo already uses it in Ch8/SaddlePoint),
NOT ζ'(0). Avoids Mellin/ζ'(0) entirely. Shortcut: identify ∫=A via the EXISTING
first-order `partition_laplace_log_asymptotic` (×t, compare) — no new ζ integral.

L(t)=∑_{k≥1} -log(1-e^{-kt}). N t=⌊1/t⌋, R t=N t·t→1. Split:
  L = ∑_{k≤N} -log(tk)  +  ∑_{k≤N} h(kt)  +  ∑_{k>N} f(kt),
  f=log1mexp=-log(1-e^{-x}),  h=log1mexpReg=f+log x  (h→0 at 0+).

3 files:
- `Ch8/Partitions/LogOneMinusExp.lean`: defs log1mexp, log1mexpReg; lemmas
  log1mexpReg_tendsto_zero (uses repo exp_sub_one_div_self_tendsto_one), tail exp
  bound, deriv2 bounds (local/private derivative formulas, don't over-generalize).
- `Ch8/Partitions/TrapezoidEM.lean`: two one-off lemmas trapezoid_sum_head (g'' bdd
  on [0,2]) + trapezoid_sum_tail (g,g'' decay on [1/2,∞)). API:
  intervalIntegral.sum_integral_adjacent_intervals, integral_eq_sub_of_hasDerivAt,
  norm_integral_le_of_norm_le_const. Per-cell error C·t³, ×N=O(1/t) → O(t)=o(1).
  NOT a general Euler–Maclaurin framework.
- `Ch8/Partitions/ProductSecondOrder.lean`: singular head via Stirling
  (∑-log(tk)=-N log t-log N!; Stirling.log_stirlingSeq_formula +
  tendsto_stirlingSeq_sqrt_pi give the 2π); assemble A+B+C → with-I form
  (log P = I/t + ½log(t/2π) + o(1)); log1mexpIntegral_eq_A via first-order theorem;
  → partLaplace_second_order.

ζ'(0) route (LOSING, do not use): needs Γ'(1)=-γ, ζ Laurent at 1, eulerMascheroni
API — all likely absent from pinned Mathlib. R2 confirms Euler–Maclaurin is shorter.

Confident Mathlib names (R2): Stirling.{log_stirlingSeq_formula,
tendsto_stirlingSeq_sqrt_pi, factorial_isEquivalent_stirling}; intervalIntegral.
{sum_integral_adjacent_intervals, integral_mono_on, norm_integral_le_of_norm_le_const};
Summable.sum_add_tsum_nat_add; norm_tsum_le_tsum_norm. Repo: PartLaplace,
partLaplace_eq_finprod_tendsto, partition_laplace_log_asymptotic, log_partLaplace_eq,
log_series_regroup, exp_sub_one_div_self_tendsto_one.
