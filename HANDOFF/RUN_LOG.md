
## Update 2026-06-14 — BRICK 2 COMPLETE (HR constant avenue d)
Brick 2 (second-order Laplace asymptotic = Meinardus main term) FULLY closed, 6 commits pushed:
- TailSum.lean: generic infinite-cell tail trapezoid summation theorem.
- Log1mexpTailTrapezoid.lean: concrete log1mexp tail -> 0 (instantiation + geometric squeeze).
- Log1mexpIoiIntegral.lean: IntegrableOn (Ioi 0) + integral split ∫_0^R+∫_R^∞=∫_0^∞ (ChatGPT-drafted).
- ProductSecondOrder.lean:
    * log_partLaplace_eq_head_add_tail (log P = head + tail, ℕ+→ℕ split)
    * log_partLaplace_second_order_with_I (with-I form)
    * log1mexp_integral_eq_A (I = A = π²/6 via limit uniqueness)
    * log_partLaplace_second_order : log P(e^{-t}) - A/t - ½log(t/2π) → 0  [FINAL brick-2 form]
All clean-3 axioms {propext, Classical.choice, Quot.sound}, 0 sorry/admit/native_decide.
REMAINING for a=1/(4√3): brick 3 (Abelian comparison P~a·modelSaddle), brick 4 (modelSaddle real
saddle ~ (4√π/C)√t e^{A/t}), brick 5 (constant algebra a=C/(4π√2)=1/(4√3)).

## Update 2026-06-14 (cont) — brick 4/5 foundations + scoped plan
DONE (committed, clean-3, pushed):
- ErdosConstant.lean: saddle_meinardus_const_identity ((4√π/C)·√(2π)=4√3), C_sq_eq (C²=2π²/3),
  modelSaddle def, modelSaddle_exponent_bound, summable_modelSaddleTerm, modelSaddle_pos,
  erdos_limit_constant_of_asymptotics (BRICK 5, conditional on brick 3+4 log-asymptotics).
TOOLS CONFIRMED in v4.29.0/repo (re-verified):
- integral_gaussian (b:ℝ): ∫ exp(-b x²)=√(π/b); b=1 → √π.
- riemann_sum_Ioi_sub_integral_bound (MassRateRiemannGeneral.lean:78): instantiate mesh-param=1,
  f := saddleDensity(s, ·+1) to compare ∑_{k≥2} saddleDensity(s,k) with ∫_{Ioi 1} saddleDensity(s,·).
- intervalIntegral.inv_smul_integral_comp_div (linear substitution), 
  MeasureTheory.tendsto_integral_filter_of_dominated_convergence.
REMAINING — BRICK 4 (modelSaddle_log_asymp), 4-file plan in HANDOFF/HR-brick4-saddle-route.md:
  (1) saddleDensity def + cutoff integral ∫_{Ioi 1}; saddleDensity_hasDerivAt.
  (2) sum↔integral error via riemann_sum_Ioi_sub_integral_bound (mesh=1) → o(√t e^{A/t}).
  (3) x=y² substitution (FLAGGED: nonlinear set-integral subst, API uncertain — do [1,B] then B→∞),
      complete-square Cy-ty²=A/t-t(y-y0)², linear u=√t(y-y0) subst (inv_smul_integral_comp_div).
  (4) Gaussian DCT: ∫_{-B}^B e^{-u²}/(1+βu) → √π (central |u|≥-C/4√t bound + far-left exp-negligible);
      B→∞ via integral_gaussian; assemble ySaddleIntegral_ratio → modelSaddle_ratio_asymp → log form.
  Then BRICK 3 (Abelian): P=1+∑ u_n·w_n, modelSaddle=∑ w_n, w_n=e^{C√n-tn}/n; |∑(u_n-a)w_n|≤ε·modelSaddle
  + bounded head, modelSaddle→∞ ⟹ log P - log a - log modelSaddle → 0. Then brick 5 discharges → a=1/(4√3).
