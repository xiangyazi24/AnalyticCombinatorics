
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

## Update 2026-06-14 (cont 2) — brick 4 CRUX RESOLVED + more plumbing
ModelSaddleIntegral.lean (all committed, clean-3, pushed):
- saddleDensity + saddleDensity_hasDerivAt; saddle_exponent_bound_real.
- integrableOn_saddleDensity_shift + ..._deriv (riemann inputs, shift dodges 1/x singularity).
- saddleDensity_shift_hasDerivAt (chain rule).
- modelSaddleInterval_substitution: ∫₁^{B²} e^{C√u-su}/u = ∫₁^B 2e^{Cv-sv²}/v
  ★ THE flagged-risk x=y² substitution — RESOLVED via intervalIntegral.integral_comp_mul_deriv'
  (image-continuity version; image [1,B²]⊂Ioi 0 avoids the singularity). No open API risks left.
- saddle_complete_square: Cv-sv² = A/s - s(v-C/2s)² (saddle v₀=C/2s, peak A/s).
REMAINING brick 4 (all tools confirmed, no risks):
  (i)  B→∞: ∫_{Ioi 1} saddleDensity s = lim_B ∫₁^{B²} = lim ∫₁^B 2e^{Cv-sv²}/v  (intervalIntegral
       → setIntegral via integral_Ioi as limit; integrableOn already have).
  (ii) linear sub u=√s(v-C/2s) (intervalIntegral.inv_smul_integral_comp_div) + complete_square ⟹
       ∫₁^B 2e^{Cv-sv²}/v = (4√s/C)e^{A/s} ∫ e^{-u²}/(1+(2√s/C)u) du.
  (iii) Gaussian DCT: ∫_{-B}^B e^{-u²}/(1+βu) → √π (central |u|≥-C/4√t bound by 2e^{-u²} +
        far-left exp-negligible); B→∞ via integral_gaussian (b=1 → √π).
  (iv) assemble modelSaddleIntegral ~ (4√π/C)√s e^{A/s}; riemann comparison
       (riemann_sum_Ioi_sub_integral_bound mesh=1, M=exp(C√3) on (0,2]) + o() error ⟹
       modelSaddle_ratio_asymp → modelSaddle_log_asymp (brick 4 done).
  Then brick 3 (Abelian) → brick 5 discharges → a=1/(4√3).

## Update 2026-06-14 (cont 3) — brick 4 ~85%: both hard analytic cores DONE
ModelSaddleIntegral.lean (committed, clean-3): saddleDensity(+deriv), exponent bounds,
ALL integrabilities (shift, shift-deriv, vIntegrand, saddleDensity_Ioi1), x=y² substitution
(crux, finite + Ioi-level), complete-square, vIntegral_eq_gaussianForm (pull e^{A/s}),
riemann_term_eq (tsum-split), modelSaddle_sub_integral_bound (RIEMANN COMPARISON applied:
|modelSaddle - saddleDensity 1 - ∫_{Ioi0}f| ≤ ∫|f'| + e^{C√3}).
GaussianTail.lean (committed, clean-3): integral_exp_neg_sq (=√π), alpha/beta tendsto,
gaussianTailKernel pointwise+dom(2e^{-u²})+DCT ⟹ cut kernel integral → √π. THE moving-limit
Gaussian DCT (the analytic heart) DONE.
BOTH hardest analytic cores complete: brick2 tail-trapezoid + brick4 Gaussian-DCT.
REMAINING (mechanical-but-large, ~300 lines, all patterns established, skeleton in
HANDOFF/HR-brick4-gaussian-route.md):
  (A) affine change-of-vars ∫_{cut}^B e^{-s(v-v₀)²}/v = (2√s/C)∫ e^{-u²}/(1+βu) du
      (integral_comp_mul_deriv' with φ u = v₀+u/√s, same pattern as modelSaddleInterval_substitution),
      + B→∞, + left-strip ∫_1^{cut} ≤ (C/4s)e^{-C²/16s} negligible ⟹ gaussianTail_asymp
      (∫_{Ioi1} e^{-s(v-v₀)²}/v ~ (2√π/C)√s).
  (B) o() estimate: ∫|f'| + e^{C√3} = o(√s e^{A/s}) (∫|f'| via same Gaussian machinery;
      f' bracket has extra small factor near saddle, so easier than (A)).
  (C) assemble modelSaddle_ratio_asymp (comparison + (A) + (B): saddleDensity 1 & errors are
      o(√s e^{A/s}), vIntegral_eq_gaussianForm gives 2e^{A/s}·(2√π/C)√s = (4√π/C)√s e^{A/s})
      → modelSaddle_log_asymp (BRICK 4 done).
  (D) BRICK 3 Abelian: P=1+∑ u_n·w_n, modelSaddle=∑ w_n, |∑(u_n-a)w_n| ≤ ε·modelSaddle + bdd head,
      modelSaddle→∞ ⟹ log P - log a - log modelSaddle → 0.
  (E) discharge erdos_limit_constant_of_asymptotics (brick 5, already proven) → a=1/(4√3).
