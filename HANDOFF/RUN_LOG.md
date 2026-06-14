
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

## Update 2026-06-14 (cont 4) — brick4 Gaussian: DCT core + affine change BOTH done
GaussianTail.lean (committed, clean-3): integral_exp_neg_sq=√π; gaussianTailAlpha/Beta tendsto;
gaussianTailKernel pointwise+dom(2e^{-u²})+DCT ⟹ ∫kernel→√π (analytic heart);
sqrt_mul_div_self, gaussianTail_denom_id, gaussianTail_affine_interval (u=√s(v-v₀) substitution
via integral_comp_mul_deriv' — the API-sensitive piece, DONE).
EVERY hard/uncertain piece of the whole a=1/(4√3) derivation is now resolved in code:
brick2 tail-trapezoid, brick4 Gaussian-DCT, the x=y² + affine substitutions, riemann comparison.
REMAINING = mechanical connective + brick 3 (all patterns established):
  (G1) affine→kernel: e^{-u²}/(C/(2√s)+u) = (2√s/C)·e^{-u²}/(1+βu) [since C/(2√s)+u=(C/(2√s))(1+βu)];
       B→∞ on gaussianTail_affine_interval (intervalIntegral_tendsto_integral_Ioi, need integrability
       of e^{-u²}/(C/(2√s)+u) on Ioi α) ⟹ ∫_{Ioi cut} e^{-s(v-v₀)²}/v = (2√s/C)·∫_ℝ gaussianTailKernel.
  (G2) left strip ∫_1^{cut} e^{-s(v-v₀)²}/v ≤ (C/4s)e^{-C²/16s} negligible; combine with DCT
       (∫kernel→√π) ⟹ gaussianTail_asymp: ∫_{Ioi 1} e^{-s(v-v₀)²}/v ~ (2√π/C)√s.
  (G3) with vIntegral_eq_gaussianForm ⟹ ∫_{Ioi 1} 2e^{Cv-sv²}/v ~ (4√π/C)√s e^{A/s}
       = modelSaddleIoi_substitution RHS ~ ; so ∫_{Ioi1} saddleDensity ~ (4√π/C)√s e^{A/s}.
  (O)  o() estimate: ∫|f'| + e^{C√3} = o(√s e^{A/s}) (modelSaddle_sub_integral_bound RHS; f' bracket
       has extra small factor → same Gaussian machinery, easier). saddleDensity s 1 also o(√s e^{A/s}).
  (R)  modelSaddle_ratio_asymp (comparison + G3 + O) → modelSaddle_log_asymp = BRICK 4.
  (B3) Abelian: P=1+∑u_n·w_n, modelSaddle=∑w_n (w_n=saddleDensity s n), |∑(u_n-a)w_n|≤ε·modelSaddle+
       bdd head, modelSaddle→∞ ⟹ log P-log a-log modelSaddle→0.
  (B5) discharge erdos_limit_constant_of_asymptotics (PROVEN) → a=1/(4√3).

## Update 2026-06-14 (cont 5) — bricks 2,3,5 DONE; brick 4 ~90%
NEW committed (clean-3, pushed):
- modelGaussCut_eq, integrability inputs (GaussianTail.lean).
- ErdosAbelian.lean = BRICK 3 COMPLETE: partLaplace_log_sub_modelSaddle_tendsto
  (log P − log a − log modelSaddle → 0), taking modelSaddle_tendsto_atTop as hypothesis.
  (modelWeight, weightedU, partLaplace_eq_one_add_weightedU, finite-head/modelSaddle→0,
   Abelian ε-split ratio→a.)
ChatGPT drafts saved: HR-brick3-abelian-route.md, HR-brick4-final-route.md, HR-brick4-gaussian-route.md.
STATUS: bricks 2 (second-order Laplace), 3 (Abelian), 5 (constant algebra + combination) all DONE/clean-3.
REMAINING (brick 4 final, ~350 lines, fully roadmapped — HR-brick4-final-route.md):
  (G) gaussianTail_asymp = ∫_{Ioi 1} e^{-s(v-v₀)²}/v ~ (2√π/C)√s:
      gaussianTail_cut_ratio_tendsto (DONE-able: modelGaussCut_eq + DCT, ratio→1) +
      gaussianTail_left_ratio_tendsto_zero (strip ∫_{Ioc 1 cut} ≤ (C/4s)e^{-C²/16s},
        /denom → 0 via tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ∘ (s↦1/s)) + split assembly.
  (T) modelSaddle_tendsto_atTop (unconditionalizes brick 3): single-term lower bound
      modelSaddle s ≥ exp(C√n(s)-s·n(s))/n(s) at n(s)=⌊1/s²⌋, →∞ since (C-1)/s →∞ (C>1).
  (O) modelSaddle_riemann_error_negligible (the o() estimate — THE last hard piece, ChatGPT punted
      on a one-screen proof but gave the route): KEY INSIGHT — after x+1=y² subst, on right strip
      y≥C/(4s) the deriv bracket |C/(2y)-s-1/y²| ≤ (3+16/C²)·s (since C/(2y)≤2s, 1/y²≤16s²/C²),
      so D_right ≤ K·s·∫_{y≥cut}2e^{Cy-sy²}/y = K·s·O(√s e^{A/s}) = o(√s e^{A/s}); left strip negligible;
      exp(C√3)/(√s e^{A/s})→0. Needs a deriv-weighted x+1=y² substitution lemma (analogue of
      modelSaddleIoi_substitution).
  (A) saddleDensity_shift_integral_eq_Ioi1 (∫_{Ioi0}sd(·+1)=∫_{Ioi1}sd, translation via interval+B→∞)
      + assemble modelSaddle_log_asymp (= BRICK 4): comparison + main term (2e^{A/s}·gaussianTail_asymp)
      + (O) ⟹ modelSaddle ~ (4√π/C)√s e^{A/s} → log form.
  (Z) discharge: a = 1/(4√3) via erdos_limit_constant_of_asymptotics (PROVEN) + brick3 + brick4,
      with modelSaddle_tendsto_atTop from (T)/(O). Strengthen erdos_partition_limit_exists.

## Update 2026-06-14 (cont 6) — gaussianTail_asymp COMPLETE
GaussianTailAsymp.lean (committed, clean-3): gaussianTail_cut_ratio_tendsto (→1),
gaussianTail_strip_bound_tendsto_zero, gaussianTail_left_ratio_tendsto_zero,
gaussianTail_asymp = ∫_{Ioi 1} e^{-s(v-v₀)²}/v ~ (2√π/C)√s. The full main Gaussian
asymptotic DONE. Bricks 2,3,5 done; brick 4 ~95%.
REMAINING (only the o()-error + mechanical assembly, ~180 lines):
  (O) modelSaddle_riemann_error_negligible: ∫_{Ioi0}|f'| = o(√s e^{A/s}).
      Route (verified arithmetic): via x+1=y² substitution,
      ∫_{Ioi0}|f'| = ∫_{Ioi1} 2e^{Cy-sy²}/y · |C/(2y)-s-1/y²| dy.  Split at cut=C/4s:
      - right (y≥cut): |C/(2y)-s-1/y²| ≤ (3+16/C²)·s [C/(2y)≤2s since y≥C/4s; 1/y²≤16s²/C²≤16s/C² for s≤1],
        so D_right ≤ Ks·∫_{Ioi cut}2e^{Cy-sy²}/y = Ks·2e^{A/s}·(2√s/C)·∫kernel ~ Ks·(4√π/C)√s e^{A/s};
        D_right/main ≤ (Ks/√π)·∫kernel → 0 (O(s)).  [uses vIntegral_eq_gaussianForm + modelGaussCut_eq]
      - left (1<y≤cut): exp-negligible (same pattern as gaussianTail_left_ratio).
      Needs: a derivative-weighted x+1=y² substitution lemma (analogue of modelSaddleInterval_substitution).
  (A) saddleDensity_shift_integral_eq_Ioi1 (∫_{Ioi0}sd(·+1)=∫_{Ioi1}sd, translation interval+B→∞)
      ⟹ modelSaddle_log_asymp: from modelSaddle_sub_integral_bound, main term
      ∫_{Ioi1}sd = ∫_{Ioi1}2e^{Cv-sv²}/v = 2e^{A/s}·gaussianTail_asymp ~ (4√π/C)√s e^{A/s},
      sd 1 & (O) = o(main) ⟹ modelSaddle ~ (4√π/C)√s e^{A/s} → log form (BRICK 4).
  (T) modelSaddle_tendsto_atTop from modelSaddle_log_asymp (denom→∞), OR single-term lower bound.
  (Z) discharge erdos_limit_constant_of_asymptotics (PROVEN) with brick2 + brick3(+T) + brick4 → a=1/(4√3).
