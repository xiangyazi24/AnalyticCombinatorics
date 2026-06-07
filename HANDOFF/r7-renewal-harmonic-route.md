# R7 convergence: renewal / harmonic-Markov-chain route (ChatGPT b0f6ab89, 06-06)

Records are abandoned (1/μ amplification proven intrinsic, see r7-amplification-obstruction.md).
New route: u as approximately harmonic for a decreasing Markov chain on the √n scale. DETERMINISTIC
Lean (no probability measures) via Hit/Pot potentials.

## Layer 1 — kernel normalization
  S n      := ∑' m, erdosWeight n m          (= kernelMass n; have kernelMass_sub_one_rate |S−1|≤K/n)
  P n k    := if k < n then erdosWeight n (n−k) / S n else 0     (prob kernel on predecessors k<n)
  d n      := u n − ∑' k, P n k · u k                            (residual)
  d_bound:   |d n| ≤ |b n| + M·|S n − 1|         (the (1−w) near-complement cancels against u·S; NOT in d)
  d_block_summable: ∃ e≥0 Summable, ∀ᶠ n |d n| ≤ e(rank n), rank n = Nat.sqrt n.
             e(j) = O(1/j²)+exp-small  ⟸ DefectSummable (summable_defect_scale), BANKED clean-3.

## Layer 2 — abstract deterministic potentials (well-founded on n, P n k=0 unless k<n)
  Hit J φ n := if rank n < J then φ n else ∑' k, P n k · Hit J φ k
  Pot J e n := if rank n < J then 0   else e (rank n) + ∑' k, P n k · Pot J e k
  rec_iter_bound:  |d n| ≤ e(rank n)  ⟹  |u n − Hit J u n| ≤ Pot J e n   (strong induction on n)

## Layer 3 — occupation ⟹ potential tail  [HARD ANALYTIC FACT A, isolate]
  ExpectedVisitsBeforeCutoff P rank J n ℓ ≤ B  (uniform renewal-density bound)
  ⟹ Pot J e n ≤ B · ∑' r, e (J+r)   (= B·tail_e J → 0 since Summable e)

## Layer 4 — hitting/overshoot convergence  [HARD ANALYTIC FACT B, isolate]
  ∀ J, ∀ bounded φ on {rank<J},  Hit J φ n  → L_J  as n→∞   (non-lattice renewal overshoot)

## Layer 5 — convergence (abstract spine, takes A,B as hypotheses)
  For fixed J: |u n − Hit J u n| ≤ B·tail_e J; Hit J u n → L_J ⟹ limsup u − liminf u ≤ 2B·tail_e J.
  J→∞ (tail_e→0) ⟹ limsup u = liminf u ⟹ ∃L Tendsto u atTop (𝓝 L).
  Positivity from u_liminf_positive (BANKED). ⟹ erdos_partition_limit_exists.

## Kernel analytic facts (Facts A,B from the Gamma(2,C) limit law)
  √n-decrement Y_n=√n−√(n−m), m=y√n ⟹ Y_n=y/2+O(y²/√n); limit density g(s)=(2π²/3)s e^{−Cs}
  (Gamma shape 2 rate C, mean 2/C, NON-LATTICE — continuous density). Required: P normalized;
  uniform exp tail P_n(Y≥R)≤Ae^{−λR}; no tiny jumps P_n(Y≤ρ)≤Aρ²+o(1); local-limit to g;
  ⟹ A (occupation) and B (overshoot). These are the renewal-theory analytic core (hardest).

## Build order
  1. Abstract spine: Layers 2+5 as a standalone theorem `triangular_renewal_convergence`
     taking (hrec, herr_block summable, hoccupation, hhitting) as hypotheses → ∃L Tendsto.
     DESIGN-INDEPENDENT, verifiable clean-3 NOW. (Layer-2 Hit/Pot recursion + Layer-5 osc collapse.)
  2. Layer 1 (normalization, d_bound, d_block_summable via DefectSummable) — concrete.
  3. Facts A,B (renewal kernel theorem) — hard analytic, separate file, from Gamma(2,C) limit.
  4. erdos_partition_limit_exists := spine applied to the partition kernel.
Banked clean-3 already reusable: DefectSummable, u_limsup_finite, u_liminf_positive, kernelMass_sub_one_rate.

---
## PROGRESS (Opus, autonomous): spine + Fact A + Hit/Pot + Layer-1 core BANKED clean-3
Banked this session (all clean-3, gate GATE_EXIT_0):
- RenewalSpine.lean: tendsto_of_uniform_hit_approx (engine, ∀ᶠ J), rec_iter_bound (herr conditional),
  pot_le_block_sum + pot_le_block_sum_of_leave (Fact A, leave-prob), block_sum_le_tail, tail_tendsto_zero.
- RenewalHitPot.lean: hitVal/potVal WF defs (sum over (range n).attach) + hitVal_eq/potVal_eq.
- PartitionRenewal.lean: Pker/rnk/dres defs, Pker_nonneg, rnk_mono, kernelMass_nonneg,
  u_eq_Pker_sum_add_dres, sum_Icc_reflect_sub (k↦n−k), Pker_sum_mul, Pker_mass(=1), dres_eq, rnk_sqrt_bounds.

## REMAINING (precise specs)
### herr = dres_block_bound  [PartitionRenewal] — analysis, ~100 lines, build in pieces
∃ errFn, (∀j, 0≤errFn j) ∧ Summable errFn ∧ ∀ᶠ n, |dres n| ≤ errFn (rnk n).
errFn j := 72*M*K/((j:ℝ)+1)^2 + (32/81)*(j:ℝ)^4 * exp(−(C/3)*j).   M from u_limsup_finite, K from kernelMass_sub_one_rate.
Summable: summable_const_div_succ_sq (72MK) + (summable_pow_mul_exp_neg (C/3) 4).mul_left (32/81).
Bound (n large, j=rnk n≥1): dres_eq ⟹ |dres n| = |u n·(S−1)+b|/S ≤ (M·(K/n)+b)/S ≤ 2(MK/n + n²e^{−C√n})
  [S≥1/2 since K/n≤1/2 eventually]. Scale via rnk_sqrt_bounds: j/3≤√n<(j+1)/3 ⟹ (j/3)²≤n<((j+1)/3)²:
  1/n ≤ 9/j² ≤ 36/(j+1)²; n²<((j+1)/3)^4≤(16/81)j^4 (j≥1); e^{−C√n}≤e^{−Cj/3}. ⟹ ≤ errFn(j).
  Build sub-lemmas first: n_lb/n_ub (sq_sqrt + gcongr), S_lb (abs_le + hhalf:K/n≤1/2 eventually), σ≤n² bound (sigmaR_le_square / boundaryTerm ≤ n²e^{−C√n} — see KernelBarriers:179).
### hP_leave  [PartitionRenewal] — window rank-drop, ~80 lines
∃μ>0, ∀ᶠ n, μ ≤ ∑_{k∈(range n).filter(rnk k<rnk n)} Pker n k.
Window m∈(√n,2√n] (erdos_kernel_fixed_window_pos: a₀=1,b₀=2, kernelWindow≥μ_w eventually). For m>√n:
√n−√(n−m) > 1/2 (since = √n/(√n+√(n−m)) > 1/2), so 3·drop>3/2>1 ⟹ ⌊3√(n−m)⌋<⌊3√n⌋ i.e. rnk(n−m)<rnk n.
So {window steps} ⊆ {rank-drop predecessors k=n−m}; ∑_{drop} Pker ≥ ∑_{window} Pker = kernelWindow/S ≥ μ_w/2 =: μ (S≤... bounded). Need: filter over k vs window over m=n−k reindex (sum_Icc_reflect_sub-style), and the rnk-drop per window m.
### Final assembly  [new file or PartitionRenewal] — needs Fact B
- hP_mass/herr/hP_leave hold for rnk n ≥ J (J large): convert ∀ᶠ n → ∀ n, J≤rnk n→ via rnk→atTop
  (rnk n≥J → n≥(J/3)²; pick J≥3√n₁). Helper: ∀ n₁, ∃ J₀, ∀ n, J₀≤rnk n → n₁≤n.
- For each large J: set Hit:=hitVal Pker rnk J u, Pot:=potVal Pker rnk J errFn. rec_iter_bound ⟹
  |u n − Hit n| ≤ Pot n; pot_le_block_sum_of_leave ⟹ μ·Pot n ≤ block ≤ tail_J. So |u n−Hit n| ≤ tail_J/μ.
  ⟹ hbound (∀ᶠ J, ∀ᶠ n, |u n−Hit_J n| ≤ (1/μ)·tail_J), B:=1/μ, tail_J:=(∑'errFn − ∑_{range J}errFn)→0.
- hhit (Fact B): ∀ᶠ J, ∃L, Tendsto (hitVal Pker rnk J u) atTop (𝓝 L).  *** STILL OPEN — consult 12a957cc ***
- erdos_partition_limit_exists := tendsto_of_uniform_hit_approx (u bdd: u_limsup_finite/u_liminf_positive)
  hbound hhit tail→0; positivity from u_liminf_positive.
