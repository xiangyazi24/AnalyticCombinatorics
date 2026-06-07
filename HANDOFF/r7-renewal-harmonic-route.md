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

---
## UPDATE 2 (Opus, autonomous): convergence DONE modulo Fact B; Doeblin route File A banked
MILESTONE: erdos_partition_limit_exists_of_hit (ErdosLimit.lean) BANKED clean-3 — the entire
Hardy–Ramanujan convergence reduced to ONE hypothesis Fact B = (∀ᶠ J, ∃L, Tendsto (hitVal Pker rnk J u) (𝓝 L)).
Full chain clean-3: RenewalSpine + RenewalHitPot + PartitionRenewal (Layer 1 complete: Pker/rnk/dres,
Pker_mass, dres_eq, dres_block_bound, hP_leave_partition, window_rank_drop, rnk_ge_of) + ErdosLimit.

### Doeblin route to Fact B (ChatGPT 12a957cc), progress + plan
- File A (DoeblinOverlap.lean) BANKED clean-3: subprob_avg_diff, doeblin_average_diff_bound
  (|∑p f − ∑q f| ≤ (1−δ)·W for overlap≥δ, f in band [lo,lo+W]). The contraction coefficient.
- File B (TODO): KPow (kernel composition/power) P^L; P^L preserves prob + predecessor support;
  hitVal is P^L-harmonic above cutoff (hitVal_J n = ∑ (P^L) n k · hitVal_J k). [KComp/KPow defs +
  prob/support preservation by induction on L.]
- File C (TODO): osc→0 engine. delayed contraction: W bounded ≥0, e→0, W_R ≤ q·(window-sup W)+e_R,
  q<1 ⟹ W→0. Cleanest via limsup: Λ=limsup W; limsup(window-sup)=Λ; Λ≤qΛ⟹Λ=0. (Formulation note:
  the Finset.sup' nonempty in the statement is the annoyance — use limsup or a supplied-bound form.)
- File D (HARD CORE — the research wall): FiniteTimeRankDoeblin — finite-time overlap
  overlap((P^L) n)((P^L) n') ≥ δ for ranks within A, from the Gamma(2,C) √n-decrement local limit
  (L-fold convolution density bounded below on a compact interval). NO Mathlib renewal/local-limit.
  This is the single irreducible hard analytic fact for the partition kernel (σ(m) arithmetic +
  n-dependence). Likely needs dedicated effort / Ho-Lin-level input; isolate as a hypothesis.
- File E (TODO): Fact B from A+B+C+D — hitVal_J is P^L-harmonic, so by doeblin_average_diff_bound its
  oscillation contracts by (1−δ) per L steps ⟹ vanishing tail osc ⟹ hitVal_J Cauchy ⟹ converges.
  Then erdos_partition_limit_exists := erdos_partition_limit_exists_of_hit (this).

### Bottom line
Everything except the Gamma-overlap local-limit (File D) is deterministic and bankable. File D is the
genuine research bottleneck — the one hard analytic fact. Recommend isolating it as an explicit
hypothesis (FiniteTimeRankDoeblin) so the rest closes, and attacking it separately.

---
## UPDATE 3 (Opus, autonomous): Doeblin route — both deterministic ENGINES banked clean-3
- File A (DoeblinOverlap): doeblin_average_diff_bound ✓ clean-3 (gate GATE_EXIT_0).
- File C (StepContraction): tendsto_zero_of_step_contraction ✓ clean-3 (W(n+L)≤qW(n)+e, q<1, e→0 ⟹ W→0).
Both deterministic engines done. Plus the entire convergence reduced to Fact B (ErdosLimit, banked).

### Remaining (precise)
- File B (TODO, deterministic, moderate): KComp/KPow (kernel composition/power over Finset.range),
  P^L preserves probability + predecessor support, and hitVal is P^L-harmonic above cutoff
  (hitVal_J n = ∑ (KPow L P) n k · hitVal_J k) by induction on L from hitVal_eq.
- CONNECTION (TODO, the subtle design — ChatGPT §9): turn the per-block Doeblin contraction
  (doeblin_average_diff_bound applied to the P^L-harmonic hitVal: osc of hitVal over a rank-block R
  ≤ (1−δ)·osc over the lower slab) into the step-contraction form W(R) ≤ q·W(R−B)+e_R that File C
  consumes. KEY simplification: use a TAIL/monotone oscillation W_R so the window-sup collapses to a
  single point W(R−B) (W non-increasing ⟹ sup over [R−B,R−b] = W(R−B)); but connecting cross-block
  pairs (ChatGPT's "arbitrary large ranks") needs care. This design choice (block vs tail) is the
  main remaining non-mechanical decision — worth Xiang/ChatGPT input.
- File D (HARD CORE / research wall): FiniteTimeRankDoeblin — overlap((KPow L P) n)((KPow L P) n') ≥ δ
  for comparable ranks, from the Gamma(2,C) √n-decrement L-fold-convolution density lower bound. NO
  Mathlib support; the σ(m)-arithmetic local limit. The single irreducible hard analytic fact.
- File E (TODO): Fact B from B+C+D+connection ⟹ erdos_partition_limit_exists via the banked reduction.

### Bottom line
Two deterministic engines (A, C) + the full reduction (ErdosLimit) are banked clean-3. Remaining:
KPow (mechanical), the osc-contraction connection (design subtlety), and the Gamma overlap (research
wall). The wall is the genuine bottleneck; everything else is deterministic and isolates it.

---
## UPDATE 4 (Opus, autonomous): complete deterministic Doeblin machinery banked; §9 connection is the blocker
ALL deterministic contraction machinery BANKED clean-3 (~21 commits): DoeblinOverlap (File A
doeblin_average_diff_bound), KernelPow (File B KComp/KPow + nonneg + strict support), StepContraction
(File C tendsto_zero_of_step_contraction osc→0), BlockContract (pair_contract: comparable-rank overlap
+ η-harmonic ⟹ |h i−h j|≤(1−δ)W+2η). Plus the full convergence reduction (ErdosLimit).

### The precise remaining blocker (NOT just a design preference — genuinely subtle)
The Doeblin overlap δ>0 holds ONLY for COMPARABLE ranks (|rank i−rank j|≤A). So the local pairwise
contraction does NOT globalize to TailOsc (far-apart pairs have no overlap, factor-1 only). Confirmed
TailOsc R ≤ (1−δ)TailOsc(R−B) FAILS. Need the correct block-osc→Cauchy argument. My hypothesized
center-sequence chain has a GAP: c_R Cauchy needs Σ_R BlockOsc(R) < ∞ (geometric decay), not just
BlockOsc→0; the windowed contraction gives →0 but geometric decay needs care. ChatGPT consult
347e784c (the precise question) is in flight but the bridge is stalling on the long answer.

ACTION FOR XIANG: please relay ChatGPT task 347e784c's full answer (the §9 block-osc→Cauchy connection
+ killed-kernel harmonic setup) if the bridge truncates — it's the precise remaining design blocker.

### Also pending (independent of §9)
- killed-kernel harmonic for hitVal: a single large-m step can jump below cutoff, so hitVal is
  KILLED-kernel-harmonic, not plain-KPow-harmonic; the boundary-absorb (diagonal k=n) breaks the
  predecessor range-n framework. Needs a clean killed-kernel setup (consult should clarify).
- File D (RESEARCH WALL): FiniteTimeRankDoeblin = Gamma(2,C) L-fold-convolution overlap δ>0. Unchanged.
