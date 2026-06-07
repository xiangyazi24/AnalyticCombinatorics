# R7 cover: rigorous obstruction in the forward-fill strategy (Opus, found 06-06)

## Setup
Goal: u_n → L>0 (erdos_partition_limit_exists). Have: u bounded in [c,M] (u_liminf_positive,
u_limsup_finite). Recurrence: u_n = Σ_m erdosWeight(n,m)·u(n−m) + boundaryTerm_n, with
Σ_m erdosWeight → 1 (kernelMass_sub_one_rate: |mass−1|≤K/n), boundaryTerm → 0.
Banked one-step pullback exists_window_near_max needs running-max; ChatGPT's cover (c43aa296)
needs a chain-usable ChainPullback (any near-top point) + forward-fill tiling.

## The amplification (derived exactly)
ChainPullback would need: from `top − loss ≤ u n`, produce m in window with
`top − (loss + Δ_n) ≤ u(n−m)`. Deriving it from the recurrence: all deep complement points
(n−m ≥ N₀') satisfy u(n−m) ≤ top (global running max). Averaging the window mass forces
  Δ_n ≥ loss·(1−w)/w + δ_n,   w := kernelWindow/kernelMass,  δ_n = (|b|+|top|·|1−mass|+M·R)/(w·mass)
so loss_{j+1} = loss_j + Δ_n = loss_j/w + δ_n  — MULTIPLICATIVE 1/w per step.
Over a chain of length ~ rank N − rank k ~ √N, loss ~ δ·w^{−√N} → BLOWS UP for w<1 fixed.
The 1/w is intrinsic to normalizing the lower bound by the window weight; cannot be removed by
choice of v (max vs weighted-avg give the same /w).

## Why w cannot → 1 (the structural hole)
- Banked window: erdos_kernel_fixed_window_pos gives [a,b]=[1,2], μ=I/2, I=∫₁²(π²/6)y e^{−(C/2)y}dy.
  Total model mass = ∫₀^∞(π²/6)y e^{−(C/2)y}dy = (π²/6)(2/C)² = 1 (C=π√(2/3)). So w=[√n,2√n]-fraction
  = I < 1, a FIXED constant. Complement = ∫₀^a + ∫_b^∞ ~ a² + e^{−(C/2)b}.
- To get w→1 need a→0, b→∞ with Σ_chain(a_t²+e^{−(C/2)b_t})<∞ (t=√n index).
- BUT forward fill (u_local_high_forward_fill, banked) reaches only r ≤ h√n, h=2ε/(CM) FIXED.
  Linear-reach fill is FALSE: √(n+r)−√n ~ √n for r~n, so u(n+r) ≥ u(n)e^{−C√n} → 0.
  ⟹ the chain STEP m must be ≤ b√n ≤ (reach) h√n ⟹ b ≤ h FIXED ⟹ w ≤ 1−e^{−(C/2)h} < 1.
- Multi-hop fill across a gap of length m≤b√n costs ~(b/h)·θ (constant per gap) × ~√N gaps =
  √N·θ → accumulates. Making θ_j summable forces h_j=2θ_j/(CM)→0 ⟹ reach→0 ⟹ fills nothing.

## Conclusion
The forward-fill record-cover (ChatGPT c43aa296) has a genuine structural obstruction: window
mass-capture (needs wide window) vs forward-fill reach √n (caps window width) are incompatible,
leaving w<1 fixed and a chain that amplifies loss geometrically. Need either:
  (1) a cover mechanism without per-gap θ and without the 1/w averaging amplification, or
  (2) replace the whole cover by an elementary RENEWAL-theory convergence: u_n = Σ_m w_{n,m}u(n−m)+b_n
      with Σw→1, b→0 is a renewal/Tauberian equation; u_n → L should follow from renewal theory
      with the kernel's regularity (the mass concentrates at m~√n; weights w_{n,m} asymptotically a
      probability law). This sidesteps records/forward-fill entirely.
Banked clean-3 regardless: DefectSummable (Σ B/(t+1)² + Σ tᵏe^{−ct}) for the rank-budget.

## UPDATE (Opus): the obstruction is strategy-level, hits the RECORD route too
Re-read partition-I56-convergence-route-R7.md (the design doc). It ALREADY flags this:
  line 448 "this one-step pointwise lemma has a loss factor 1/μ ... not by itself for unbounded chains"
  line 493 "should NOT amplify pointwise losses by κ^K ... use record averaging ... additively"
but the "additive" replacement (Routes 8A shell-error / 8B path-spread) is only sketched, never
justified at the 1/μ step. Proved now that the 1/μ is INTRINSIC to the record route:

Record pullback (rigorous): N high-record on [N₀,N], u N − η ≤ u q. Recurrence u q = Σ_m W u(q−m)+b_q;
all record-range predecessors ≤ u N. Total deficit Σ_{record-range} W(u N − u(q−m)) = u N·S_q − u q + b
≤ η + M|S_q−1| + b =: η+Err (SMALL, μ-independent — the (1−μ) near-complement is bounded by u N and
CANCELS against u N·S_q, so it does NOT enter Err). BUT the deficit is WEIGHTED; converting to a
POINTWISE near-record window predecessor (which forward-fill REQUIRES) costs division by the window
mass: ∃ window m, u N − u(q−m) ≤ (η+Err)/μ_win. So η ↦ (η+Err)/μ — multiplicative 1/μ per step.
Over the ~√N steps to cover [N₀,N], η_K = Err·Σ μ^{-i} ~ Err·μ^{−√N}. Even with Err~1/shell²
(summable), the early (shell~√N, Err~1/N) errors get μ^{−√N} ≫ 1/N → BLOWS UP.

Root cause: weighted-deficit → pointwise-bound conversion costs 1/μ_win; forward-fill needs pointwise;
fixed window ⟹ μ_win<1 ⟹ compounding. Cannot be fixed by Err being summable (it is) — the homogeneous
1/μ factor is the killer. Both ChatGPT's ChainPullback (c43aa296) and the doc's Routes 8A/8B assume
additive accumulation that is not derivable.

## Status: genuine strategy-level blocker
The record-cover/forward-fill strategy for high_record_covers_tail appears structurally unable to avoid
the 1/μ compounding. Erdős's theorem is TRUE (u_n converges), so a correct argument exists — but it is
likely NOT this record-chaining strategy. Open questions (ChatGPT consult b0f6ab89 in flight):
  (i) a convergence argument that stays WEIGHTED (never converts deficit→pointwise), or
  (ii) Erdős's actual 1942 closing mechanism (literature) — possibly a direct monotonicity / Tauberian
       on the σ-convolution p(n)=(1/n)Σσ(m)p(n−m), not records at all.
Banked clean-3 this round: DefectSummable (gate GATE_EXIT_0, DIRTY:0) — reusable if a route needs it.
