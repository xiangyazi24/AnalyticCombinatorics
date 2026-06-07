# DOCTRINE — Path A: discharge the two Doeblin walls from scratch (unconditional Hardy–Ramanujan)

## Goal (one sentence)
Prove `∀ᶠ J, DoeblinWalls J` with zero axioms, turning `erdos_partition_limit_exists_of_walls`
into the UNCONDITIONAL `erdos_partition_limit_exists : ∃ a > 0, Tendsto u atTop (𝓝 a)`.

## Mathematical structure (what the walls really are)
Both walls concern the L-step law of the killed Erdős predecessor chain. The per-step rank-decrement
Δ = rnk(n) − rnk(n−m), m ~ erdosWeight, has (in the continuous Γ(2,C) limit, banked as
`Model.modelIntegral` / `erdos_kernel_window`):
  • jump m = x√n  ⟹  Δ ≈ 3x/2,  with x distributed ∝ (π²/6) x e^{−Cx/2}  (the Γ(2,C/2) shape);
  • E[Δ] = Θ(1) (constant, R-independent); the chain takes ~ R/E[Δ] ~ Θ(R) steps to drop from rank R
    to the boundary J  ⟹  Θ(R) regenerations  ⟹  osc(h) at rank R ~ (1−δ)^{cR} → 0. This Θ(R)-fold
    geometric decay IS the convergence (renewal mechanism).

## KEY SUBTLETY found while drafting (affects avenue choice — needs your eyes)
The banked capstone `tendsto_of_killed_doeblin` uses the ESCAPE-SPLIT engine: overlap δ on band
{rnk ≥ R−B} (fixed B) + escape mass `e(R) → 0`, via `tendsto_zero_of_step_contraction`. But the
per-step big-jump probability is  P(Δ > B) ~ e^{−cB},  CONSTANT in R (it is a normalized tail, no R).
So with FIXED B the escape mass does NOT → 0; it is a small constant ε(B). The escape-split recursion
then gives  V(R) ≤ (1−δ)V(R−B) + ε·2M  ⟹  V(∞) ≤ ε·2M/δ  (small constant, NOT 0). I.e. WALL 2 as
currently stated (`e(R)→0`, fixed B) is NOT satisfiable for this kernel. The honest convergence needs
the Θ(R)-fold geometric decay (growing block count), which the constant-B additive engine cannot give.

GOOD NEWS: the alternative engine is ALSO already banked — `tailsup_summable` (TailSup.lean):
  W R ≤ q · sSup(W '' {s ≥ R−B})  ⟹  Summable (sSup over tails)  ⟹  convergence,
PURE multiplicative (no additive e(R)). It captures the Θ(R)-fold decay directly. The remaining
difficulty is the big-jump mass: it lands at rank < R−B where osc is LARGER (V antitone), so it is not
automatically ≤ q·V(R−B). It must be handled by overlapping the big-jump landing laws too, or by a
coupling that couples big jumps.

## Avenues (ranked)
(a) RE-WIRE to the tail-sup engine + full-support overlap. Prove the L-step laws from i,j (rank ≥ R)
    overlap by δ on the WHOLE support {rnk ≥ J}, AND that the non-overlap (1−δ) part, after differencing,
    sees osc ≤ q·sSup(W over {s ≥ R−B}). Feed `tailsup_summable` (banked). Terminal: Summable tail-osc
    ⟹ `tendsto_of_center_tracking` (banked) ⟹ converge. Most reuse of banked infra.
(b) COUPLING. Construct a coupling of the two killed chains from i,j that meets within Θ(1) regenerations
    w.p. ≥ δ (maximal coupling per step using the single-step window minorization), handling big jumps by
    coupling them maximally too. Meeting ⟹ overlap. Cleanest probabilistically, heaviest in Lean (no
    Mathlib coupling-for-Markov-kernel machinery — would build it).
(c) DENSITY / LOCAL LIMIT. Transfer the Γ(2,C/2) lower density bound (banked window-integral convergence)
    to a discrete L-fold-convolution lower bound on the band ⟹ minorization δ. Needs arithmetic
    local-limit handling of the σ(m) factor (irregular) — hardest analytically.
(d) ESCAPE wall standalone (tractable warm-up regardless of route): per-step large-drop tail
    P(Δ > b) ≤ C e^{−cb} uniform in R, from the erdosWeight formula + sigmaR bounds + the
    √n−√(n−m) ≥ b/3 exponential. This is needed by (a)/(b) as the big-jump control.

## Terminal conditions
- Success: `erdos_partition_limit_exists` unconditional, audit GATE_EXIT_0, clean-3, 0 sorry.
- Avenue death: a written counterexample/obstruction (like the escape-constant finding above), then
  backtrack to the next avenue.

## Plan of attack
Start with (d) (escape per-step tail — concrete, needed everywhere), in parallel re-design the engine
wiring toward (a) (tail-sup + full-support overlap). Keep (b)/(c) as fallbacks. The escape-constant
finding means the FINAL connection (`tendsto_of_killed_doeblin` / `DoeblinWalls`) will likely be
re-stated against `tailsup_summable` rather than the escape-split — a framework revision, flagged here
because it touches banked code.

## UPDATE (resolution of the escape-constant subtlety — multi-scale engine)
The escape-constant problem is resolved WITHOUT a growing-step recursion, by a multi-scale limit:
  • for each fixed band width B: `V(R) ≤ (1−δ_B)·V(R−B) + δ_B·bnd B` (R ≥ R₀(B)), where
    `bnd B = 3·ε_B·M/δ_B` and ε_B = escape mass below band B for the L_B-step kernel;
  • `limsup_le_of_step_contraction_const` (banked) ⟹ `limsup V ≤ bnd B`;
  • this holds for EVERY B, and `bnd B → 0` (ε_B = e^{−cB} → 0, δ_B ≥ δ₀ > 0 since L_B ~ B steps
    over-mix the band) ⟹ `tendsto_zero_of_limsup_le_all` (banked) ⟹ `V → 0` ⟹ h converges.
Engine banked in StepContractionConst.lean; the multi-scale capstone in RenewalMultiB.lean
(`tendsto_of_tailOsc_multiB`, `tendsto_of_killed_doeblin_multiB`), reusing `doeblin_escape_bound`
unchanged. The two analytic walls are now correctly B-indexed:
  WALL 1':  ∀ B, overlap δ_B > 0 on band {rnk ≥ R−B} for the L_B-step killed kernel (δ_B ≥ δ₀);
  WALL 2':  ∀ B, escape mass below band B ≤ ε_B, with 3·ε_B·M/δ_B → 0  (ε_B → 0 fast).
This is the genuine renewal structure (Θ(R)-fold geometric mixing) in a form the banked engine drives.

## CORRECTION (Opus, honest) — the all-pairs overlap is FALSE; the real wall is V→0 (renewal)
Pressure-testing the wall against the kernel: `DoeblinWalls`/`DoeblinWallsMultiB` quantify the overlap
over ALL i,j with rnk ≥ R. For a far-apart pair (rnk i = R, rnk j = R+G, G large) the L-step laws
concentrate at ranks ≈ R−O(L) and ≈ R+G−O(L), DISJOINT, so ∑min = 0 < δ. The overlap conjunct is
unsatisfiable ⟹ bricks 66/69/71/72 are true implications but conditional on a FALSE premise; they do
NOT reduce HR to true facts. (Earlier "reduced to two satisfiable walls" was wrong.)

What's sound: every abstract engine (doeblin_escape_bound, doeblin_average_diff_bound, pair_contract,
tailsup_summable, tendsto_of_center_tracking, StepContraction(+Const), killed_harmonic_pow,
KilledStochastic, tendsto_of_tail_osc_to_zero, the multi-scale fix). The ERROR is the capstone
*structure*: overlap must be COMPARABLE-rank only (pair_contract), with far pairs handled by the
band/center structure.

Reduction to the true core: with c R := tailInf (monotone bounded ⟹ links summable for free) and
V R := tailOsc, `tendsto_of_center_tracking` (and equally `tendsto_of_tail_osc_to_zero`) reduce
h-convergence to **V R → 0** (tail oscillation → 0). And V is antitone-bounded so V R → V_∞ ≥ 0; the
whole difficulty is **V_∞ = 0**. The naive bounds give only factor 1:
  • averaging+escape: V R ≤ (1−ε)V(R−B) + 2εM  (ε = escape; factor ≈ 1, useless);
  • far-pair: the δ-overlap contraction only applies to comparable ranks; the sup-achiever and
    inf-achiever of the tail can sit at far-apart ranks, where overlap = 0.
So V_∞ = 0 is the genuine renewal/tail-triviality result for the rank-descending σ-kernel — the real
hard analytic wall. Routes: (i) standard renewal/coupling (couple the chains, meeting time finite a.s.);
(ii) tail-triviality of the descending chain; (iii) a quantitative mixing/spectral-gap argument.
DISPATCHED to ChatGPT for the cleanest Lean-formalizable argument. Escape estimate (input (B)) is being
ground in parallel (uniform exp-moment ∑ Pker(i,k)e^{s(rnk i−rnk k)} ≤ M for s < C/3, then Markov).

## FIND (Opus) — escape wall is essentially banked: far_erdos_tail_le
`far_erdos_tail_le` (MassRateApprox2): ∑_{m ∈ Icc (⌊n^{2/3}⌋+1) (n−1)} erdosWeight n m ≤ K/n eventually.
This is the big-jump mass (jump m > n^{2/3} ⟺ rank drop ≳ n^{1/6} ~ R^{1/3}), bounded by K/n → 0. Over
kernelMass → 1, the per-step P(rank drop > ~R^{1/3}) ≤ K'/n ~ K'·9/R². Union bound over the ~R-step
descent: P(any big jump) ≲ R/n → 0 ⟹ w.h.p. the chain makes NO big jump and descends by ≤ R^{1/3}/step.
So escape (input B) is in hand (modulo wiring far_erdos_tail_le into the band structure; note its natural
band ~R^{1/3} GROWS with R, so the contraction engine wants the growing-band/tail-sup variant, not fixed
B). The ONLY genuine wall left is the OVERLAP / renewal convergence V→0 (comparable-rank Doeblin →
far-pair convergence) — dispatched to ChatGPT. model_tail_le + erdosWeight_sub_model_le give the
model-vs-kernel control likely needed for the comparable-rank overlap too.
