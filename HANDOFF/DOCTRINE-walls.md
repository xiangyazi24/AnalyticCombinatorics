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

## RESOLUTION (Opus + ChatGPT R2) — correct capstone banked; lone wall = ErdosAlignment
ChatGPT R2 confirmed the all-pairs overlap is unprovable (matches my finding) and gave the correct
deterministic input: the m-step terminal-law ALIGNMENT  ov(P̃^m(i,·),P̃^m(j,·)) ≥ 1−(1−δ)^m−ε (high
starts). Then |h i−h j| = |μ_i h − μ_j h| ≤ 2M(1−ov) ≤ 2M((1−δ)^m+ε) ⟹ V∞=0. BANKED clean-3:
  brick 73 RenewalAlign.tendsto_of_renewal_alignment (the capstone, full-support overlap + squeeze);
  brick 74 ErdosAlignConnect.erdos_partition_limit_exists_of_alignment (reduces HR to ErdosAlignment).
This SUPERSEDES the conditional-on-false bricks 66/69/71/72 (kept as valid-but-vacuous infra).

### Lone remaining wall: ErdosAlignment J  (the m-step terminal-law overlap)
Decomposes into:
  (B′) comparable-rank single-step overlap δ* > 0: for rnk i = rnk j (≥ R₁),
       ∑_k min(Pker i k, Pker j k) ≥ δ*  — kernel L¹-continuity in the start index; provable from banked
       erdosWeight_sub_model_le + model_tail_le + kernelMass→1.
  (ITER) descent-coupling: single-step comparable overlap ⟹ m-step terminal overlap ≥ 1−(1−δ*)^m, via
       the two chains synchronizing at the shared lower rank levels they both descend through. THE hard
       analytic core (needs a coupling/overlap-iteration; Mathlib has no Markov coupling). Escape (no big
       jumps, far_erdos_tail_le) feeds both. Dispatched R3 to ChatGPT for the explicit ITER argument.

## CORRECTION 2 (Opus + ChatGPT R3) — bricks 73/74 alignment also unsatisfiable; correct = windowed ITER
ChatGPT R3 §0: the clean alignment ov(P̃^m(i,·),P̃^m(j,·)) ≥ 1−(1−δ)^m−ε for arbitrary far ranks is
FALSE (counterexample: deterministic descent, rank gap > m ⟹ disjoint m-step laws ⟹ overlap 0). So
bricks 73/74's `halign` hypothesis is unsatisfiable for far pairs — a SECOND conditional-on-false capstone.
They stay as valid-but-vacuous infra; the correct reduction needs the windowed deterministic ITER.

### Correct structure (ChatGPT R3, saved verbatim in HANDOFF/chatgpt-R3-iter-design.md)
NO probabilistic coupling — pure finite-sum algebra over the reachable Finset:
  • (B_W) windowed minorization: |rnk x − rnk y| ≤ W ⟹ ∑_z min(P x z, P y z) ≥ δ. (provable from
    (B′) exact-rank overlap + local-TV regularity: ov(μ,ν') ≥ ov(μ,ν) − ‖ν−ν'‖₁.)
  • deterministic coupling pair (ρ_t, U_t): ρ_t = coalesced common-minorant mass, U_t(x,y) = unmatched
    pair mass. C_{x,y}(z) = if Good_W x y then min(Px z, Py z) else 0; Lres = Px − C, Rres = Py − C;
    Kres(x,y;a,b) = Lres·Rres/(1−cmass) residual product.
  • MARGINAL INVARIANT (crux mechanical lemma, induction on t):
      ρ_t(z) + ∑_y U_t(z,y) = P^t(i,z);  ρ_t(z) + ∑_x U_t(x,z) = P^t(j,z).
    ⟹ ρ_t ≤ min(μ_t, ν_t) ⟹ ∑ρ_t ≤ overlap(μ_t,ν_t).
  • CORE INEQ: u_{t+1} = ∑ U_t(x,y)(1−cmass(x,y)) ≤ (1−δ)u_t + δ·b_t,  b_t = unmatched mass OUTSIDE
    the window. (cmass ≥ δ on good pairs.)
  • scalar_rec_solve (BUILT, ScalarRecSolve.lean, brick 75): u_m ≤ q^m u_0 + δ∑ q^{m−t−1} e_t.
  ⟹ iter_window_overlap: overlap(P^m(i,·),P^m(j,·)) ≥ 1 − (1−δ)^m − δ∑(1−δ)^{m−t−1} e_t.

### The LONE deep analytic wall (now precisely isolated): the bad-mass bound
  b_t = unmatched mass outside the rank window ≤ e_t  (with ∑_{t<m} b_t ≤ E small, the aggregate form is
  easier). This is the rank-difference walk ENTERING the window — a local-CLT / recurrence statement
  (A = no-big-jumps, banked, feeds it but does NOT prove it). ChatGPT R3 §7: keep layers separate
  (A + rank-decrement asymptotics ⟹ bad-mass; B_W ⟹ one-step coalescence; finite-sum ITER ⟹ m-step).

NEXT (mechanical, in progress): build the ITER (ρ_t,U_t marginal invariant + core ineq + iter_window_overlap)
over the reachable Finset, then the capstone tendsto_of_renewal_alignment' taking (B_W)+bad-mass.
Lone hard wall left after that: the bad-mass/recurrence local-CLT.

## MILESTONE (Opus) — bricks 75-76: the deterministic windowed-coupling ITER is DONE
ScalarRecSolve.scalar_rec_solve + ITERCoupling.iter_window_overlap banked clean-3. The entire renewal
ALIGNMENT is now mechanized as finite-sum algebra (~20 lemmas, no probabilistic coupling library):
  ρ_t (coalesced common minorant) + U_t (unmatched pair mass), marginal invariant
  ρ_t z + ∑_y U_t z y = P^t i z  (left_marginal/right_marginal, the crux induction) ⟹ ρ_t ≤ min(μ_t,ν_t)
  ⟹ ∑ρ_t ≤ overlap;  unmatched mass contracts  u_{t+1} ≤ (1−δ)u_t + δ·badMass_t  (umass_core)
  ⟹ iter_window_overlap:  overlap(P^m i, P^m j) ≥ 1 − (1−δ)^m − δ·∑(1−δ)^{m−t−1}·badMass_t.

### Remaining chain (precisely isolated)
(1) INSTANTIATION GLUE [mechanical]: apply the abstract ITER (over Fintype `Fin (N+1)`) to the concrete
    `killedKer Pker rnk J` — Mpow ↔ KPowK correspondence, killedKer stochastic on the reachable set,
    overlap correspondence.
(2) E-CORRECTED CAPSTONE [mechanical]: the banked `tendsto_of_renewal_alignment` takes the (false) clean
    alignment; replace with one consuming iter_window_overlap's E-corrected bound + the V→0 squeeze
    (forcing → 0 requires sup over high i,j of badMass-sum → 0).
(3) TWO ANALYTIC WALLS:
    (B_W) windowed minorization  δ ≤ cmass(x,y) for |rnk x − rnk y| ≤ W  — kernel L¹-continuity in the
        start index; provable from banked erdosWeight_sub_model_le + model_tail_le + kernelMass→1. [hard
        but mechanical-ish estimate]
    (BAD-MASS) badMass_t ≤ e_t with e_t → 0 appropriately — the rank-difference walk entering the rank
        window; a RECURRENCE / local-CLT statement. **THE lone irreducible analytic wall** (Mathlib has
        no local-CLT/recurrence for such walks; (A)=far_erdos_tail_le feeds it but does not prove it).

So HR is now reduced — on the mechanical side, essentially completely — to the single bad-mass/recurrence
fact (plus the L¹-continuity estimate). That recurrence is the genuine analytic frontier of path A.

## REFINED STRUCTURE (Opus) — center-tracking resolves far pairs; ITER is for COMPARABLE pairs only
The far-pair obstruction recurs at every "overlap-for-all-pairs" formulation (incl. the E-corrected one):
a far pair (rnk i = R, rnk j = R+G, G≫m) has overlap ≈ 0 at any fixed m, so V(R)=sup over ALL pairs
can't be squeezed by overlap. The CORRECT resolution uses the banked `tendsto_of_center_tracking`:
  • block centers c(R); block oscillation V_blk(R) = osc over COMPARABLE pairs (|rnk i − rnk j| ≤ W);
  • h converges if  V_blk → 0  AND  ∑_R |c(R+1) − c(R)| < ∞  (summable center links)  AND
    |h n − c(rnk n)| ≤ V_blk(rnk n)  (tracking).  [exactly the banked CenterTracking interface]
Far pairs are handled by  |h i − h j| ≤ V_blk(rnk i) + |c(rnk i) − c(rnk j)| + V_blk(rnk j), the middle
term ≤ tail of the summable links → 0.  The ITER overlap is then needed ONLY for COMPARABLE pairs
(|rnk i − rnk j| ≤ W) — which IS satisfiable (comparable starts are in the window, so badMass is small
and they align: overlap ≥ 1 − (1−δ)^m − small).

### So the corrected remaining build:
(C1) `tendsto_of_block_overlap` capstone: comparable-pair m-step overlap (≥ 1−(1−δ)^m − small) ⟹
     V_blk → 0 and summable links ⟹ via `tendsto_of_center_tracking` ⟹ h converges. [mechanical]
(C2) instantiate ITER for the killed kernel (Mpow ↔ KPowK) restricted to comparable pairs. [glue]
(C3) (B_W) windowed minorization δ ≤ cmass (L¹-continuity). [hard estimate, within reach]
(C4) comparable-pair bad-mass: for |rnk i − rnk j| ≤ W (≥ J), badMass_t → 0 as both chains descend to
     the absorbing boundary {rnk < J} (which lies entirely inside the window W ≥ J, so all boundary
     pairs are "good"). The RATE (geometric in R, for the summable links) is the analytic content —
     now about COMPARABLE-pair absorption, NOT the far-pair recurrence. Still analysis, but tractable.
The deep far-pair recurrence/local-CLT is AVOIDED by center-tracking. The lone analytic content is the
comparable-pair bad-mass decay (C4) + the L¹-continuity (C3). Both lean on the banked model machinery.

## HONEST REFINEMENT of C4 (Opus) — comparable bad-mass is still a coalescence/diff-walk statement
Earlier I framed C4 as "comparable pairs absorb into the window, so bad-mass → 0 — tractable." That is
too optimistic. For a same-rank pair (rnk i = rnk j, indices differ), the two coupled chains have a
rank-DIFFERENCE that starts at 0 but does a mean-0 random walk (difference of two ~Γ(2,C/2) decrements),
spreading like √t. The bad-mass b_t = unmatched mass with |rnk-difference| > W. So b_t can GROW in t
until coalescence. The ITER's scalar solve weights it by (1−δ)^{m−t−1} (downweighting old steps), so
what's needed is essentially: the unmatched mass coalesces (δ chance/step while in window) FASTER than
the diff-walk carries it out of the window. This is a genuine recurrence/coalescence estimate for the
rank-difference walk — NOT trivially "they absorb." Center-tracking removes the UNBOUNDED-gap far pairs
(good), but the residual comparable-pair bad-mass is still real analysis (local-CLT/recurrence flavor for
a bounded-start diff walk). It IS more tractable than the unbounded far-pair version (bounded initial
gap; the window W can be taken ≥ the typical √m spread by choosing m ~ W²), but it is NOT mechanical.

So the lone irreducible analytic content of path A is: (C3) Pker L¹-continuity in the start index +
(C4) the comparable-start rank-difference-walk coalescence/bad-mass bound. Both are genuine analysis
leaning on the σ-kernel asymptotics (banked model machinery); C4 is the harder, and how deeply to build
the coalescence/local-limit foundations is a scope decision. Everything mechanical (bricks 61-77) is done.

## HONEST FINAL FRAMING (Opus) — BOTH remaining walls are σ-averaging / arithmetic-local-limit analysis
Scoping modelSummand (= σ(m)·exp(−(massLam/√n)m)·(1/n + m/n² − …)) shows C3 is NOT a routine calculus
estimate. The kernel L¹ distance ∑_z|Pker x z − Pker y z| compares the two rows at SHIFTED jump indices
(m_x = x−z vs m_y = y−z, differing by x−y), so it hinges on σ(m) vs σ(m + (x−y)) summed — the σ(m)
ARITHMETIC IRREGULARITY is the core difficulty, the SAME σ-averaging / arithmetic-local-limit flavor as
C4 (the diff-walk coalescence). So:

  Both C3 (windowed minorization via L¹-continuity) and C4 (comparable bad-mass / coalescence) reduce to
  AVERAGED control of the σ-weighted kernel under index shifts — i.e. an arithmetic local-limit theorem
  for the σ(m)-weighted predecessor walk. This is the genuine irreducible analytic content of Erdős's
  elementary Hardy–Ramanujan proof, and Mathlib has NO σ-averaging / local-limit machinery for it.

### Net, fully honest, status of path A
HR (erdos_partition_limit_exists) is reduced — with the ENTIRE renewal/coupling/center-tracking machinery
mechanized clean-3 (bricks 61-78) — to a single class of fact: an arithmetic local-limit / σ-averaging
estimate for the Erdős kernel under index shifts (yielding both the windowed minorization δ and the
coalescence/bad-mass bound). Building that from scratch in Lean means constructing σ-average and
local-limit foundations Mathlib lacks — a major, multi-week+ undertaking whose SCOPE (how deep to build
those probability/number-theory foundations, vs. a different attack) is the senior author's decision.
The banked Model machinery (modelIntegral, erdos_kernel_window, erdosWeight_sub_model_le, far_erdos_tail_le,
kernelMass→1) is the starting capital, but the σ-shift averaging is the new content.
This is the genuine research frontier of path A — not a mechanical gap.

## BREAKTHROUGH (Opus, 06-08) — C3 minorization is ELEMENTARY via σ(m) ≥ m (no σ-averaging!)
ChatGPT (ask-gpt ac) correctly said: use BLOCK overlap not L¹, and the content is ∑_m min(σ(m),σ(m+d))
≥ cN. It worried a σ-free bound fails ("σ≥1 gives Θ(N^{-1/2})"). BUT it (and I earlier) missed:
σ(m) ≥ m (since m ∣ m ⟹ sigmaR m = ∑_{d|m} d ≥ m). In the window jump m ∈ [a√x, b√x] this gives
σ(m) ≥ a√x, and ∑ over ~(b−a)√x terms gives Θ(x) — the RIGHT order. So:

  ∑_k min(Pker x k, Pker y k)  ≥  (Θ(1)/x)·∑_{j∈[a√x,b√x]} min(σ(j), σ(j+(y−x)))
     ≥ (Θ(1)/x)·∑_j min(j, j+(y−x))  [σ≥self]  ≥ (Θ(1)/x)·(b−a)√x·(a−D)√x  = (b−a)(a−D)·Θ(1) = δ>0,

where |y−x| ≤ D√x (comparable, D=2W/3), window left endpoint a > D, smooth factor 1/k·exp(−C(√x−√k))/km
= Θ(1)/x on the window (k~x, exp∈[e^{−Cb/2},e^{−Ca/2}], km→1). FULLY ELEMENTARY: needs only σ(m)≥m,
σ(m)≤... not even needed, k~x, exp monotonicity, kernelMass→1 (banked). NO σ-summatory, NO local-limit,
NO concentration. This bypasses the σ-averaging wall I'd flagged. The minorization δ(W)>0 (decreasing in
W via e^{−CW}). C4 (bad-mass/diff-walk) still to assess, but C3 is cracked elementarily.
Formalizing in ErdosMinorization.lean: sigmaR_ge_self → block-min → smooth-factor → δ.

## C3 BANKED + C4 SHARPENED (Opus, 06-08) — bricks 79/80/81

- **Brick 79 `Pker_window_minor` (ErdosMinorization.lean), clean-3, gated.** δ = exp(−C(2+D))/8 > 0,
  UNIFORM for x ≥ 16 (rank ≥ 12). The σ-averaging wall is bypassed for C3. Done, on main.
- **Brick 80 `harmonic_diff_le_overlap` (HarmonicOverlap.lean), clean-3.** Route-independent half:
  bounded m-step-harmonic h ⟹ |h i − h j| ≤ 2B(1 − overlap(pᵢ,pⱼ)). Pure linear algebra.
- **Brick 81 `umass_le_one_sub_occupation` / `overlap_ge_occupation` (ITEROccupation.lean), clean-3.**
  Telescoping umass_core gives umass m ≤ 1 − δ·∑_{t<m} goodMass t (cumulative WINDOW OCCUPATION),
  hence overlap(Pᵐ i,Pᵐ j) ≥ δ·∑ goodMass t.

### The single remaining input (C4, sharpened to occupation form)
Single-window single-pass ITER is PROVABLY insufficient for C = π/√6 (self-consistency 2 ln v = c v,
c ≈ ⅔C ≈ 0.855 > 2/e ≈ 0.736 has no solution — derived by Opus, independently confirmed by ChatGPT R5).
The occupation form fixes this: it credits EVERY return of the rank-difference walk D_t = rnk Xₜ − rnk Yₜ
to the window, not just the first pass. So the ENTIRE wall is now ONE lemma:

  **(C4-occ)  ∑_{t<M} goodMass t  →  1/δ   (i.e. ≥ (1−ε)/δ for M = M(rank) large), as rank → ∞.**

goodMass t = unmatched-coupling mass currently inside the rank window at step t. This is the window
LOCAL TIME of the residual coupling. D_t is a bounded-increment, centered (same marginal law for
comparable ranks), positive-local-variance walk on a finite rank ladder; it is recurrent, so its window
local time over the ~rank(n) steps before absorption → ∞. ChatGPT R5 recommends a finite Lyapunov /
hitting argument for D_t (NOT Mathlib martingales/Azuma, which lack a usable API; NOT a Tauberian bypass,
judged longer). Plan: bound goodMass t below by (window-fraction)·umass t and the residual-walk return
structure; the genuine analytic content is the recurrence/return-count of D_t under the Erdős kernel
(uses banked far_erdos_tail_le for bounded increments + erdos_kernel_window for the local variance).
This is the lone open frontier; everything else (C3 + both convergence halves) is banked clean-3.

## FINAL REDUCTION (Opus, 06-08) — bricks 82/83, the wall is ONE probability lemma + instantiation

The occupation form is realized via a GREEN POTENTIAL (ChatGPT R6/R7, verified+formalized):
- **Brick 82 `occupation_ge_green_tight`:** for any Kres-Poisson-subsolution g, `g i j − greenMass M ≤ ∑ goodMass`.
- **Brick 83 `greenT_subsolution`:** the finite-horizon `greenT T = ∑_{t<T} KresAct^[t] goodIndic` IS a
  subsolution FOR FREE (Poisson identity `KresAct(greenT)=greenT−goodIndic+KresAct^[T]goodIndic`,
  nonneg tail). No recurrence needed for the subsolution — finite-sum algebra.

### The lone analytic input (now exactly pinned)
  **greenT T (i,j) ≥ (1−ε)/δ for high-rank comparable starts** — equivalently the EXPECTED LOCAL TIME
  `∑_{t<T} P(|D_t| ≤ W) ≥ (1−ε)/δ`. A mean-0, bounded-increment, local-variance-v walk has
  `P(|D_t|≤W) ≳ W/√t` (local-CLT lower bound), so `∑_{t<T} ≳ W√T`; with T up to the absorption time
  ~ rnk(i) → ∞, `W√T ≥ 1/δ = e^{cW}` once `rnk(i) ≥ e^{2cW}/W²` (constant, W fixed). Chebyshev ALONE gives
  only ~W² ≪ 1/δ — the √T (multi-excursion recurrence) is irreducible. The genuine content is the
  local-CLT/recurrence LOWER bound `P(|D_t|≤W) ≳ 1/√t` (equivalently `∑_t P(D_t=0)=∞`), which Mathlib
  lacks a ready form of. Per-step moments feeding it (banked): erdos_kernel_window (local variance v>0),
  far_erdos_tail_le (bounded increments), kernelMass→1. THIS is the method-flexibility point.

### Remaining instantiation (mechanical-ish)
Instantiate the abstract ITER (α=Fin(N+1), P=killed Pker, rnk) for `hhit` in ErdosLimit's
`erdos_partition_limit_exists_of_hit`. Subtlety: Pker_window_minor gives δ only for rank ≥ 12, so the
occupation predicate generalizes from GoodW to `Good ⊆ GoodW` (minorizable high-rank window); bricks
81/82/83 generalize cleanly (proofs never used GoodW's specific form). Then harmonic_diff_le_overlap (80)
+ overlap→1 ⟹ hitVal converges.

Banked clean-3 this campaign night: 79 (δ minorization), 80 (harmonic bridge), 81 (occupation),
82 (Green telescoping), 83 (greenT subsolution-for-free). HR fully architected; only non-mechanical
gap is the local-time/recurrence lower bound.

## DETERMINISTIC TANAKA OCCUPATION MACHINERY BANKED (Opus, 06-08), bricks 84–90
The local-time lower bound (occupation → ∞) is now built in the deterministic finite-sum substrate
(NO measure theory, NO local-CLT), via Tanaka + Paley–Zygmund:
- 84 mean_sq_cubed_le: (∑pf²)³ ≤ (∑p|f|)²(∑pf⁴)  [Paley–Zygmund anti-concentration].
- 85 abs_drift_nonneg/le/eq_of_far: per-step |D|-submartingale drift, compensator = window local time.
- 86 occupation_ge_tanaka: window-occ ≥ (E|D_T| − E|D_0|)/b  [telescoped over distPow].
- 87 sq_moment_telescope/sq_moment_ge: Doob for D², lower QV E[D_T²] ≥ E0²+v₀T.
- 88 fourth_drift_le: per-step 4th-moment drift ≤ 8b²Dx²+3b⁴.
- 89 sq_moment_le + fourth_moment_telescope_le: upper QV + 4th-moment telescoping.
- 90 locVar_le + fourth_moment_le_quadratic: E[D_T⁴] ≤ E0⁴+8b²E0²T+8b⁴T²+3b⁴T (quadratic).
Combine: (E|D_T|)²·CT² ≥ (E[D_T²])³ ≥ (v₀T)³ ⟹ E|D_T| ≥ c√T (capstone, next) ⟹ occupation → ∞ > 1/δ.

### ⚠ Instantiation subtlety: D is only an APPROXIMATE martingale for Pker
D = rnk X − rnk Y under the product walk has E[D'] − D = −(μ(rnk X) − μ(rnk Y)) where μ(r) = mean
rank-decrement at rank r. For the Erdős kernel μ(r) ≈ 3/2 (rank-independent to leading order) but the
rank-DEPENDENCE gives |E[D'] − D| ≤ η with η ~ 1/√n → 0 (NOT exactly 0). So the exact-martingale bricks
84–90 do not instantiate verbatim. Options: (a) η-robust versions (QV/Tanaka identities pick up error
terms ≤ 2η·∑E|D_t|; manageable since η·T_coalesce ~ 1/√n → 0 ≪ W for high rank — matches convergence
as rank→∞); (b) scale-function transform φ (harmonic for Pker, so φ(X)−φ(Y) is an EXACT martingale) —
needs φ regularity for the increment/variance bounds. A drift HURTS occupation (chains drift apart, no
return), so η must be threaded as → 0 with rank; this is precisely why HR convergence is a rank→∞ statement.
The exact-martingale machinery is the rank→∞ backbone; the η→0 control is the bridge to discharge next.

## ABSTRACT + η-ROBUST OCCUPATION BACKBONE COMPLETE (Opus, 06-08), bricks 79–94
The entire recurrence/occupation content (the conceptual wall that needed local-CLT/martingale machinery)
is mechanized clean-3 in elementary deterministic form, INCLUDING η-robustness for the approximate-
martingale Erdős kernel. occupation_unbounded_eta (brick 94): for an η-approx-martingale, bounded-
increment-b, locVar≥v₀, |D|≤R walk with 0<v₀−2Rη, the window occupation exceeds any target. Trivial
E[D_T⁴]≤R⁴ + linear lower QV ⟹ PZ gives (E|D_T|)²≥((v₀−2Rη)T)³/R⁴→∞.

### CONCRETE Pker INSTANTIATION ROADMAP (the remaining phase)
Infrastructure (all over ℕ; for fixed i,j the killed chain lives on {0..max(i,j)}, effectively finite):
- killedKer P rnk J (KilledHarmonic.lean): identity-absorb below J, Pker above.
- hitVal P rnk J u (RenewalHitPot.lean): harmonic extension; hitVal_eq the 1-step relation;
  killed_harmonic_pow: hitVal is harmonic for every KPowK L (killedKer) — the m-step killed law.
- Goal hhit: ∀ᶠ J, ∃ L, Tendsto (hitVal Pker rnk J u) atTop (𝓝 L).
Steps:
1. Finite-state setup: restrict to Fin(N+1) (N ≥ max start); killedKer stochastic (check Pker_mass:
   ∑_{range n} Pker = 1 above J; identity row below). hKsum/hKnn for the abstract machinery.
2. Concrete per-step Erdős moments (the genuine analytic inputs): mean rank-decrement μ(r) and the
   approx-martingale bound |E[ΔD]| ≤ η(r) ~ 1/r² for comparable pairs (from the jump law / erdos_kernel_
   window); local variance v₀ > 0 (erdos_kernel_window gives the Θ(1) rank-step variance); bounded
   increment b (far_erdos_tail_le).
   ⚠ USE THE UNROUNDED SCALE (Opus 06-08): rnk = ⌊3√n⌋, and the ROUNDED difference D = ⌊3√X⌋−⌊3√Y⌋ has a
   Θ(1) floor perturbation (frac(3√X)−frac(3√Y) is Θ(1) for comparable X,Y) — it is NOT an approximate
   martingale. FIX: take the martingale coordinate to be the UNROUNDED D̃ = 3√X − 3√Y. Then
   μ̃(n) = 3√n − 3·E[√(n−m)] = μ̄ + c/√n + O(1/n) (smooth; expand √(1−m/n), μ̄ = (3/2)E[y], c = (3/8)E[y²],
   y = m/√n under the model density f(y) = (π²/6)y e^{−Cy/2}), so η̃ = |μ̃(X)−μ̃(Y)| ~ |c|·W·r/n^{3/2} ~ 1/r²
   (since n ~ r²). The window |D̃| ≤ b relates to the rnk-window |rnk X − rnk Y| ≤ W within O(1) slack
   (|D̃ − D| < 1), so the occupation/minorization transfer with an O(1) window adjustment. This avoids the
   floor being fatal. The concrete computation: expand μ̃ via the decrement moments E[y], E[y²] from
   erdos_kernel_window (Gamma integrals of f), and bound η̃ via the c/√n correction's rank-derivative.
3. ⚠ PRODUCT→COALESCING BRIDGE (the key remaining analytical piece, mechanism worked out):
   occupation_unbounded_eta is for a STOCHASTIC (mass-conserving) walk, but Umat is SUBSTOCHASTIC. Use the
   CONDITIONED walk Ûmat(t) := Umat(t)/umass(t) (= Umat conditioned on not-yet-coalesced). Ûmat is
   stochastic and evolves by the renormalized kernel K̂res(x,y,·) := Kres/(1−cmass) = Lres⊗Rres/(1−cmass)²
   (∑ K̂res = 1). Apply occupation_unbounded_eta to (K̂res, D=rnk-diff, Ûmat₀=δ_{(i,j)}) ⟹ the conditioned
   window occupation ∑ĝoodMass(t) → ∞. Bridge to umass: goodMass(t) = umass(t)·ĝoodMass(t) (un-normalized
   = mass × conditioned fraction). Brick 81 gives δ·∑_{t<M} goodMass ≤ 1 (umass ≥ 0). Contradiction: if
   umass(t) ≥ ε for all t ≤ M then ∑goodMass ≥ ε·∑ĝoodMass → ∞, impossible. Hence umass(M) < ε for M
   large; umass nonincreasing ⟹ umass → 0. The K̂res moments: OFF-window K̂res = Kprod = P⊗P exactly
   (cmass=0 there), so mart-eta/v₀/b come from the product Erdős kernel; ON-window K̂res reweights the
   residual but the rank-diff increments stay ≤ b. THIS is the lemma to build (the conditioned-walk
   occupation + the ε-contradiction), then it consumes occupation_unbounded_eta directly.
4. Assembly: umass→0 ⟹ overlap(KPowK L i,KPowK L j)→1 (overlap_ge_occupation 81 / umass_eq) ⟹
   |hitVal i − hitVal j|→0 (harmonic_diff_le_overlap 80, hitVal bounded by u's bounds) for comparable i,j
   ⟹ (center-tracking CompContraction 77, far pairs via summable links) hitVal converges ⟹ hhit ⟹
   erdos_partition_limit_exists_of_hit. No conceptual wall; concrete-kernel analysis + the bridge.

## ABSTRACT OCCUPATION BACKBONE COMPLETE + η-robustness QUANTITATIVELY SOUND (Opus, 06-08), brick 91
occupation_unbounded (brick 91) closes the abstract chain: for a mean-preserving, bounded-increment (b),
uniformly-positive-local-variance (v₀) walk, the cumulative window occupation exceeds ANY target (hence
1/δ). The entire abstract recurrence content is now mechanized clean-3 in elementary deterministic form
(bricks 79–91), no measure theory, no local-CLT.

### η is small: the η-robust instantiation is feasible (KEY quantitative finding)
The drift η = |E[D'] − D| = |μ(rnk X) − μ(rnk Y)| where μ(r) = mean rank-decrement at rank r. For the
Erdős kernel μ(r) → 3/2 with a ~1/r correction, so μ'(r) ~ 1/r², and for comparable X,Y (|rnk-diff| ≤ W
= O(1)) η ~ |μ'(r)|·W ~ 1/r² (≈ 1/n, NOT 1/√n). Effect on the occupation chain:
- η-robust Tanaka (brick 86'): occ ≥ (E|D_T| − E|D_0| − η·T)/b  [off-window |D|-drift is ≤ η, not 0].
- η-robust QV (brick 87'): E[D_T²] ≥ E0² + v₀T − 2η·∑E|D_t| ≥ v₀T − 2ηTR; with η ~ 1/r², R ~ r,
  the correction 2ηTR ~ 2T/r ≪ v₀T at the optimal T ~ r². So lower QV survives.
- Optimal horizon: occ ≥ (c√T − ηT − W0)/b maximized at T ~ c²r²/4 gives occ ~ c²r/4 → ∞ ≫ 1/δ.
So the η-drift is negligible relative to the variance signal; the approach is sound. This is precisely
why HR convergence is a rank→∞ statement (η → 0 only as rank → ∞).

### Remaining concrete phase (η-robust re-derivation + Pker instantiation)
1. η-robust versions of bricks 85–91 (per-step |D|-drift and QV pick up ≤ η error terms; 4th-moment
   binomial's mean-zero term becomes ≤ η; PZ brick 84 needs NO change). Each mirrors the exact version
   with a tracked η. Moderate, mechanical re-derivation.
2. Concrete per-step Pker moments: mean rank-decrement μ(r) and |μ(X)−μ(Y)| ≤ η(r) ~ 1/r² (from
   erdos_kernel_window / the jump law), local variance v₀ > 0 (from erdos_kernel_window), bounded
   increment b (from far_erdos_tail_le).
3. ITER instantiation: α = Fin(N+1), P = killed Pker, rnk; Good ⊆ GoodW = minorizable high-rank window;
   δ from Pker_window_minor; combine occupation_unbounded(η-robust) + overlap_ge_occupation (81) +
   harmonic_diff_le_overlap (80) ⟹ hitVal converges ⟹ erdos_partition_limit_exists_of_hit. No conceptual
   wall remains — concrete-kernel analysis + assembly.

## OCCUPATION LOWER BOUND: tent FAILS, Tanaka route VIABLE (Opus, 06-08, verified)

ChatGPT R8 proposed an explicit "tent" subsolution g = max(R−|D|,0)/b to make the lower bound elementary
(no local-CLT). VERIFIED FLAWED ("不盲信"): on-window Kres is SUB-stochastic (∑Kres = 1−cmass ≤ 1−δ;
coalescence removes exactly the high-potential mass near the tent peak), so ∑Kres·g ≥ (1−cmass)(g−1),
which is < g−1 whenever g > 1. The start (i,j) is on-window (comparable) and needs g(i,j) ≈ 1/δ ≫ 1, so
the tent cannot be a subsolution there. By LP duality the occupation potential greenT IS the maximal
subsolution, so NO elementary subsolution exceeds it — the recurrence content is irreducible. (ChatGPT
silently assumed ∑Kres = 1.)

VIABLE route (Tanaka + Paley–Zygmund, uses Mathlib's EXISTING martingale/Doob theory, NOT local-CLT):
  (1) lower quadratic variation: E[D_T²] ≥ v₀·(active steps) ≥ v₀·cT  (erdos local variance, banked-ish);
  (2) 4th-moment / BDG: E[D_T⁴] ≤ C·(v·T)²  (bounded increments far_erdos_tail_le);
  (3) Paley–Zygmund on D_T²: P(D_T² ≥ ½v₀T) ≥ c, hence E|D_T| ≥ c√T;
  (4) Doob/Tanaka: |D_t| − A_t is a martingale, compensator A_t = window local time (supported on
      |D_t| ≤ b, increment ≤ b), so E|D_T| = E[A_T] ≤ b·E[∑ 1_{|D_t|≤b}];
  (5) ⟹ window occupation E[∑_{t<T} 1_{|D_t|≤W}] ≥ E[A_T]/b ≥ c√T/b ≥ 1/δ once T ≥ b²/(c²δ²) (a
      constant; available since T ~ rnk(i) → ∞).
The genuine per-step analytic inputs (concrete Pker-kernel facts, bankable): mean-zero-off-window
E[ΔD]=0 (rank-step mean rank-independent), lower local variance v₀>0, bounded increment b, 4th-moment.
This is substantial but Mathlib-supported (martingale Doob decomposition exists). NEXT: build the per-step
moment lemmas + the Tanaka local-time bound, then the ITER instantiation (Good⊆GoodW generalization).

ARCHITECTURE DECISION (Opus, 06-08): do the Tanaka route in the DETERMINISTIC finite-sum substrate
(mirroring ITER/greenT), NOT Mathlib's measure-theoretic martingales. Define the product-walk
distribution M_prod(t) (both coords independent Pker steps, a prob dist on pairs, like Mpow);
then E[f(D_t)] := ∑_{x,y} M_prod(t)(x,y)·f(rnk x − rnk y), and all moments / the Doob compensator /
Paley–Zygmund become finite-sum identities (∑M_prod(t+1)|D| − ∑M_prod(t)|D| = ∑M_prod(t)·(one-step |D|
drift); the increasing compensator = window local time). Mathlib's predictablePart exists but bridging
deterministic-Umat ↔ measure-theoretic E[·] is avoidable and not worth the setup. Keep it finite-sum.

## KILLED-CHAIN INSTANTIATION: the ONE remaining analytic lemma (Opus + ChatGPT R11/R12, 06-08)
Abstract coupling machinery COMPLETE, 20 bricks (79-98): C3 minorization, harmonic→overlap bridge,
Green/occupation reduction, full Tanaka+Paley-Zygmund occupation (84-94), CoalesceBridge (95), smooth-scale
window transfer (96), D²-energy bridge (97), umass_tendsto_zero (98).

CRUX resolved (R12): applying coalescence to the KILLED chain (absorption ~r steps) needs L(i,j) =
P(no coalescence before both absorb) → 0 as start rank r → ∞. The D²-ENERGY route (97-98) has the WRONG
RATE (E ≤ R² loses the √r local-time scale; gives umass(r) ~ O(1), not → 0). The OCCUPATION route is
correct but occupation_unbounded_eta must be LOCALIZED: hypotheses needed only OFF the (high-rank) window
GoodHi (martingale |∑Khat·ΔD| ≤ η and variance ∑Khat·ΔD² ≥ v₀ off GoodHi; on-window arbitrary bounded —
the repelling drift is HARMLESS, charged to the occupation being lower-bounded), over the ACTIVE-PHASE
horizon M ~ r. The conditioned residual walk K̂res = Lres⊗Rres/(1−cmass)² is mart-eta OFF window
(=product there) which is all the localized lemma needs.

### THE single genuine analytic input (everything else is banked finite-sum):
  khat_residual_active_good_occupation_tends_infty:
    ∀ A>0, ∃ R0 M, ∀ comparable high-rank i,j (rnk ≥ R0, |ρi−ρj| ≤ W0),
      A ≤ ∑_{t<M} ∑_z K̂resᵗ(i,j)(z) · 1_{GoodHi z}
  (GoodHi z = Jhi ≤ rnk z.1 ∧ Jhi ≤ rnk z.2 ∧ |ρ z.1 − ρ z.2| ≤ Wρ, Jhi ≥ 16).
  = a 1-D recurrent bounded-increment walk, martingale+positive-variance OFF a fixed window, has expected
  window-visits before the rank clock descends r→Jhi tending to ∞ (the √r local time over the r-step
  descent). This is THE last probability lemma; it needs the concrete Erdős moments (off-window product
  drift η~1/r² [smooth ρ, μ̃ expansion], off-window variance v₀>0, bounded increment b, active-time→∞).
Then CoalesceBridge (95, with g = ĝ = goodMass/umass) gives umass M ≤ ε, hence overlap→1, hence
|hitVal i − hitVal j| → 0 (harmonic_diff_le_overlap 80), hence hitVal converges (center-tracking 77) ⟹ hhit.
Remaining FINITE-SUM (re-derivations/assembly): localized occupation lemma (generalize 92-94 to
off-window-only hyps + active horizon), GoodHi generalization of umass_core/brick 81, the final
killed_umass bridge, and the finite-state Fin(N+1) glue connecting KPowK/hitVal to the abstract Mpow/overlap.

## CONCRETE MOMENTS: smooth-scale resolution CONFIRMED + constants (Opus + ChatGPT R9, 06-08)
ChatGPT R9 independently confirmed the floor concern and the fix:
- Floored rnk=⌊3√n⌋ is NOT an approx-martingale coordinate: μ_floor(n) has an O(1) phase term F({3√n});
  comparable x,y differ in fractional phase by O(1), so |μ_floor(x)−μ_floor(y)| = Θ(1), NOT o(1/r). Fatal.
- FIX: martingale/tent coordinate = SMOOTH ρ(n) = 3√n (use Real.sqrt directly, no floor). Keep ⌊3√n⌋
  only for killing/window bookkeeping; transfer with constant slack |⌊ρx⌋−⌊ρy⌋|≤W ⟹ |ρx−ρy|≤W+2.
- For smooth ρ: μ_ρ(n) = E[ρ(n)−ρ(n−m)] = μ̄ + O(n^{−1/2}), and for comparable starts |x−y|=O(√n),
  |μ_ρ(x)−μ_ρ(y)| = O(n^{−1}) = O(r^{−2}). So η ~ 1/r² holds — but ONLY for smooth rank.
Constants (decrement y=m/√n ~ Gamma(2, λ=C/2), C=π/√6): μ̄ = 6√6/π; single-step smooth-rank variance
v = (9/4)Var(y) = 108/π²; product-difference walk v_D ≈ 2v = 216/π² > 0; increment b ~ (3/2)n^{1/6} on
m ≤ n^{2/3}. NORMALIZATION note: f(y)=(π²/6)y e^{−(C/2)y} integrates to 4 over (0,∞), not 1 — but moments
are normalization-independent ratios (∫yf/∫f), and actual Pker decrement = erdosWeight/kernelMass with
kernelMass→1 (banked), so use ratio moments. NEXT: formalize μ_ρ expansion (η~1/r²) + v_D>0 + b, set up
the smooth-ρ difference walk + K̂res, finite-state Fin(N+1), assemble to hhit. The floor showstopper is
RESOLVED; the route is sound.

## NO-BUILD WINDOW (server down 06-08): concrete η-rate scoped + bridge drafted (Opus + ChatGPT R13)
Server (uisai1) down; switched to draft-only (no build/commit of Lean) per Xiang. Verified-by-reading:
- R13's cited infra ALL EXISTS (grep-confirmed): modelSummand, sigmaMoment (= ∑' m^r σ(m) e^{−tm}),
  massLam=C/2 (massLam_sq: λ²=π²/6), sigmaMoment_le_power_sharp, erdosWeight_sub_model_le, main_range_error_le,
  sqrt_drop_second_order, exp_sqrt_drop_second_order, leftBlockMajorant (+summable). Plus sigmaMoment_zero/
  one/two_lambert and sigmaMoment_one/two_asymp_weak.
- KEY: the banked _asymp_weak give only the LEADING term with rate, e.g.
  |sigmaMoment 1 t − 2λ²/t³| ≤ 388/t²  (one term). R13 confirms μ̃ = μ̄ + O(1/√n) is INSUFFICIENT (gives
  2Rη ~ O(1), not < v₀). So the GENUINE remaining analytic input is the TWO-TERM Lambert expansions:
    sigmaMoment_one_two_term : |M₁ t − (2λ²/t³ − 1/(2t²))| ≤ K/t
    sigmaMoment_two_one_term : |M₂ t − 6λ²/t⁴| ≤ K/t³
    sigmaMoment_three_one_term : |M₃ t − 24λ²/t⁵| ≤ K/t⁴
  — extend the existing _asymp_weak proofs (boseReg/Lambert technique) by ONE order. THIS is the last hard
  analytic lemma (a Lambert/Bose-kernel moment expansion, NOT σ-local-averaging).
Route to μ̃ = μ̄ + μA/√n + O(1/n) (μ̄=3/λ, μA=3/(2λ²)): muNum = ∑ erdosWeight·rhoDrop, rhoDrop=3(√n−√(n−m));
expand erdosWeight via erdosWeight_sub_model_le (main-range weighted error O(1/n) using moments shifted
2,3,4→3,4,5 + sigmaMoment_le_power_sharp), model side via sqrt_drop_second_order + the two-term sigmaMoment
expansions; weighted tails via leftBlockMajorant (×(k+1) factor, exp still wins); normalize by kernelMass
(|kernelMass−1|≤K/n). Then two_term_local_lip ⟹ |μ̃ x − μ̃ y| ≤ K'/x = O(1/r²) ⟹ feeds
occupation_unbounded_loc (101) with c=v₀−2Rη>0.

### QUEUED DRAFTS (unverified, await server; do NOT assume correct):
- AnalyticCombinatorics/Ch8/Partitions/TwoTermLocalLip.lean — two_term_local_lip (the bridge above);
  full proof written blind, expect minor lemma-name/nlinarith fixes (abs_sub, Real.sqrt_lt_sqrt,
  div_le_div_iff₀). Verify FIRST when server recovers.

### STATUS 06-08 (Opus): LAST HARD ANALYTIC LEMMA CLOSED + course-correction
- ✅ `sigmaMoment_one_two_term` BANKED (commit ac6cf80, clean-3, 0 sorry):
  |M₁ t − (2(π²/6)/t³ − 1/(2t²))| ≤ K/t for 0<t<1. Route = Riemann-sum of
  G(x)=x·boseReg0′(x) via general `riemann_sum_Ioi_sub_integral_bound`
  (MassRateRiemannGeneral.lean — was an untracked never-built draft, now fixed+banked),
  with ∫₀^∞ G = 1/2 from G=(x·boseReg0)′−boseReg0 + improper FTC
  (`integral_Gw_Ioi`). New file: MassRateMomentOneTwoTerm.lean.
- ✅ `sigmaMoment_two_one_term` = banked `sigmaMoment_two_asymp_weak`
  (|M₂ − 6(π²/6)/t⁴| ≤ C/t³). NO new work needed.
- ✅ M₃: the μ̃ O(1/n) REMAINDER only needs an UPPER BOUND E[y³]=O(1), i.e.
  M₃ ≤ K/t⁵, which is the BANKED `sigmaMoment_le_power_sharp 3`. The sharp
  `sigmaMoment_three_one_term` (24λ²/t⁵) is NOT needed → NO order-4 boseKernel4/
  reg4 certificate required. This removes the last anticipated hard sub-wall.
- ✅ `two_term_local_lip` (brick 103, TwoTermLocalLip.lean) verified+banked earlier.
- ⇒ ALL moment inputs for the μ̃ expansion now exist. Remaining = pure ASSEMBLY
  (no hard analysis): define muNum=∑ erdosWeight·rhoDrop (rhoDrop=3(√n−√(n−m))),
  muTilde=muNum/kernelMass; split main-range (erdosWeight_sub_model_le, modelSummand
  carries the kernel expansion) + tail (leftBlockMajorant); model side via
  sqrt_drop_second_order + M₁(2-term)/M₂(1-term)/M₃(≤bound); normalize kernelMass;
  ⟹ muTilde = μ̄ + μA/√n + O(1/n); then two_term_local_lip ⟹ |μ̃ x−μ̃ y| ≤ K'/x
  = O(1/r²) ⟹ occupation_unbounded_loc (101) ⟹ ... ⟹ hhit.

### CORRECTION 06-08 (Opus): M₃ LEADING term IS needed after all (prior note wrong)
Re-derived the μ̃ order-counting two ways (modelSummand×rhoDrop product; and
decrement-moment E[m]). BOTH show: E[m]'s O(1) sub-leading term carries
`−(C/(8n²√n))·M₃`, and since M₃ ~ 24λ²/t⁵ ~ 24n^{5/2}/λ³ this is O(1), feeding
μ̃'s 1/√n coefficient μA. So an upper bound on M₃ does NOT suffice — the SHARP
leading coefficient (24λ²/t⁵) is required. Hence `sigmaMoment_three_one_term`
:= |M₃ t − 24λ²/t⁵| ≤ K/t⁴ IS on the critical path.
Construction (mirror boseKernel3/sigmaMoment_two_lambert/reg3):
  boseKernel4 z := ∑_d d⁴ e^{−dz} = e^{−z}(1+11e^{−z}+11e^{−2z}+e^{−3z})/(1−e^{−z})⁵
    (Eulerian numbers ⟨4,k⟩=1,11,11,1), ~ 24/z⁵.
  sigmaMoment_three_lambert: M₃ = ∑'_k k³·boseKernel4(tk) (differentiate M₂ identity;
    boseKernel4 = −d/dz boseKernel3).
  reg4 z := boseKernel4 z − 24/z⁵; |reg4| ≤ const near 0 (sympy poly certificate,
    like MassRateReg3) + exp tail. Then M₃ one-term mirrors sigmaMoment_two_asymp_weak.
The reg4 near-zero polynomial certificate is the hard mechanical part → dispatch.

### STATUS 06-11 (Opus master + codex worker): μ̃ 5-block assembly
DONE (clean-3, pushed): #1 main_kernel_error_rhoModel_le (3c1c139), #2 model_sum_two_term_asymp
(1f1d184, μ̄=3/λ μA=3/(2λ²)), #3 main_model_rho_error_le (d9f5c4c). #4 weighted_far_erdos_tail_le
(WeightedTail.lean capstone) → dispatched to uisai2 codex (xhigh, tmux hr-codex), spec /tmp/hr_spec.md,
template = unweighted far_erdos_tail_le.

### #5 FINAL ASSEMBLY decomposition (muNum two-term ⟹ hhit) — route locked
Goal: `muNum_two_term : ∃K>0, ∀ᶠ n, |muNum n − (3/massLam + (3/(2·massLam²))/√n)| ≤ K/n`,
then `muTilde_expansion_of_muNum` (already committed division lemma) ⟹ μ̃ two-term ⟹
`two_term_local_lip` (brick 103) ⟹ `occupation_unbounded_loc` (101) ⟹ hhit.

muNum n = ∑_{m∈Icc 1 (n-1)} erdosWeight n m · rhoDrop n m. Set M = ⌊n^{2/3}⌋. Decompose
muNum − (μ̄+μA/√n) = [#2: ∑'_{all m} modelSummand·rhoDropModel − (μ̄+μA/√n)]  (≤K/n, DONE)
  + (muNum − ∑'_{all m} modelSummand·rhoDropModel), and the latter error splits as:
  (A) main-range model error (Icc 1 M): ∑(erdosWeight·rhoDrop − modelSummand·rhoDropModel)
      = #1 [(eW−mS)·rhoDropModel] + #3 [mS·(rhoDrop−rhoDropModel)] + (b) 2nd-order cross
        [(eW−mS)·(rhoDrop−rhoDropModel) ≤ |#1-bound|·|#3-bound|, even smaller, O(1/n^{3/2})].
  (B) muNum tail (Icc M+1 (n-1)): ∑ erdosWeight·rhoDrop ≤ (3/√n)·∑ erdosWeight·m
      [since rhoDrop = 3(√n−√(n−m)) = 3m/(√n+√(n−m)) ≤ 3m/√n] = (3/√n)·#4 ≤ O(1/n^{3/2}). Needs #4.
  (C) model tail (m>M): ∑_{m>M} modelSummand·rhoDropModel ≤ K/n  [(d) NEW: like #4 but model side,
      modelSummand·rhoDropModel ≤ σ·exp·(poly), tail via poly_mul_exp_neg_sixthRoot_le_inv].
REMAINING NEW sub-blocks for #5: (b) 2nd-order cross [small, ~80 lines], (c) muNum-tail-via-#4
[needs rhoDrop≤3m/√n lemma + #4, ~60 lines], (d) model-tail [~150 lines, mirror #4/#3 pattern],
(e) main assembly [tie #1+#2+#3+#4+b+c+d, ~120 lines]. (d) is independent of #4 → parallelizable
(2nd codex worktree or self). (b),(c),(e) wait on #4.

### STATUS 06-11 evening: ★μ̃ TWO-TERM COMPLETE★ + final gap precisely diagnosed
μ̃ 两项展开彻底完成 (5/5 blocks clean-3): #1 main_kernel_error(3c1c139) #2 model_sum_two_term(1f1d184)
#3 main_model_rho(d9f5c4c) #4 weighted_far_erdos_tail(ace602d,codex) #5 muNum_two_term+muTilde_two_term
(65328be,codex). muTilde n = 3/λ + (3/(2λ²))/√n + O(1/n). Full Ch8/Partitions = 0 sorry.

FINAL GAP (codex #6 honestly documented, 0 sorry, see HANDOFF/TASK6-gap.md): wiring muTilde_two_term → hhit
needs ONE new theorem `khat_residual_active_good_occupation_tends_infty`:
- Define stochastic conditioned residual kernel KhatRes = Kres/(1−cmass) (ITERCoupling only exports the
  SUBstochastic Kres, row sum 1−cmass; no KhatRes / normalized-Umat evolution lemma yet).
- Prove conditioned walk's GoodHi active-occupation unbounded from comparable high starts, = the g(t) the
  coalescence bridge needs (g t = ∑GoodHi·Umat / umass; u(t+1) ≤ u(t) − δ·u(t)·g(t) → umass_lt_of_occupation).
CORE OBSTRUCTION (doctrine's recurring hard-bone): occupation_unbounded_loc (101) needs GLOBAL hard
bounded-increment `K x z ≠ 0 → |D z − D x| ≤ b`, but the Erdős predecessor kernel has SOFT far tails (any
large rank-jump has small prob, not zero). Need: truncate to active GoodW window (hard b there) + show the
soft-tail mass is negligible over the active horizon M~r (weighted_far_erdos_tail_le gives the tail O(1/n)),
i.e. a LOCALIZED occupation that only uses the off-window martingale + window-truncated increments. The
v0/b moments come from the product Erdős kernel off-window; η~1/r² from muTilde via two_term_local_lip.
This is design-heavy (master to design the truncation + KhatRes instantiation, then codex to grind).

## RENEWAL ROUTE UPDATE (Opus + ChatGPT ac R2, 06-14) — fixed-window Tanaka-DEFECT local time
The b-vs-W tension (occupation needs large truncation scale b~r^{1/3} for soft-tail control, but
coalescence needs fixed small window W with δ bounded below) is REAL and confirmed:
RankDropGeoMinor records minorization rate d·e^{-Cd/3} — exponential in window width, so a growing
window kills coalescence (route (c) dead). Charging every >W jump as 2R additive Tanaka error
(my abs_drift_le_soft, SoftTailDrift.lean — banked, valid, but too lossy here: 4R²·farMass=O(1)·r²→∞
at fixed W) does NOT close it either.
CORRECT object (ChatGPT R2): fixed-window crossing / Tanaka-DEFECT local time with the tent/defect
  Φ_W(d) = max(|d| - W, 0).
Non-crossing large jumps are handled by the martingale drift (they don't push |D| up on average);
crossing jumps are NOT errors — they are coalescence opportunities. Recommended stack:
  1. tanakaDefect W D x z  (per-step defect of Φ_W).
  2. defect telescope: E[Φ_W(D_T)] - E[Φ_W(D_0)] - ηT ≤ ∑_t ∑_x μ_t(x) ∑_z K(x,z)·tanakaDefect.
  3. QV/PZ growth for Φ_W: since Φ_W(d) ≥ |d| - W, the banked E|D_T| ≥ c√T lower bound transfers
     with a -W loss ⟹ E[Φ_W(D_T)] large.
  4. coalescence bridge: κ_W · defectMass_t ≤ goodMass_t.
  5. ∑_t goodMass_t ≥ κ_W ∑_t defectMass_t → ∞ ⟹ umass→0 (via CoalesceBridge) ⟹ overlap→1 ⟹ hhit.
This keeps W FIXED for coalescence and counts crossings instead of discarding far mass. SoftTailDrift's
abs_drift_le_soft stays banked as general infra but is NOT the closing route; the defect local time is.
(ac2 KhatRes-bridge query failed to capture — re-dispatch when needed.)
NOTE 06-14: uisai2 remote Lean build server began refusing SSH mid-session (host up, sshd refusing —
likely MaxStartups throttle from concurrent ssh or load). Blocks all Lean verification until restored.

## ROUTE-A DEAD + route-B structure clarified (Opus + ChatGPT ac R3, 06-14)
Re-attacked the occupation→coalescence closure. Built route-independent transfer primitives
(OccupationTransfer.lean: distPow_L1_le — t-step laws within per-step L¹ ε differ by ≤t·ε;
occupation_transfer — window-occ transfers between kernels, discrepancy (∑t)·ε). Both clean-3.

DECISIVE FINDING (route A = truncate-K̂res-at-fixed-b + transfer is DEAD):
 - occupation_unbounded_loc/eta give occ of {|D|≤b} with b = the increment bound; to lower-bound the
   FIXED coalescence window {|D|≤W} need b ≤ W. That needs hbinc(b) for small b.
 - Truncating K̂res at fixed b≤W removes the per-step mass ρ = P(|ΔD|>b). For the Erdős kernel the
   rank-drop tail is P(drop>b) ~ e^{-cb} = CONSTANT in r (NOT ~1/r²). weighted_far_erdos_tail_le only
   bounds drop > n^{2/3} (mass ~1/n), i.e. a GROWING threshold, not fixed b.
 - So truncation drift-perturbation η_tr = η + 4Rρ/(1−ρ) ~ R·ρ ~ r·const, and 2R·η_tr ~ r²·const → ∞
   ≫ v0. Hence v0_tr − 2R·η_tr < 0: occupation_unbounded_loc's hv' FAILS. Route A cannot apply.
 - ChatGPT ac R3 confirmed: route A valid only if ρ ≲ 1/R²; here ρ~const, so DEAD.

TWO SEPARATE obstructions, correctly disentangled:
 (a) TANAKA/skip: window-occupation local time needs bounded increment (to cross {|D|≤W} you must
     LAND in it); soft far jumps SKIP the window → the local-time = occupation identity breaks. This is
     what the Φ_W DEFECT (R2) fixes: Φ_W(d)=max(|d|−W,0) counts crossings robustly to skips.
 (b) 4th moment / horizon: PZ needs E[D_T⁴] ≤ C(v0T)² (quadratic, → const horizon). The banked
     quadratic 4th moment (fourth_moment_le_quadratic) needs EXACT mart + bounded incr. The η-robust
     occupation uses the TRIVIAL R⁴ → horizon ~R⁶ (useless). BUT: the Erdős increment has a FINITE 4th
     moment (e^{-cs} drop tail ⟹ ∑_s e^{-cs}s⁴ = const), so E[D_T⁴] ≤ C(v0T)² + C'T holds via a
     FINITE-4th-MOMENT hypothesis (∑_z K x z (Dz−Dx)⁴ ≤ B₄ uniform) — NO truncation needed. The current
     bricks are stated with "bounded increment b"; the right generalization is "finite per-step 4th
     moment B₄" (+ for Tanaka, the Φ_W defect instead of the indicator window).

⇒ CORRECT PATH (route B, no truncation): Φ_W-defect Tanaka (skip-robust) + finite-4th-moment PZ
  (const horizon) + a new coalescence bridge from crossing-defect → one-step coalescence mass. Uses the
  REAL η~1/r² (small, so v0−2Rη = v0−2/r > 0 ✓ — no truncation catastrophe). Concrete moments needed:
  v0>0 (rank-diff local variance), η~1/r² (two_term_local_lip, banked), B₄ (per-step 4th moment, from
  the e^{-cs} tail). The v0 second-moment is the likely genuine new analytic input (ac2 R3 pending).

## MOMENT AUDIT (ChatGPT ac2 R3, 06-14) — v0 (local variance) is the lone genuine analytic input
Classification of the three concrete moment inputs route B needs for the rank-difference walk
D = 3√(rnk X) − 3√(rnk Y):
 (2) DRIFT η: ALREADY IMPLIED modulo wiring. η = |μ̃(X) − μ̃(Y)| via muTilde_eq_drift + muTilde_two_term
     + two_term_local_lip + KhatRes_eq_prod_of_not_GoodW (off-GoodW = product kernel). Scale η = O(ρ⁻²)
     (ρ = rank ~ r). Just assembly.
 (3) INCREMENT: soft only. Product tail P(|ΔD|>b) ≤ 2K/n by union bound from the single-chain tail
     (far_erdos_tail_le). But the exported occupation theorems demand HARD hbinc (|ΔD|≤b) — a soft tail
     does NOT instantiate it. ⟹ confirms route A dead AND that route B must use the FINITE-4th-MOMENT
     occupation variant (no hard increment), not the banked bounded-increment ones.
 (1) LOCAL VARIANCE v0 > 0: THE GENUINE MISSING CONCRETE INPUT. Need a positive lower bound on
       locVar (KhatResPair) D xy  for off-GoodW high-rank pairs.
     ChatGPT target: ρSqTilde(n) = ∑ erdosWeight·rhoDrop²/kernelMass → 27/(2λ²) (single-chain
       ρ-decrement 2nd moment); product variance ≈ 2(ρSqTilde − μ̃²) > 0. The repo has sigmaMoment 2,
       modelSummand, rhoDropModel, kernel-error machinery, but NO assembled 2nd-moment theorem. This is
       the concrete lemma to add — a parallel to the (huge) muNum/muTilde 1st-moment assembly.
     OPUS NOTE: for route B we only need v0 > 0 (a uniform POSITIVE LOWER BOUND), NOT the exact limit
       27/(2λ²). Likely far cheaper via a TWO-CLUMP argument: the jump m has ≥δ₁ mass on [a√n,1.5a√n]
       and ≥δ₂ mass on [2a√n,2.5a√n] (separated), so Δρ takes two separated values w.p. ≥δ ⟹
       Var(Δρ) ≥ δ·(gap)² > 0. Uses banked window-mass / σ(m)≥m bounds, avoids the full 2nd-moment
       Lambert assembly. THIS is the recommended next concrete build for v0.
 Also: TASK8-gap.md — no theorem yet instantiates KhatRes drift/QV/increment on the ACTIVE domain
   (global occupation hyps fail on killed/frozen boundary rows); the localized (off-window-only)
   occupation + active-horizon statement is still needed.

### Route B remaining build (pinned, gated on v0):
 1. v0 > 0 lower bound (two-clump argument) — the gating analytic input.
 2. Φ_W defect Tanaka telescope (TentDefect.lean base banked: tentW + props + expected_tentW_ge).
 3. finite-4th-moment occupation (η-approx-mart + finite per-step 4th → const horizon).
 4. crossing→coalescence bridge (κ_W·defectMass ≤ goodMass → CoalesceBridge).
 5. active-domain KhatRes instantiation (TASK8-gap).

## OCCUPATION CAPSTONE = greenT (ChatGPT ac R4, 06-15) — Tanaka occupation is the WRONG tool
Confirmed the κ_W one-pass self-consistency wall (off-window |D|-drift ≤ η + κ_W, κ_W=e^{−cW}·const
fixed; single-window single-pass gives occ ~ e^{cW}/W < 1/δ_W = e^{cW}, loses by log). FIX = multi-pass
expected window LOCAL TIME = greenT, NOT terminal Φ_W defect / occupation_unbounded_*.
 - RIGHT capstone (BANKED): ITERGreen.occupation_ge_green_tight (greenT ≥ any Poisson subsolution at
   start − tail) + ITERGreenT.greenT_subsolution (finite-horizon greenT IS a subsolution for free).
   occupation_unbounded_eta/_loc are WRONG (hard hbinc + terminal E|D_T| growth + κ_W wall).
 - The lone remaining analytic theorem: greenT_lower_fixed_window : c·√T ≤ ∑_{t<T} window-occupation,
   for the conditioned residual rank-diff walk. Inputs: {v0>0, η~1/r², finite 4th moment B4, |D|≤R}
   PLUS local accessibility = the banked drop-1/drop-2 minorization (RankDropMinor.lean:
   ∀x p ≤ ∑_z K x z·1[D z = D x±1]). Green algebra removes κ_W (changes the object) but the
   recurrence/local-time lower bound is the genuine wall.
 - Clean route: occupation_ge_green_tight + greenT_subsolution (banked) + greenT_le_T + NEW
   greenT_lower_fixed_window (explicit Poisson subsolution g on {−R..R}: K·g ≤ g − 1[|D|≤W], g(start)
   ≥ c√T, via drop-minor p + drift + range) → CoalesceBridge. T ~ active horizon ~ R², √T ~ R → ∞.

### v0 progress (this run, all clean-3): product_locVar_ge (VarianceLower) + Pker_subwindow_mass +
khatResPair_locVar_eq_of_not_GoodW (VarianceConcrete). Remaining for v0: ρ-decrement two-clump
separation (jump sub-windows [s,6s/5],[9s/5,2s], √x−√k ≈ m/(2√x), gap ≥ const via √(x−2s) ≥ √x/√2 for
x≥16). Then v0 = δ₁δ₂(hi−lo)² > 0 via product_locVar_ge + the bridge.
