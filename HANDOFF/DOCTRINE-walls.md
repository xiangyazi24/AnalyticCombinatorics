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
