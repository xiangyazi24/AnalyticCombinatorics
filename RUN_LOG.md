# RUN_LOG

## Run 2026-06-03 (automode, whole-book)
- doctrine: DOCTRINE.md (whole-book F&S, audit-passing)
- approval: standing /goal "完成全书形式化, 以通过 audit 为准" + /automode
- starting avenue: (a) Ch V — meromorphic coefficient transfer (F&S IV.10)
- pre-run reconcile: salvaged remote HAdmissible(645L)+design docs (84238ab,c092bda); git-based
  remote (uisai1 git checkout, .lake preserved, rsync retired); baseline green (8322 jobs, axioms clean);
  dedicated codex worker ac-codex up; C-group spot-audit Catalan/Fib/Transfer-VI.3/Bell/Surjections = FAITHFUL (AUDIT_STATUS.md, 42bff08); UNDERSTANDING corrected (0b820c6).
- avenue (a) progress:
  - meromorphic-transfer brick (codex): DONE — Ch5/Meromorphic/Transfer.lean, 7 theorems, FAITHFUL,
    all #print axioms clean, full build green (8323 jobs), committed 1d0f262.
  - surjections asymptotic brick (codex): DONE — Ch5/Meromorphic/Surjections.lean, 15 theorems,
    FAITHFUL (incl. hard transcendental remainder differentiable on closedBall 2 via dslope),
    surjectionsCount n/n! ~ 1/(2(log2)^(n+1)) (Fubini numbers), build green 8324 jobs, axioms clean,
    committed fa90671. Avenue (a) Ch V core delivered.
- avenue (b) Ch VII opened:
  - ternary trees / Fuss-Catalan brick (codex): DONE — Ch7/SingularityApp/TernaryTrees.lean, 20 thms,
    FAITHFUL, T_n=C(3n,n)/(2n+1) ~ (27/4)^n √3/(4√π n^{3/2}). codex rejected my wrong target constant,
    proved true Stirling value (有来有往). build green 8325, axioms clean, committed 126b7c6.
  - DISCOVERY: TransferGeneral.transfer_theorem covers ALL α (α≠-m), incl √-singularities (α=-1/2).
    Singularity-analysis framework is complete → Ch VI/VII tree results unlocked.
  - Motzkin brick: DONE (4 sub-bricks) — Ch7/SingularityApp/Motzkin.lean, UNCONDITIONAL FAITHFUL,
    M_n ~ (3√3/(2√π))·3^n·n^{-3/2}. v1 = vacuous impostor (caught by trust-but-verify) → v2 found
    the hsing contradiction → v3 corrected (centered architecture) + proved Δ-domain analyticity +
    denominator nonvanishing + singular expansion → v4 closed power-series bridge (quadratic branch
    uniqueness). build green 8326, axioms clean, committed 323a011.
  - Fuss-Catalan general p-ary brick (codex): DONE — Ch7/SingularityApp/FussCatalan.lean, FAITHFUL,
    fussCatalan p n ~ (√p/((p-1)^{3/2}√(2π)))·(p^p/(p-1)^{p-1})^n·n^{-3/2} for all p≥2; Catalan/ternary
    cross-checks + fussCatalan 3 = ternaryTreeCount proved in Lean. build green 8327, axioms clean,
    committed eca8d96.
- avenue (c) Ch IX opened:
  - quasi-powers / Gaussian limit law brick (codex): DONE — Ch9/LimitLaws/QuasiPowers.lean, opens Ch IX.
    Mathlib Levy continuity theorem PRESENT (tendsto_iff_tendsto_charFun) → quasi-powers Gaussian limit
    law (X_n−β_n u₁)/√(β_n u₂)→d N(0,1) proved, + mean/variance asymptotics. FAITHFUL framework
    (conditional on genuine quasi-powers hypothesis, satisfiable). build green 8328, axioms clean,
    committed c2a024b.
- Session FAITHFUL deliverables (6): Ch5 meromorphic transfer (IV.10), Ch5 surjections/Fubini,
  Ch7 ternary, Ch7 Motzkin (impostor caught+fixed), Ch7 Fuss-Catalan general, Ch9 quasi-powers limit law.
  Opened Ch V, Ch VII, Ch IX. Whole-tree Group-A/C audit clean. Caught+fixed 1 vacuous impostor.
  - quasi-powers fidelity fix + instance (codex): DONE — instance-attempt PROVED the committed hChar was
    over-strong (global exp identity unsatisfiable for lattice laws; charFun oneBitCountLaw π=0). Honestly
    downgraded (9dd62c4), then weakened hChar to LOCAL form (faithful Hwang) + proved unconditional
    binary-word CLT (#ones →d N(0,1)). build green 8329, axioms clean, committed 5a0f4b8. Ch IX now has a
    faithful framework + a non-vacuous instance.
  - permutation cycle-count CLT (codex, 2 sub-bricks): DONE — Ch9/LimitLaws/PermutationCycles.lean,
    UNCONDITIONAL FAITHFUL. (C_n−H_n)/√H_n →d N(0,1) (Goncharov), Feller-coupling realization; cycle_hChar
    (local quasi-powers) proved, scaled log-sum remainder closed. build green 8330, axioms clean,
    committed 2463a33. Ch IX now: faithful framework + 2 unconditional instances.
- Session FAITHFUL deliverables (8): Ch5 meromorphic transfer (IV.10), Ch5 surjections/Fubini, Ch7 ternary,
  Ch7 Motzkin (impostor caught+fixed), Ch7 Fuss-Catalan general, Ch9 quasi-powers limit law (over-strong
  hChar caught+fixed), Ch9 binary-word CLT, Ch9 permutation cycle CLT. Opened Ch V, VII, IX with
  framework + instance(s) each. Whole-tree Group-A/C audit clean. Trust-but-verify caught + fixed 2
  fidelity issues (Motzkin-v1 vacuous, quasi-powers hChar over-strong).
  - 2-regular graphs asymptotic (codex): DONE — Ch7/SingularityApp/TwoRegular.lean, g_n/n! ~
    e^{-3/4}/√(πn) via general transfer (α=1/2, entire prefactor). FAITHFUL as GF-coefficient asymptotic
    (count defined via EGF — weakest fidelity this run, honestly flagged). build green 8331, axioms clean,
    committed a339174.
- Session FAITHFUL deliverables (9): Ch5 meromorphic transfer, Ch5 surjections/Fubini, Ch7 ternary,
  Ch7 Motzkin, Ch7 Fuss-Catalan, Ch9 quasi-powers framework, Ch9 binary-word CLT, Ch9 cycle CLT,
  Ch7 2-regular (GF-coeff). Opened Ch V, VII, IX. Whole-tree audit clean. 2 fidelity issues caught+fixed.
- fidelity note: prefer genuine combinatorial definitions (surjections/ternary/Motzkin/Fuss-Catalan have
  them); 2-regular drifted to GF-coeff definition — future bricks should re-anchor to real counts.
  - CODEX OUTAGE (05:27 CDT): gpt-5.5 usage limit hit. Handled per automode hard-stop: (i) Opus-authored
    Fuss-Catalan p=4/5/6 instances (ab9a48a, build green 8332); (ii) updated UNDERSTANDING (56be2cb);
    (iii) bridge command auto-waited to 05:29 reset then re-dispatched composition-parts.
  - composition part-count CLT (codex, auto-bridged): DONE — Ch9/LimitLaws/CompositionParts.lean,
    HIGH-FIDELITY (card {c:Composition n//c.length=k}=C(n-1,k-1) proved via compositionAsSetEquiv —
    genuine combinatorial object, re-anchoring after 2-regular's GF-coeff drift). #parts →d N(0,1).
    committed 398ac98.
- Session FAITHFUL deliverables (11): meromorphic transfer, surjections, ternary, Motzkin, Fuss-Catalan
  general, quasi-powers framework, binary-word CLT, cycle CLT, 2-regular (GF-coeff), Fuss-Catalan
  p=4/5/6 instances (Opus), composition-parts CLT. Opened Ch V/VII/IX. Whole-tree audit clean.
  2 fidelity issues caught+fixed; codex outage bridged.
  - alignments (codex): DONE — Ch5/Meromorphic/Alignments.lean, HIGH-FIDELITY (genuine alignmentClass),
    o_n/n! ~ (1/(e-1))(e/(e-1))^n; codex corrected brief's wrong OEIS values. committed f235290, green 8334.
  - supercritical-seq schema (codex): DONE-with-fidelity-fix — codex dressed dominant_simplePole with
    UNUSED supercritical C-hypotheses (3rd fidelity catch this run). Removed decorative hyps; committed
    honest thin SEQ-form-constant transfer (d64a98c, green 8335). Genuine V.2 (derive decomposition from
    C(ρ)=1) flagged future work.
- Session FAITHFUL deliverables (13): meromorphic transfer, surjections, ternary, Motzkin, Fuss-Catalan
  general + p=4/5/6, quasi-powers framework, binary-word CLT, cycle CLT, 2-regular (GF-coeff),
  composition-parts CLT, alignments, supercrit transfer (thin). Opened Ch V/VII/IX. Whole-tree audit clean
  (build green 8335). 3 fidelity issues caught+fixed (Motzkin-v1 vacuous, quasi-powers hChar over-strong,
  supercrit decorative hyps); codex outage bridged.
  - 2-regular fidelity upgrade (codex): DONE — TwoRegularClass.lean, genuine SET-of-undirected-cycles
    count, EGF derived, counts=old GF-coeff count proved; asymptotic now for the genuine count. The one
    flagged fidelity gap is CLOSED. (My Audit #print-axioms namespace path was wrong → full build caught
    it, lake env lean had missed it — lesson: always run the integrated build, not just env lean.)
    committed 2c7796b/63b7695, green 8336.
- CAPSTONE (2026-06-04): 88 files, build green 8336 jobs, 0 sorry/admit/native_decide/custom-axiom;
  ~160 headline theorems #print-axioms-certified clean. Opened Ch V (meromorphic transfer + surjections +
  alignments + supercrit-transfer), Ch VII (ternary, Motzkin, Fuss-Catalan general+p=4/5/6, 2-regular
  genuine), Ch IX (quasi-powers framework + binary-word + cycle + composition-parts CLTs). 3 fidelity
  issues caught+fixed; 1 gap closed; codex outage bridged. ~38 commits.
  - genuine V.2 supercrit (codex): DONE — SupercriticalSeqGenuine.lean, decomposition DERIVED from
    C(ρ)=1 simple (dslope removable-singularity subtraction), no assumed decomposition. The thin-wrapper's
    flagged future-work is CLOSED. committed d5b0241, green 8337.
- CAPSTONE v2 (2026-06-04): 89 files, build green 8337, 0 sorry/admit/native_decide/custom-axiom; ~162
  headline theorems #print-axioms-certified. Opened Ch V/VII/IX. ALL flagged fidelity gaps closed
  (2-regular → genuine count; supercrit → genuine V.2). 3 fidelity issues caught+fixed; codex outage
  bridged. ~40 commits. Every fidelity concern raised this run has been resolved.
- next (genuinely multi-session): hard saddle/circle-method (Bell/involutions/Hardy-Ramanujan partitions);
  more Ch V/VII/IX breadth; multivariate (Ch IX); appendices A/B/C.
  - exp HAdmissible instance (codex): DONE — Ch8/SaddlePoint/ExpHAdmissible.lean, FULL instance
    expHAdmissible : HAdmissible Complex.exp (local_uniform + tail_uniform proved), exp asymptotic derived
    THROUGH the general Hayman coeff_isEquivalent_saddle → interface now NON-VACUOUS. Closes the original
    session-start CONDITIONAL gap (task #3). instance axioms clean. committed 9b7d2bd, green 8338.
- CAPSTONE v3 — EVERY flagged fidelity concern this run is now CLOSED:
  (1) Motzkin v1 vacuous impostor → rebuilt unconditional;
  (2) quasi-powers hChar over-strong → weakened to faithful local form + binary-word instance;
  (3) supercrit decorative hyps → removed, then genuine F&S V.2 derived (decomposition from C(ρ)=1);
  (4) 2-regular GF-coeff → upgraded to genuine SET-of-cycles combinatorial count;
  (5) original Ch8 HAdmissible no-instance → exp instance constructed, general interface non-vacuous.
  State: 91 files, build green 8338, 0 sorry/admit/native_decide/custom-axiom, ~164 headline theorems
  #print-axioms-certified. Opened Ch V/VII/IX. ~41 commits.
- next (genuinely multi-session): hard saddle/circle-method (Bell/involutions/Hardy-Ramanujan partitions);
  Ch V/VII/IX breadth; multivariate; appendices A/B/C.
- end: <comprehensive capstone; all flagged gaps closed; campaign continues per doctrine across sessions>
- final result: <ongoing — book is multi-session; this run delivered 16 faithful results + opened 3 chapters>


## Run continued — hard saddle phase
- Bell HAdmissible (codex): DONE — BellHAdmissible.lean (849L), full instance for e^{e^z-1} (Hayman
  flagship), saddle r·e^r=n genuine, all fields incl local/tail uniform proved, B_n/n! ~ saddleScale via
  the general interface, tied to posInt.set.counts. Deep-audited genuine. green 8339, axioms clean,
  committed 4235801. (17th deliverable; 92 files.)
- next: involutions (e^{z+z²/2}, another Hayman instance); then Hardy-Ramanujan partitions (circle method,
  hard); breadth; appendices.
- involutions HAdmissible (codex): DONE — InvolutionHAdmissible.lean (912L), 3rd Hayman instance
  (e^{z+z²/2}), genuine count parts12.set (verified parts12=(0,1,1,0,…) atom class). green 8340, clean,
  committed d62b396. (18th deliverable; 93 files, 21,171 L total.)
- set-partition block-count CLT (codex): NOT BANKED — codex honestly reduced it to a single
  `def BellBlockSaddleCoefficientAsymptoticsObligation : Prop` that CONTAINS the substance (mean ~ n/log n,
  variance ~ n/(log n)², AND the bivariate-Bell charFun quasi-powers expansion). The Gaussian conclusion
  follows trivially from that obligation, so this is the "hard part bundled into a hypothesis" / def:Prop
  pattern — NOT a faithful result. Per audit discipline, NOT wired into the tree, NOT counted as a
  deliverable. The obligation = genuine hard multi-session sub-goal (parameter-uniform bivariate Bell
  saddle, beyond the univariate BellHAdmissible). Flagged future work. (SetPartitionBlocks.lean left on
  uisai1 as scaffolding, unwired.)
- audit lesson reaffirmed: a CLT "conditional on" an obligation that contains the mean/variance/expansion
  is not progress — refuse to bank it (substrate: 不容忍把数学负担塞进假设).
- Schröder (codex): DONE — Schroeder.lean (852L), genuine recurrence (verified vs A006318 incl S_10),
  S_n ~ C·(3+2√2)^n·n^{-3/2}, OGF zS²+(z-1)S+1=0. green 8341, clean. committed 820e226. (19th deliverable.)
- coverage note: tractable frontiers largely covered (3 chapters, frameworks+instances, 3 saddle instances,
  algebraic/explicit/meromorphic-SEQ/limit-law families). Remaining is the HARD frontier: Hardy-Ramanujan
  circle method (partitions), bivariate saddles (set-partition blocks — flagged), multivariate, appendices.
- Riordan (codex): DONE — Riordan.lean (751L), genuine first-return def R=1+z²MR (vs A005043 incl R_10=603),
  R_n ~ (3√3/(8√π))·3^n·n^{-3/2}. green 8342, clean. committed 915e95b. (20th deliverable.)
- PIVOT: algebraic √-family (Motzkin/Schröder/Riordan) well-covered; turning to NEW territory —
  two-dominant-pole meromorphic transfer (tangent numbers, tan z poles ±π/2), then conjugate/higher-order
  poles, log-singularity transfer, appendices.
- tangent numbers (codex, 2 sub-bricks): DONE — Tangent.lean (789L), UNCONDITIONAL. First two-dominant-pole
  meromorphic transfer (tan poles ±π/2, residue −1); remainder analytic to closedBall 3 proved → T_n/n! ~
  2(2/π)^{n+1} (odd n). green 8343, clean. committed c620359. (21st deliverable; new two-pole machinery.)
- secant/Euler numbers (codex): DONE — Secant.lean (609L), UNCONDITIONAL, reused tangent two-pole
  machinery; E_{2n}/(2n)! ~ 2(2/π)^{2k+1}, numeric → 0.99995. green 8344, clean. committed 1296edb. (22nd.)
- coverage: Ch V (single+two-pole meromorphic + 4 apps + supercrit V.2), Ch VII (6 algebraic/singularity),
  Ch IX (framework + 3 CLT), Ch VIII (3 Hayman saddle instances). Reusable machinery built. All fidelity
  gaps closed. Next genuinely-new: log-singularity transfer (VI.2), then circle method / appendices / multivariate.
- log-singularity coeff scale (codex): DONE — LogSingularity.lean (183L), leading-order β=1
  [z^n](1-z)^{-α}log(1/(1-z)) ~ (n^{α-1}/Γα)log n (α>1), α=2 ~ n log n. Full analytic log-transfer +
  general β honestly reported-open. green 8345, clean. committed 721fa0c (+b13b48e import fix). (23rd.)
  (process note: forgot Audit import — full build caught the unknown-constant; env-lean had missed it.)
- blocks≤3 saddle (codex): DONE — Blocks3HAdmissible.lean (1067L), 4th Hayman instance e^{z+z²/2+z³/6},
  genuine count parts123.set (set partitions blocks ≤3). green 8346, clean. committed 4a8d953. (24th.)
- PIVOT to implicit-function schema (F&S VII.4): tree function T=ze^{T}, √-singularity at 1/e.
- tree function / Cayley (codex): DONE — TreeFunction.lean (namespaced TreeFunctionNS to avoid helper
  collision with FussCatalan), n^{n-1}/n! ~ e^n/(√(2π)n^{3/2}); codex corrected my exponent (3/2 not 5/2).
  green 8347, clean. committed 8f9101e (+145a36f namespace fix). (25th deliverable.)
- build-integration lessons this run: (a) forgot Audit import (logsing); (b) helper-name collision
  (treefun vs fusscatalan). Both caught by the FULL build (not env-lean) → namespace agent files +
  always full-build before banking.
- rooted forests (codex): DONE — Forests.lean (namespaced ForestsNS), rootedForest n=(n+1)^{n-1}
  (Cayley-Prüfer), shift identity to tree function; (n+1)^{n-1}/n! ~ e^{n+1}/(√(2π)n^{3/2}). green 8348,
  clean. committed a53289f. (26th.)
- PIVOT to a genuinely-different limit law: fixed points of a random permutation → Poisson(1) (discrete
  limit, not Gaussian; method of factorial moments). Opens the discrete-limit-law side of Ch IX.
- fixed points → Poisson(1) (codex): DONE (pmf-level) — FixedPointsPoisson.lean (namespaced), FIRST
  discrete limit law: exact factorial moments E[(F_n)_k]=1, pmf → poissonPMFReal 1 j (via derangements).
  Full weak-convergence reported-open (Mathlib lacks pmf⟹weak bridge for ℕ). green 8349, clean. 36f7a74. (27th.)
- LIMIT-LAW LANDSCAPE now covers BOTH Gaussian (binary-word/cycle/composition-parts) AND Poisson
  (fixed points) — the two canonical F&S Ch IX universal laws.
- pmf⟹weak bridge + full Poisson (codex): DONE — PMFToDistribution.lean (namespaced), reusable
  probabilityMeasure_nat_tendsto_of_tendsto_singleton (portmanteau), fixed-points → FULL
  TendstoInDistribution Poisson(1). Filled the Mathlib gap. green 8350, clean. committed 4c59db5. (28th.)
- This unlocks more discrete limit laws (the bridge is reusable). Ch IX now: Gaussian (3 instances) +
  Poisson (fixed points, full weak convergence) + reusable Gaussian (quasi-powers) & discrete (pmf) bridges.
- r-cycles → Poisson(1/r) (codex): RCyclesPoisson.lean (namespaced RCyclesPoissonNS).
  BANKED unconditional: rCyclePMFFormula_tendsto_poisson — analytic limit of the Goncharov
  inclusion-exclusion truncated-exp pmf formula (r^j j!)⁻¹·expPartial(-1/r,⌊n/r⌋-j+1) → e^{-1/r}(1/r)^j/j!
  (moving truncation ⌊n/r⌋→∞ is the crux). Genuine RV rCycleCount (cycleType.count r / fixedPointCount),
  genuine count restatement rCycleCount_eq_card_cycleFactorsFinset_filter, laws + bridge wired.
  CONDITIONAL (NOT banked as headline): full →d Poisson(1/r) general r, reduced via reusable pmf⟹weak
  bridge to the marginal cycle-count identity rCyclePMF=rCyclePMFFormula — genuine Mathlib gap (no
  marginal cycleType.count r=j enumeration / Goncharov exact count). r=1 = re-wrap of fixed-points (not banked).
  Honest conditional status; combinatorial enumeration is multi-session future work. (29th deliverable.)
- Fibonacci OGF asymptotic (codex): FibonacciCompositions.lean (namespaced FibonacciCompositionsNS).
  BANKED unconditional: natFib_succ_isEquivalent_phi — Nat.fib(n+1) ~ φ^{n+1}/√5, the textbook first
  rational-coefficient asymptotic (F&S Ch V). Genuine: partial-fraction split of 1/(1-z-z²) into poles
  ρ=1/φ (dominant) + 1/(-φ) (remainder radius>1 via FMLS estimate), coeff=Nat.fib(n+1) from recurrence
  (fibonacciSeries_mul_denominator), residue -1/√5, fed to banked dominant_simplePole_isEquivalent.
  13 theorems, 0 blocked. NOTE: fibonacciCompositionCount:=Nat.fib(n+1) by def; {1,2}-composition
  bijection NOT proved — banked the clean Nat.fib statement, not the "composition" framing. (30th deliverable.)
- Derangements D_n/n!→1/e (codex): REJECTED — NOT banked. Mathlib ALREADY proves this
  (Mathlib/Combinatorics/Derangements/Exponential.lean:27 numDerangements_tendsto_inv_e). codex's
  derangementRatio_tendsto is a restatement of that existing theorem; numDerangements_isEquivalent
  (D_n~n!/e) is cosmetic repackaging into IsEquivalent (D_n/(n!/e)=e·(D_n/n!)→1). Per playbook
  "never bank re-wrappers / zero-new-math". File left unwired/uncommitted. LESSON: grep Mathlib for the
  target theorem BEFORE dispatching a textbook limit — derangements→1/e was already there.
- r-cycle FACTORIAL-MOMENT identity (codex, hard): RCyclesFactorialMoment.lean (654L, namespace
  RCyclesPoissonNS, nested FM). BANKED unconditional, fills the documented Mathlib gap:
  * FM.cycleType_count_factorialMoment_sum_in: r^k·Σ_σ (σ.cycleType.count r)_k = (card α)! — the Goncharov
    identity, proved FROM FIRST PRINCIPLES via genuine Equiv bijections (delete a distinguished r-cycle ↔
    permute the complement) + induction over the complement. NOT a Mathlib re-wrapper (~650L combinatorics).
  * factorialMoment_rCycle: E[(C_{n,r})_k] = r^{-k} (general k, r·k≤n) over the genuine uniform perm average.
  * rCycle_mean_eq_inv: classic mean E[C_{n,r}] = 1/r.
  This is the genuine combinatorial HEART the conditional r-cycles→Poisson(1/r) was missing. Full
  distribution-level Poisson(1/r) still needs a factorial-moment⟹law bridge (separate Mathlib gap).
  0 blocked. (31st deliverable — strongest since the pmf⟹weak bridge.)
- r-cycles → Poisson(1/r) COMPLETED UNCONDITIONAL (codex, INV): RCyclesPoissonComplete.lean (349L,
  namespace RCyclesPoissonNS.Complete). 17 theorems, 0 blocked. FLAGSHIP — the number of length-r cycles
  in a uniform random permutation →d Poisson(1/r), end-to-end unconditional. Chain:
  * rCycleCount ≤ ⌊n/r⌋ (boundedness: Multiset.count_mul_le_sum + cycleType.sum=card),
  * finite_pmf_eq_factorial_moment_sum — GENERAL method-of-factorial-moments pmf inversion for bounded
    ℕ-valued r.v. on a finite space, via alternating-binomial kernel factorial_kernel_sum_eq_indicator
    (reusable Mathlib-gap filler),
  * substitute EXACT moments r^{-k} (factorialMoment_rCycle) ⟹ rCyclePMF = rCyclePMFFormula (exact Goncharov pmf),
  * discharge hformula ⟹ rCycles_tendstoInDistribution_poisson (full weak conv to Poisson(1/r)).
  Genuine, no Mathlib re-wrapper. r-cycles avenue driven to terminal: CONDITIONAL→UNCONDITIONAL. (32nd deliverable.)
- JOINT cycle factorial moments (codex, JFM): JointCycleMoments.lean (636L, namespace JointCycleMomentsNS).
  BANKED unconditional (two distinct lengths): factorialMoment_two_rCycle_of_pos — E[(C_{n,r})_a (C_{n,s})_b]
  = r^{-a}·s^{-b} for distinct positive r,s with r·a+s·b≤n (incl. fixed-point branch r or s =1), proved by
  extending the FM deletion bijection with cross-length cycle DISJOINTNESS (Equiv.Perm.Disjoint). Covariance
  corollary rCycleCount_mul_mean_eq_inv_mul_inv: E[C_{n,r}C_{n,s}]=1/(rs) (counts of two different lengths
  uncorrelated). Foundation of Goncharov–Kolchin (asymptotic independence of cycle-length counts).
  BLOCKED/documented: general >2-length family (indexed-family deletion induction is the remaining work).
  Genuine, no Mathlib re-wrapper. (33rd deliverable.)
