# AUDIT_STATUS — fidelity audit

## Group A (mechanical, whole tree) — 2026-06-03

Across all 77 `.lean` files: **0 sorry, 0 admit, 0 native_decide, 0 custom axiom**
(the lone `native_decide` grep hit is the prohibition text in `Audit.lean`'s docstring, not a tactic).
Full library build green (8324 jobs). Every headline `#print axioms` in `Audit.lean` =
{propext, Classical.choice, Quot.sound}. The tree passes Group A unconditionally.

## Group C (semantic fidelity) spot-checks

Tracking statement-fidelity verdicts for headline theorems, per formalization-playbook
Phase 3 (Group C semantic review). The old tree (archive/impostor-2026-05) was a whole-repo
IMPOSTOR; every "FAITHFUL" claim in the rebuilt tree must be spot-checked against F&S.

Verdict legend: FAITHFUL / CONDITIONAL-honest / FRAGMENT / IMPOSTOR.

## Checked 2026-06-03

| Theorem | F&S | Statement (abridged) | Verdict |
|---------|-----|----------------------|---------|
| `catalan_isEquivalent_complex_sqrt_mul_nat` | — | `catalan n ~ 4^n/(√(πn)·n)` = 4^n/(√π·n^{3/2}) | FAITHFUL |
| `catalan_isEquivalent_real_rpow` | — | `catalan n ~ 4^n/(√π·n^{3/2})` | FAITHFUL |
| `fib_isEquivalent_real` | — | `fib(n+1) ~ (φ/(φ-ψ))·φ^n` = (φ/√5)·φ^n | FAITHFUL |
| `transfer_theorem_re_alpha_gt_one` | VI.3 | Δ-domain analytic + singular expansion `f ~ C(1-z)^{-α}` ⟹ `[z^n]f ~ C·n^{α-1}/Γ(α)` (Re α>1) | FAITHFUL — genuine analytic hypotheses, proof subtracts principal part + bounds remainder o(n^{α.re-1}) |
| `CombClass.egf_bell` | II | `posInt.set.egf = exp(exp-1)` (Bell EGF e^{e^z-1}) | FAITHFUL |
| `CombClass.egf_surjections` | II.3 | `lseq.egf·(2-e^z) = 1` (surjection EGF 1/(2-e^z)) | FAITHFUL |
| `exp_coeff_isEquivalent_saddle` | VIII | exp coeff ~ saddleScale (= e^n/(n^n√(2πn))) | FAITHFUL, unconditional |
| `coeff_isEquivalent_saddle` (HAdmissible) | VIII.4 | given `HAdmissible f p`, `p.coeff n ~ saddleScale` | CONDITIONAL-honest — general transfer, no concrete instance yet |

### Checked 2026-06-03 (symbolic method + moments)

| Theorem | F&S | Statement (abridged) | Verdict |
|---------|-----|----------------------|---------|
| `CombClass.ogf_prod` | I.1 | `(C×D).ogf = C.ogf·D.ogf` | FAITHFUL |
| `CombClass.ogf_sum` | I.1 | `(C+D).ogf = C.ogf+D.ogf` | FAITHFUL |
| `CombClass.ogf_seq_mul` | I.2 | `C.seq.ogf·(1-C.ogf)=1` (quasi-inverse SEQ) | FAITHFUL |
| `CombClass.ogf_mset` | I.2 | `MSET(C).ogf = ∏_i ∑_k multichoose(c_i,k)X^{ik}` | FAITHFUL |
| `CombClass.ogf_partitions` | I.3 | `∏_i ∑_j X^{(i+1)j}` (= ∏ 1/(1-X^{i+1}), Euler) | FAITHFUL |
| `CombClass.ogf_pset` | I.2 | `PSET(C).ogf = ∏_i ∑_k choose(c_i,k)X^{ik}` | FAITHFUL |
| `ParamClass.mean_eq` | III | `mean = (Σ param)/count` | FAITHFUL |
| `ParamClass.variance_eq` | III | `variance = (Σ param²)/count − mean²` | FAITHFUL |

### Checked 2026-06-03 (Ch2 EGF core)

| Theorem | F&S | Statement (abridged) | Verdict |
|---------|-----|----------------------|---------|
| `CombClass.egf_lprod` | II.1 | `(A⋆B).egf = A.egf·B.egf` (labelled product) | FAITHFUL |
| `CombClass.egf_set` | II.2 | `SET(C).egf = exp(C.egf)` (C.counts 0 = 0) | FAITHFUL |
| `CombClass.egf_lseq` | II.2 | `SEQ(C).egf·(1-C.egf)=1` | FAITHFUL |
| `CombClass.egf_lcyc_ode` | II.2 | `d/dX CYC(C).egf = C.egf'·SEQ(C).egf` (CYC = log 1/(1-C)) | FAITHFUL |

Conclusion so far: spot-checks across ALL existing chapters (Ch1 OGF, Ch2 EGF, Ch3 BGF,
Ch4 complex+singularity, Ch8 saddle) — every core transfer rule and payoff theorem is a genuine,
correctly-constanted statement. The rebuilt tree is honest, unlike the old whole-repo impostor.
Continue spot-checks chapter by chapter as coverage grows.

### New work 2026-06-03 (Ch5 meromorphic transfer, codex brick, audited)

| Theorem | F&S | Statement (abridged) | Verdict |
|---------|-----|----------------------|---------|
| `Ch5.Meromorphic.coeff_norm_isBigO_of_hasFPowerSeriesAt_differentiableOn` | IV.10 | g analytic on closedBall R ⟹ `‖coeff n‖ =O(R^{-n})` (Cauchy estimate) | FAITHFUL — real proof via `norm_coeff_le_of_circleIntegral` |
| `Ch5.Meromorphic.coeff_sub_principalPart_isBigO_of_remainder_radius` | IV.10 | `f=S+g`, g analytic past R ⟹ `coeff f − coeff S =O(R^{-n})` | FAITHFUL |
| `Ch5.Meromorphic.meromorphic_coeff_transfer_simplePoleSum` | IV.10 | finite simple-pole sum + remainder ⟹ `coeff f − Σ cᵢaᵢⁿ =O(R^{-n})` | FAITHFUL |
| `Ch5.Meromorphic.single_simplePole_principal_isEquivalent` | — | `coeff` of `c/(ρ−X)` `~ c·ρ^{-(n+1)}` | FAITHFUL |
| `Ch5.Meromorphic.dominant_simplePole_isEquivalent` | IV.10 | simple pole at ρ + remainder analytic past R>‖ρ‖ ⟹ `coeff f ~ c·ρ^{-(n+1)}` | FAITHFUL — genuine remainder-radius hypothesis, not buried |

All 5 `#print axioms` = {propext, Classical.choice, Quot.sound}; full build green (8323 jobs).

### Checked 2026-06-03 (Pringsheim — singularity-location foundation)

| Theorem | F&S | Statement (abridged) | Verdict |
|---------|-----|----------------------|---------|
| `pringsheim_not_analyticAt` | IV.6 | nonneg-coeff series of radius R ⟹ sum not analytic at z=R | FAITHFUL |
| `pringsheim_not_analyticContinuation` | IV.6 | nonneg-coeff series ⟹ no analytic continuation across z=R | FAITHFUL |

Audit coverage now spans every foundational layer (symbolic transfer Ch1/2/3, complex core
Pringsheim/Transfer-VI.3/Cauchy-coeff, asymptotic payoffs Catalan/Fib/CentralBinom, saddle exp,
Ch5 meromorphic) — all FAITHFUL. The rebuilt tree passes C-group audit for its current content.

### New work 2026-06-03 (Ch5 surjections — Fubini numbers, F&S Ch V)

| Theorem | F&S | Statement (abridged) | Verdict |
|---------|-----|----------------------|---------|
| `Surjections.surjectionsCount_div_factorial_isEquivalent` | V | `r_n/n! ~ 1/(2(log2)^{n+1})`, r_n = posInt.lseq.counts (Fubini/ordered-Bell) | FAITHFUL — correct constant |
| `Surjections.remainder_radius_gt_one` | V | toFMLS radius of (surjEGF − principal) > 1 | FAITHFUL — genuine |
| `Surjections.analyticRemainderFun_differentiableOn_closedBall_two` | V | meromorphic remainder of 1/(2−e^z) analytic on closedBall 2 | FAITHFUL — dslope removable-singularity continuation, math cross-checked: remainder = (1/2)(e^w−1−w)/(w(e^w−1)), w=z−log2; next poles log2±2πi modulus ≈6.3>2 |

The hard transcendental step (remainder radius) is genuinely proved, not buried. All headline
`#print axioms` clean; full build green (8324 jobs).

### New work 2026-06-04 (Ch7 ternary trees — Fuss-Catalan, F&S Ch VII)

| Theorem | F&S | Statement (abridged) | Verdict |
|---------|-----|----------------------|---------|
| `ternary_choose_dvd` | — | `2n+1 ∣ C(3n,n)` (Fuss-Catalan integrality) | FAITHFUL — choose recurrence + coprimality |
| `choose_three_mul_isEquivalent` | VII | `C(3n,n) ~ (27/4)^n √3/(2√(πn))` | FAITHFUL (Stirling) |
| `ternaryTreeCount_isEquivalent` | VII | `C(3n,n)/(2n+1) ~ (27/4)^n √3/(4√π · n^{3/2})` | FAITHFUL |

Note: codex correctly REJECTED the (wrong, self-inconsistent) target constant in the dispatch brief
and proved the true Stirling value √3/(4√π) — verified by hand. Healthy "有来有往" (not 传声筒).
All `#print axioms` = {propext, Classical.choice, Quot.sound}; full build green (8325 jobs).

### New work 2026-06-04 (Ch7 Motzkin — algebraic √-singularity, F&S Ch VII) — UNCONDITIONAL

| Theorem | F&S | Statement (abridged) | Verdict |
|---------|-----|----------------------|---------|
| `motzkin_isEquivalent` | VII | `M_n ~ (3√3/(2√π))·3^n·n^{-3/2}`, M = genuine Motzkin recurrence | FAITHFUL, UNCONDITIONAL |
| `motzkinRescaledDenominator_ne_zero` | — | denominator of rescaled OGF ≠ 0 on Δ-domain (the crux) | FAITHFUL |
| `motzkinCenteredRescaledFun_hasFPowerSeriesAt_zero` | — | explicit fn's Taylor series = formal Motzkin (centered) series | FAITHFUL — via quadratic branch uniqueness |

IMPOSTOR CAUGHT + FIXED: the first Motzkin attempt produced a conditional theorem whose hypotheses
(`hp`: series = motzkinRescaledSeriesℂ ⟹ f(1)=3; `hsing`: f ~ C(1-z)^{1/2} ⟹ f(1)=0) were JOINTLY
UNSATISFIABLE → vacuously true → unusable. Trust-but-verify caught it; rebuilt with the centered
architecture (subtract regular part f(1)=3 before transfer). Constant cross-checked numerically
(M_n/(K·3^n·n^{-3/2}) → 1, 0.80 at n=10). All `#print axioms` clean; full build green (8326 jobs).

### New work 2026-06-04 (Ch7 general Fuss-Catalan / p-ary trees, F&S Ch VII)

| Theorem | F&S | Statement (abridged) | Verdict |
|---------|-----|----------------------|---------|
| `fussCatalan_isEquivalent (p≥2)` | VII | `C(pn,n)/((p-1)n+1) ~ (√p/((p-1)^{3/2}√(2π)))·(p^p/(p-1)^{p-1})^n·n^{-3/2}` | FAITHFUL |
| `fussCatalan_choose_dvd (p≥2)` | — | `(p-1)n+1 ∣ C(pn,n)` (Fuss-Catalan integrality) | FAITHFUL |
| `fussCatalan_three_eq_ternaryTreeCount` | — | `fussCatalan 3 n = ternaryTreeCount n` (consistency) | FAITHFUL |

Subsumes Catalan (p=2: base 4, const 1/√π) and ternary (p=3: 27/4, √3/(4√π)) — both cross-checks
PROVED in Lean, not asserted. All `#print axioms` clean; full build green (8327 jobs).

### New work 2026-06-04 (Ch9 quasi-powers / Gaussian limit law, F&S/Hwang IX.8) — opens Ch IX

| Theorem | F&S | Statement (abridged) | Verdict |
|---------|-----|----------------------|---------|
| `quasiPowers_tendstoInDistribution_of_continuousAt` | IX.8 | LOCAL quasi-powers charFun form (∃s₀>0,∀|s|≤s₀) + β→∞ + scaled-remainder→0 ⟹ `(X_n−β_n u₁)/√(β_n u₂) →d N(0,1)` | FAITHFUL (local hChar = Hwang's hypothesis; now instantiable) |
| `binaryWord_symbolCount_tendstoInDistribution_gaussian` | IX | #ones in uniform binary word: `(X_n−n/2)/√(n/4) →d N(0,1)` | FAITHFUL, UNCONDITIONAL — instantiates the framework (sign sum, u₁=0,u₂=1,s₀=1/2) |
| `permutationCycles_tendstoInDistribution_gaussian` | IX (Goncharov) | #cycles of random permutation: `(C_n−H_n)/√H_n →d N(0,1)` | FAITHFUL, UNCONDITIONAL — Feller-coupling realization (Σ indep Bernoulli(1/k)); cycle_hChar (local quasi-powers, u₁=u₂=1) proved, remainder closed. Non-iid instance. Note: distribution-faithful realization, not a literal permutation count |
| `twoRegularGraphCount_div_factorial_isEquivalent` | VI/VII | 2-regular graphs: `g_n/n! ~ (e^{-3/4}/√π)·n^{-1/2}` (EGF exp(-z/2-z²/4)/√(1-z), α=1/2) | FAITHFUL **as GF-coefficient asymptotic** — clean (entire prefactor); constant numerically checked vs OEIS A001205. ⚠ WEAKEST fidelity this run: `twoRegularGraphCount := n!·[z^n](EGF)`, so the combinatorial identity (EGF counts 2-regular graphs) is the standard *input*, not proved in Lean. Contrast surjections/ternary/Motzkin/Fuss-Catalan/cycles which have genuine combinatorial definitions. |
| `expectation_sub_quasiPowerCoeff_isBigO` | IX | `E[X_n] = β_n u₁ + O(1)` from cgf | FAITHFUL |
| `variance_sub_quasiPowerCoeff_isBigO` | IX | `Var[X_n] = β_n u₂ + O(1)` from cgf | FAITHFUL |

Proved via Mathlib's Levy continuity theorem (`ProbabilityMeasure.tendsto_iff_tendsto_charFun`) +
`charFun_gaussianReal` — genuinely used, not faked. The quasi-powers hypothesis (charFun exponential
form + scaled remainder→0) is the genuine Hwang input — SATISFIABLE (unlike the Motzkin-v1 vacuous
contradiction), not the conclusion smuggled in. Concrete instance is the natural follow-up.
All `#print axioms` clean; full build green (8328 jobs). Mathlib survey logged: Levy continuity +
gaussianReal + charFun present; Curtiss MGF-continuity absent.

⚠ FIDELITY ISSUE (caught 2026-06-04 by the instance-attempt; fix in progress): the committed
`quasiPowers_…` hypothesis `hChar` requires a GLOBAL identity `charFun = Complex.exp(…)`. But
`Complex.exp _ ≠ 0` everywhere, while genuine lattice laws have vanishing charFun
(PROVED: `charFun oneBitCountLaw Real.pi = 0`, and `oneBitCountLaw_no_quasiPowers_hChar : hChar → False`).
So the committed theorem is STRONGER than Hwang's actual (LOCAL, s near 0) quasi-powers condition and is
NOT instantiable by binomial/binary-word counts — the canonical Ch IX examples. It is a true theorem but
an over-narrow / non-faithful IX.8. FIX: weaken `hChar` to a local-neighborhood form (the standard Hwang
hypothesis), then instantiate the binary-word CLT. Until fixed, this result is NOT counted as FAITHFUL.
This is exactly the over-strong-hypothesis failure mode the audit exists to catch — same family as the
Motzkin-v1 vacuous impostor.

RESOLVED 2026-06-04 (commit 5a0f4b8): `hChar` weakened to the LOCAL form
`∃ s₀>0, ∀ n s, |s|≤s₀ → charFun = exp(quasi-powers)` — exactly Hwang's local quasi-powers hypothesis.
The framework theorems were re-proved (the proof only evaluates charFun at scaled args → 0, which
eventually lie in `|s|≤s₀`). The binary-word CLT then instantiates it unconditionally, confirming the
fixed framework is faithful AND non-vacuous. Full build green (8329 jobs); both `#print axioms` clean.

### Opus-authored 2026-06-04 (during codex usage-limit outage)

| Theorem | F&S | Statement | Verdict |
|---------|-----|-----------|---------|
| `fussCatalan_four_isEquivalent` | VII | quaternary trees `~ C₄·(256/27)^n·n^{-3/2}` | FAITHFUL — specialization of the general theorem |
| `fussCatalan_five_isEquivalent` | VII | quinary trees `~ C₅·(3125/256)^n·n^{-3/2}` | FAITHFUL — specialization |
| `fussCatalan_six_isEquivalent` | VII | senary trees `~ C₆·(6^6/5^5)^n·n^{-3/2}` | FAITHFUL — specialization |

Authored directly with Opus (codex gpt-5.5 out of credits until ~5:27 AM); lake env lean + full build
green (8332 jobs), axioms clean. Low marginal value (instances of the general p-ary theorem) but genuine
faithful results, keeping progress through the external block.

### New work 2026-06-04 (Ch9 composition part-count CLT — HIGH FIDELITY)

| Theorem | F&S | Statement | Verdict |
|---------|-----|-----------|---------|
| `card_compositionsWithParts_eq_choose` | III/IX | `card {c : Composition n // c.length = k} = C(n-1,k-1)` | FAITHFUL — genuine combinatorial count via Mathlib compositionAsSetEquiv (NOT assumed) |
| `compositionParts_tendstoInDistribution_gaussian` | IX | #parts of uniform composition: `(parts−(n+1)/2)/√((n-1)/4) →d N(0,1)` | FAITHFUL — re-anchored to genuine object (corrects 2-regular's GF-coeff drift) |

Dispatched after codex usage-limit reset (auto-bridged at 05:29). build green (8333 jobs), axioms clean.
This re-establishes genuine-combinatorial fidelity: the part-count law is proved equal to the uniform
distribution over the real Mathlib `Composition n` type, not posited.

### New work 2026-06-04 (Ch5 alignments — SEQ of CYC, F&S Ch V, HIGH FIDELITY)

| Theorem | F&S | Statement | Verdict |
|---------|-----|-----------|---------|
| `Alignments.alignmentCount_div_factorial_isEquivalent` | V | `o_n/n! ~ (1/(e-1))·(e/(e-1))^n` (ρ=1-1/e) | FAITHFUL — genuine class `alignmentClass.counts`, dominant simple pole of 1/(1-log(1/(1-z))) |
| `Alignments.alignmentEGFℂ_mul_denominator` | V | `alignmentEGF·(1-cycleEGF)=1` (SEQ-of-CYC) | FAITHFUL — ties to Ch2 genuine cycle EGF |

codex corrected the brief's wrong OEIS values (true A007840 = 1,1,3,14,88,694; ratios → 1). build green
(8334 jobs), axioms clean. Genuine-combinatorial fidelity (alignmentClass, not EGF-defined).

### Fidelity upgrade 2026-06-04 (2-regular → genuine combinatorial; closes the one flagged gap)

The earlier `twoRegularGraphCount` was GF-coefficient-defined (flagged as the weakest-fidelity result).
`TwoRegularClass.lean` now closes that gap:

| Theorem | Statement | Verdict |
|---------|-----------|---------|
| `TwoRegularClass.undirectedCycle_card_of_three_le` | `card(UndirectedCycle n) = (n-1)!/2` (k≥3) | FAITHFUL — directed cycle mod reversal |
| `TwoRegularClass.twoRegularClass_counts_eq_twoRegularGraphCount` | genuine `SET`-of-cycles count = old GF-coeff count | FAITHFUL — ties genuine class to the asymptotic |
| `TwoRegularClass.twoRegularClass_counts_div_factorial_isEquivalent` | `twoRegularClass.counts n /n! ~ e^{-3/4}/√(πn)` | FAITHFUL — asymptotic now for the GENUINE combinatorial count |

`twoRegularClass = SET` of undirected-cycle blocks (Ch2 SET-EGF machinery), EGF derived
= exp(-z/2-z²/4)/√(1-z). The audit closed its own flagged gap. build green; axioms clean.

## Summary (2026-06-04, this run)

Whole tree: 88 files, 0 sorry/admit/native_decide/custom-axiom; Audit.lean #print-axioms-certifies ~160
headline theorems = {propext, Classical.choice, Quot.sound}; full build green (8336 jobs).
Opened F&S Ch V (meromorphic transfer + surjections + alignments + supercrit-transfer), Ch VII (ternary,
Motzkin, general+p=4/5/6 Fuss-Catalan, 2-regular genuine), Ch IX (quasi-powers framework + binary-word +
cycle + composition-parts CLTs). 3 fidelity issues caught & fixed (Motzkin-v1 vacuous, quasi-powers hChar
over-strong, supercrit decorative hyps); 1 fidelity gap closed (2-regular). Whole book remains
multi-session (hard saddle/circle-method: Bell/partitions/Hardy-Ramanujan; more breadth; appendices).

## Summary update (2026-06-04 evening, continuation)

102→~115 files; certified headlines ~200+; build green (8364 jobs at last full verify); 0 sorry/admit/
native_decide/custom-axiom throughout. Major arcs COMPLETED this continuation:

**Goncharov–Kolchin (Ch IX), FULLY GENERAL, in distribution** — the crown of the run:
- r-cycles →d Poisson(1/r) (marginal, unconditional, end-to-end: factorial moments r^{-k} from first
  principles → bounded finite method-of-factorial-moments pmf inversion → reusable ℕ pmf⟹weak bridge).
- Bivariate (C_r,C_s) →weak Poisson⊗Poisson; GENERAL multivariate (C_{r_1},…,C_{r_m}) →weak ⨂Poisson(1/r_i)
  (Fin-m product measure; reusable ℕ×ℕ and (Fin m → ℕ) pmf⟹weak bridges — Mathlib-gap fillers).
- Joint factorial moments for arbitrary finite families = ∏ r^{-k_r} (indexed-family deletion bijections);
  E[#cycles]=H_n; Var(C_r)=1/r; Cov(C_r,C_s)=0.

**Random mappings arc (Ch II.3), substantially built**:
- Ramanujan Q-function: genuine def; Θ(√n) + sharp upper 1+√(πn/2); FULL Q ~ √(πn/2) (Laplace method for
  sums — new analytic technique for the repo).
- GENERALIZED CAYLEY FORMULA: #(forests of k rooted trees, specified roots) = k·n^{n-k-1} (fiber-equivalence
  induction + Abel-binomial engine); named Cayley corollary n^{n-2} (arborescence form).
- Connected mappings: periodic-core classification machinery + fixed-core fiber ≃ forests + single-cycle
  count (k-1)! all PROVED; global fiber-sum assembly (→ c_n = n^{n-1}Q(n) → P(connected) ~ √(π/(2n)))
  IN FLIGHT (codex usage-limit pause, auto-resumes 20:31).

Also: Fibonacci OGF Nat.fib(n+1) ~ φ^{n+1}/√5 (golden-ratio dominant pole); r-cycle exact pmf = Goncharov
inclusion-exclusion formula. Honest rejections: derangements →1/e (already Mathlib, re-wrapper refused).
Standard remains: every headline #print-axioms = {propext, Classical.choice, Quot.sound}; statement read
for fidelity; no def:Prop bundling; full build before banking.

## Summary update (2026-06-05, continuation cont'd)

~120 files; certified headlines ~235; build green (8375 jobs); standard unchanged (clean-3, 0 forbidden).
FIVE major completions this continuation:
1. **Goncharov–Kolchin, fully general, in distribution** (Ch IX): marginal/bivariate/multivariate product-
   Poisson weak convergence + all joint factorial moments + 3 reusable pmf⟹weak bridges.
2. **Random mappings sharp suite** (Ch II.3): Q ~ √(πn/2) (Laplace-for-sums), GENERALIZED CAYLEY k·n^{n-k-1}
   (+ n^{n-2} corollary), P(connected) ~ √(π/2n), E[#cyclic] = Q(n), E[#components] = Σ(n)_k/(k·n^k) ~ ½log n.
3. **LAGRANGE INVERSION** (famous Mathlib gap): implicit series T = X·φ(T) + self-built formal residue
   calculus + n·[Xⁿ]T = [X^{n-1}]φⁿ + Catalan/Cayley applications.
4. **PÓLYA ENUMERATION** (famous gap): fixed-coloring |C|^{#cycles}, unweighted PET, binary necklaces
   (gcd + φ forms), WEIGHTED cycle-index theorem.
5. Fibonacci golden-ratio asymptotic; cycle-statistics trio (H_n mean / Var / Cov).
Honest rejections/deferrals: derangements (already Mathlib), components sharp const (later closed), φ-form
(later closed). Hard frontiers remaining: Hardy–Ramanujan (circle method), general-β log transfer, Bell
bivariate block CLT, Mellin appendix, multivariate Ch IX beyond product-Poisson.

## Summary update (2026-06-05 mid-day)

62 banked deliverables; build green (8383 jobs); standard unchanged. New since last update:
- **FLAJOLET CONTINUED-FRACTION THEOREM, COMPLETE** (Ch V.4, famous): first-return recursion ⇒ finite
  J-fraction + the path-sum bridge (J-fraction coefficients = literal weighted Motzkin path Finset sums).
- **Bell block-count exact moments**: B_n := card(Finpartition univ) (genuine; Mathlib lacked it), Bell
  recurrence, Σ#blocks = B_{n+1}−B_n, E[#blocks] = B_{n+1}/B_n−1, B_{n+2}-second-moment, exact variance.
- **PARTITION CAMPAIGN** (route: HANDOFF/partition-campaign-route-R1.md, target log p(n) ~ π√(2n/3)):
  Milestone A ✓ (p(n) ≤ e^{π√(2n/3)}, elementary GF); B analytic-half ✓ (Euler-series Laplace limit → π²/6);
  Euler product bridge ✓ (bounded-partition equivalence, finite product identity, K-sandwich tendsto);
  B-closer (log + tsum_comm) in flight (codex outage #3 bridged, resumes 10:15); then C (reusable
  log-Tauberian — the central asset) and D (monotonicity transfer).
- ChatGPT Pro channel "ac" active for frontier route design (R1 delivered the partition route).
Outage protocol exercised 3×; sync protocol hardened (no stash -u with in-flight worker files; backup +
targeted rm + pull).

## ★ Milestone (2026-06-05 evening): HARDY–RAMANUJAN LOG-ASYMPTOTIC COMPLETE

partition_log_asymptotic: log p(n)/√n → π√(2/3) (+ IsEquivalent form), genuine card (Nat.Partition n),
clean-3, fully elementary (no circle method/modular forms). Pipeline (1 day): ChatGPT-R1 route → PARTA
(GF upper bound) → PARTB×3 (Euler product K-sandwich + Laplace t·log P → π²/6) → PARTC×3 (THE reusable
log-Tauberian: limsup/Abel/strong saddle gap/localization/liminf) → PARTD (monotone transfer). 67 banked
deliverables total; build green 8388 jobs. Remaining true frontier: the sharp HR constant (circle method).

## Summary update (2026-06-06, codex-outage period)

80 banked deliverables; build green (8401 jobs); standard unchanged. Codex weekly quota exhausted (resumes
Jun 10 7:27 PM); output sustained via Opus-solo + ChatGPT-draft/Opus-fix loop:
- Partition campaign COMPLETE earlier: log p(n) ~ π√(2n/3) + distinct/odd/Glaisher-m family.
- General compositions family COMPLETE (Perron gcd dominance + ρ_S asymptotic for every finite alphabet).
- HR-CONSTANT campaign (route R2 archived) Stage I progress: σ-recurrence ✓, divisor summatory (explicit
  K) ✓, normalized Erdős u-recurrence + boundary→0 ✓, kernel tail tightness ✓, summatory window-diff ✓,
  kernel density integral = 1 ✓, uniform window replacements ✓, HALF-OPEN WINDOW MASS LIMIT ✓
  ((S(β√n)−S(α√n))/n → (π²/12)(β²−α²)) + endpoint squeeze ✓.
  Remaining Stage I.3: summatory↔windowed-sum index bridge → weighted block squeeze → step assembly →
  window/total theorems; then I.4 boundedness, block propagation (b), Stage II Euler–Maclaurin, Stage III
  constant. Engine note: draft-loop lessons recorded in RUN_LOG (hλ parser trap, squeeze_zero_norm', ₀-renames).

## 2026-06-05/06 — HR Stage I.3 kernel package BANKED (clean-3 verified on uisai2)
- Erdos.Model.blockSum_eventually_between_mesh_eps — PASS clean-3
- Erdos.Model.mesh_endpoint_sums_approx_integral — PASS clean-3 (was the R4 draft's axiom; proved)
- Erdos.Model.model_kernel_window — PASS clean-3
- Erdos.Model.erdos_kernel_window — PASS clean-3 (true kernel)
- Erdos.Model.erdos_kernel_total — PASS clean-3 (kernel mass → 1)
- Partitions.part_mono — PASS clean-3
Gate: per-file lake env lean exit 0 + full lib build (8409 jobs, 0 sorryAx/ofReduceBool/trustCompiler)
+ Audit module build exit 0 with 157 clean-3 lines, on uisai2 (uisai1 outage; clone + cache bootstrap).

## 2026-06-06 — Stage I.5/I.6 opening bricks BANKED (clean-3 on uisai2, Audit exit 0, 0 dirty)
- Erdos.u_local_lower_from_monotone — PASS clean-3 (forward propagation; R6 lemma 14)
- Erdos.erdos_kernel_fixed_window_pos — PASS clean-3 (R6 lemma 2)
- Erdos.upperBarrier_eventually_pos_bdd / lowerBarrier_eventually_pos_bdd — PASS clean-3 (R6 lemma 3)
- Erdos.boundaryTerm_le_barrierSlack — PASS clean-3 (R6 lemma 7)
- Erdos.upperBarrier_gap_on_window / lowerBarrier_gap_on_window — PASS clean-3 (R6 lemma 4)
- Erdos.upperBarrier_kernel_superharmonic_of_rate / lowerBarrier_kernel_subharmonic_of_rate — PASS clean-3 (CONDITIONAL: o(slack) mass rate as explicit hypothesis)
- Erdos.upperBarrier_mono / lowerBarrier_anti / u_pos — PASS clean-3 (unconditional)
- Erdos.u_upper_of_superharmonic / u_limsup_finite_of_superharmonic — PASS clean-3 (conditional on harmonic hyp)
- Erdos.u_lower_of_subharmonic / u_liminf_positive_of_subharmonic — PASS clean-3 (conditional on harmonic hyp)
- Erdos.exists_highRecordFrom / exists_lowRecordFrom / u_tendsto_of_record_covers /
  erdos_limit_pos_of_tendsto / u_local_high_forward_fill — PASS clean-3 (R7 kernel-free layers)
- Erdos.massLam_sq / boseKernel_eq_exp_form / mass_rate_sqrt_coeff_cancel — PASS clean-3
  (mass-rate campaign opening, R8 route)
