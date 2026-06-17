# ROADMAP — singularity-analysis & transfer extensions (按图索骥)

Status legend: ☐ open · ◐ in progress (agent) · ☑ done (commit) · ⊘ blocked (external)

Each item = one NEW file, one writer (codex agent). Master (me) wires imports +
`#print axioms` in Audit.lean and commits after clean-3 verification. GitHub main only
gets build-green + 0 sorry/admit/native + axioms ⊆ {propext, Classical.choice, Quot.sound}.

## A. Hankel contour → explicit constants (deepening Ch4/VI) — serial chain
- ☑ **A1. Explicit model-coeff constant** [655ff14, via Γ-ratio+Bohr-Mollerup, NOT Hankel]
- (old A1 Hankel-full-expansion superseded by the Γ-ratio route)
- ~~Hankel model expansion~~: `[zⁿ](1-z)^{-α} = n^{α-1}/Γ(α)·(1 + a₁/n + a₂/n² + …)`
  with explicit `aₖ`. Build the keyhole/Hankel contour + the `∫e^{-u}u^{-α}du = Γ` step.
  (Design via ChatGPT first; then codex builds.) FOUNDATIONAL, LARGE. Blocks A2/A3.
- ☐ **A2. O-transfer**: residual `O(|1-z|^{-β})` ⟹ `[zⁿ]f = O(n^{β-1})` (big-O companion to
  the committed little-o transfers). Reuses A1's contour. MEDIUM.
- ☐ **A3. Second-order transfer**: explicit subdominant terms for existing applications. Needs A1.

## B. Other chapters — independent, parallelizable
- ☐ **B4. Supercritical sequence schema (F&S V.2)** `Ch5/Meromorphic/`: derive the
  principal-part decomposition from supercritical data (`F·(1−C)=1`, `C(ρ)=1`, `C'(ρ)≠0`,
  next singularity past R). Explicitly flagged "future work" in `SupercriticalSeq.lean`.
  SELF-CONTAINED.
- ☑ **B5. Fragmented permutations finite-radius saddle** [655ff14, first finite-radius H-admissible instance]
- ☐ **B5+. More H-admissible saddle-point structures** `Ch8/SaddlePoint/`: framework + Bell,
  Exp, Involution, Blocks3 done; add new GF classes (e.g. fragmented permutations
  `e^{z/(1-z)}`, set-of-cycles). MEDIUM each.
- ☐ **B6. More singularity-analysis limit laws** `Ch9/LimitLaws/`: apply the committed
  `QuasiPowers`→Gaussian engine to new parameters. SELF-CONTAINED each.
- ☐ **B7. More F&S VII applications** `Ch7/SingularityApp/`: classic singular-expansion
  classes. First target: **2-regular labelled graphs** — EGF `e^{-z/2-z²/4}·(1-z)^{-1/2}`,
  `aₙ/n! ~ e^{-3/4}/√(πn)` — exercises the α=1/2 (0<α<1) transfer (`TransferGeneral`) for a
  real combinatorial class. SMALL–MEDIUM each.
- ⊘ **B8. Literal Euler product for partitions** `∏(1−zᵏ)⁻¹` `Ch1/OGF/Partitions.lean`:
  BLOCKED on a Mathlib `GenFun` TODO (external). Not codex-dispatchable.

## Not free to pick up
- `Ch8/Partitions/` (Erdős partition / HR mass-rate, 218 files) = active campaign frontier.

## Dispatch plan (统筹)
- ChatGPT ac → A1 Hankel-contour design (long-think, overlaps).
- codex agents (parallel, one file each): B4, B7(2-regular), then B5/B6 as slots free.
- A1 build dispatched once ChatGPT design returns + verified.
(note: B7 2-regular already done at TwoRegularClass.twoRegularClass_counts_div_factorial_isEquivalent — pick a verified-open target)

## Verification log (repo is MORE complete than docstrings suggest — grep companions first!)
- B7 2-regular: ALREADY DONE — `TwoRegularClass.twoRegularClass_counts_div_factorial_isEquivalent`.
- α<1 transfer: ALREADY DONE — `coeff_norm_isLittleO_atTop_of_delta_littleO` (all real β) +
  `TransferGeneral.transfer_theorem` (all α∉{0,-1,…}).
- B4 supercritical V.2: ALREADY DONE — `SupercriticalSeqGenuine.{supercriticalSeq_decomposition,
  supercriticalSeq_isEquivalent}_from_supercritical_data` (commit d5b0241, clean, in Audit).
  `SupercriticalSeq.lean`'s "future work" docstring is STALE. Only an OPTIONAL formal-inverse
  bridge (`F=(1-C)⁻¹` from raw formal `C`, HasFPowerSeriesAt.inv-style) remains — marginal,
  possible Mathlib gap.
- ⇒ Genuine LIVE frontier: A1 (Hankel explicit constants — no contour yet) + B5 (fragmented-perm
  finite-radius saddle — no companion found). B6/B7 need deep companion-grep before dispatch.

## Post-A1/B5 verification (continuing the grep-first discipline)
- A2 (big-O transfer): ALREADY DONE — `coeff_norm_isBigO_atTop_of_delta_bound` (CoeffDescent.lean)
  + `coeff_norm_isBigO_atTop_of_delta_bound_beta_gt_one` (OTransfer.lean). Struck off.
- B6 (limit laws): engine + many apps ALREADY DONE — quasi-powers→Gaussian, RCycles Poisson,
  CompositionParts/BinaryWord/PermutationCycles Gaussian. No obvious clean gap without a new
  specific parameter target. Effectively complete.
- A3 (second-order / explicit subdominant expansion): GENUINELY OPEN — no second-order transfer
  exists; now enabled by A1's explicit O(1/n) constant. The one substantial remaining frontier.

## FINAL TALLY (today's roadmap)
- Newly proven + committed: A1 (655ff14), B5 (655ff14) = 2.
- Verified already-done: B4, B7, α<1, A2, (B6 engine) = ~5.
- Genuinely open: A3 (second-order, substantial). Blocked: B8 (Mathlib GenFun TODO).
- Conclusion: the transfer + limit-law infrastructure spans all regimes and is essentially complete;
  A3 (quantitative subdominant expansion) is the sole remaining substantial extension.
