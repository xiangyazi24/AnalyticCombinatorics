# DOCTRINE — third-order quantitative layer: instances + completion

**Main goal (one sentence):** Make the abstract third-order saddle theorem
`coeff_thirdOrder_saddle` (T4, landed 6c02d7c) CONCRETE by building clean-3
third-order instances mirroring the existing second-order instance suite, give
Fuss-Catalan named third-order corollaries, and close any remaining quantitative
gaps — all axioms ⊆ {propext, Classical.choice, Quot.sound}, 0 sorry/admit/native_decide.

## Avenues (ranked)

### (a) Involution third-order instance — HIGHEST PROMISE
`involution_count_over_factorial_thirdOrder`: nₙ/n! third-order, δ₂ = 1/(72 n²)
(VERIFIED: f=e^{z+z²/2}, bₖ=r+2^{k-1}r², r(1+r)=n → δ₂→1/72n²; numeric residual→1).
Build on `InvolutionSecondOrder` + `InvolutionHAdmissible` + `coeff_thirdOrder_saddle`.
Discharge b5,b6, corrScale3, local_third_L1 (vs saddleThirdPoly), tail_third_uniform.
Entire function (infinite radius) ⇒ tail is clean. Terminal: clean-3 theorem OR
documented exact hypothesis that won't discharge + the failing tactic chain.

### (b) Bell + Blocks3 third-order instances (set partitions)
`bell_number_over_factorial_thirdOrder`, `blocks3_..._thirdOrder`. f=e^{e^z−1} (Bell).
Need bₖ(r) for set partitions + δ₂ value (ChatGPT derives, I verify numerically vs
exact Bell numbers). Extend BellSecondOrder/Blocks3SecondOrder to saddleThirdPoly.

### (c) Fuss-Catalan named third-order corollaries
Catalan (p=2, δ relative c₂=145/128), ternary (p=3, c₂=3145/10368) as named instances
of `fussCatalanGeneral_relative_thirdOrder`. Cheap corollaries; cross-check constants.

### (d) Repo-wide quantitative-gap survey
grep sorry/admit/placeholder across Ch4/Ch7/Ch8; close any genuine remaining gap in
the quantitative layer (documented gaps from earlier campaign: re-check each).

### (e) STRETCH — fourth-order saddle (δ₃) and/or √-meta fourth order
Only if (a)-(d) exhaust. δ₃ via the same Wick expansion (b^{-3} grade).

## Fallbacks
If instance-building stalls (a hypothesis genuinely can't be discharged), document
the exact blocker, move to next avenue. (d) is always available as productive work.

## Terminal conditions
Each instance: clean-3 theorem landed on origin/main, OR a written proof-of-failure
(the specific limit/integral that resists + the concrete tactic chain tried).
Run ends only when all avenues have terminal verdicts in RUN_LOG.

## Coordination (统筹: keep codex×2 + ac + ac2 all rolling)
- codex (single coherent per instance; parallel only across INDEPENDENT instances).
- ac/ac2: derive per-function saddle data (bₖ, δ₂) + audit hypothesis discharge;
  I verify numerically + in Lean. No effort caps in any brief.
- Land each instance with fresh-origin/main-checkout verification (build clone was
  stale once — see feedback_build_clone_staleness).
