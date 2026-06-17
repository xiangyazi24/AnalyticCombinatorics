# DOCTRINE — general logᵏ transfer capstone (automode)

## Main goal (one sentence)
Make the general logᵏ singularity hierarchy usable end-to-end: prove the logᵏ natural-remainder
transfer theorem `[zⁿ]f ~ C·n^{α-1}/Γα·(log n)ᵏ` and a genuine combinatorial application, all clean-3.

## State (already committed clean-3 on main)
- LogKCoeff (coeff identity), LogKFaithful (faithfulness/analyticity), LogKAsymp (scale k!·e_k~(log n)ᵏ).
- Kernel chunk DONE (uncommitted WIP in LittleOTransfer.lean): one_add_pow_le_pred_mul_one_add_of_le,
  circleKernelLogK_intervalIntegrable, circleKernelLogK_integral_bound_nat (k≥1). Compiles clean.
- Chunk 3 (LogKTransferNatural.lean) DRAFTED, builds once chunk 2's coeff wrapper exists.

## Avenues (ranked)
- (a) PRIMARY — generalize the committed log² transfer machinery 2→k, chunk by chunk:
      kernel [done] → bridge (exists_delta_littleO_kernel_bound_logK + transferCircleBoundLogK_isLittleO)
      → coeff wrapper (coeff_norm_isLittleO_..._logK) → transfer theorem [drafted] → application.
      Terminal success: all compile clean-3, committed. Failure: 3 concrete proof routes to the bridge fail
      with written verdicts.
- (b) If the bridge mirror is intractable: prove the logK coeff little-o by a different route — bound the
      weight at the coeff level (induct on k via the banked log¹ coeff little-o) instead of the integral level.
- (c) Fallback capstone: strong-remainder logK transfer (residual o(|1-z|^{-α}) → o(n^{α-1}logᵏn)),
      which reuses the banked no-log/log¹ kernel — no new logK integral kernel needed. A real (weaker) capstone.
- (d) Application: `cycleMarkedPermClass.lpow k` (k-tuple of marked-cycle perms), EGF
      log^k(1/(1-z))·(1-z)^{-k} = logKSingularityGF (k:ℂ) k ⟹ aₙ/n! ~ n^{k-1}/(k-1)!·(log n)ᵏ,
      via logK transfer at α=k, C=1, ZERO residual (f = logKSingularityFun exactly, hsing trivially 0).

## Fallbacks
If (a) bridge blocked → (b) coeff-level route → (c) strong-remainder capstone. Application (d) needs only
the chosen transfer theorem; if all transfer routes blocked, deliver (d) for fixed k=3 via direct k=3 kernel.

## Terminal conditions
SUCCESS = logK transfer theorem (natural or strong) + ≥1 application theorem, both clean-3, committed+pushed.
Per avenue: success = compiles clean-3; proof-of-failure = 3 written concrete-tactic verdicts.
