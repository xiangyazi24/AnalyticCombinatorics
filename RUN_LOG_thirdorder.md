## Run 2026-06-19 (automode, Xiang asleep, pre-approved)
- doctrine: DOCTRINE_thirdorder_instances.md
- base: origin/main 232e512 (T1-T4 landed, repo clean-3)
- outstanding map: saddle-family 3rd-order instances missing (Involution/Bell/Blocks3/FragmentedPerm/Product/TwoRegular); √-family 3rd done
- starting avenue: (a) Involution-3rd + (b) Bell-3rd in parallel

### Avenue verdict: integer partitions p(n) THIRD-order — DOCUMENTED GAP (not attempted in Lean)
p(n)=e^ν/(4√3·N)(1-1/ν), N=n-1/24, ν=π√(2N/3); or e^μ/(4√3 n)(1-(1+π²/72)/μ+(π²/24+π⁴/10368)/μ²).
Constants confirmed numerically vs exact p(n). TERMINAL VERDICT: rigorous Lean third-order needs
Dedekind-eta modularity + minor-arc/tail control (a major ANT formalization Mathlib lacks) — out of
scope for the saddle-instance run; same class as the Ch1/Ch9 modularity/Euler-product gaps. Not 退堂鼓:
concrete infra dependency, documented. TwoRegular (√-route) IS tractable and queued.

## Run COMPLETE 2026-06-20 (automode, overnight)
THIRD-ORDER INSTANCE SUITE — landed on origin/main, all clean-3 (axioms ⊆ {propext, Classical.choice, Quot.sound}):
  - Involution   489a910  (δ₂=1/72n²)         entire saddle, coeff_thirdOrder_saddle instance
  - Bell         82a380f  (bₖ=e^r T_k(r))     entire saddle
  - Blocks3      6bbc6e2  (bₖ=r+2^{k-1}r²+3^{k-1}r³/2)  entire saddle
  - TwoRegular   b9ac39e  (n^{-1/2}(a₀+a₁/n+a₂/n²))  √-singularity (1-z)^{-1/2} route
  - FragmentedPerm 8360f5f (δ₂~-15/512n)      FINITE-RADIUS saddle, narrow-window apparatus + sliver tail
DOCUMENTED TERMINAL GAP: integer partitions / Product (∏1/(1-q^k)) — rigorous 3rd order needs
  Dedekind-eta modularity / Rademacher / minor-arc control (Mathlib lacks); constants verified, not a saddle instance.
VERIFICATION: 6 families numerically confirmed (residual/δ₂→1); δ₂ formula + exp(g) bₖ recipe cross-checked
  by 2 independent ChatGPT derivations + numerics. 2 premature codex "done"s caught by trust-but-verify
  (2reg3 compile errors, frag3 missing assembly) → re-dispatched and completed.
The third-order suite now matches the second-order suite exactly, except the documented partition gap.
