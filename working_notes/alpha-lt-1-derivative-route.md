# α<1 transfer via the derivative route (ChatGPT ac R1, verified)

## Why not the circle bound
For 0<α<1 the absolute Cauchy-circle kernel ∫|1-r e^{iθ}|^{-α}dθ loses n^{α-1}:
the near-θ=0 piece is O(ρ^{1-α}) (good, ρ=1/n) but the COMPLEMENT ∫_{ρ<|θ|≤π}|θ|^{-α}dθ = O(1)
(integrable singularity). No radius rescues it. The true small coeff comes from branch
cancellation that ‖·‖ erases. So a direct α<1 proof needs Hankel — UNLESS we differentiate.

## Derivative route (avoids Hankel, reuses committed β>1 transfer)
If residual f = o(|1-z|^{-α}) on Δ (0<α<1), then on a smaller Δ:
  f'(z) = o(|1-z|^{-(α+1)}),  β := α+1 > 1.
Apply the COMMITTED β>1 transfer to f' ⟹ [zⁿ]f' = o(n^α). Since [zⁿ]f' = (n+1)[z^{n+1}]f,
shifting the index gives [zⁿ]f = o(n^{α-1}).  □

## Two new lemmas (the only new work)
1. delta_littleO_deriv_of_delta_littleO: o(|1-z|^{-α}) on Δ R φ ⟹ o(|1-z|^{-(α+1)}) on Δ R' φ'.
   Mechanism: Cauchy deriv estimate |f'(z)| ≤ (1/r_z)·sup_{|w-z|=r_z}|f(w)|, r_z ≍ |1-z|.
   On the local disk |1-w| ≍ |1-z| and disk ⊂ larger Δ ⇒ ε|1-z|^{-α} bumps to ε|1-z|^{-(α+1)}.
   TOOLING EXISTS in DeltaGeometry.lean: ball z (κ·‖1-z‖) ⊆ DeltaDomainArg R φ (κ = the
   `n R R' φ φ'` radius fn), plus norm-comparability lemmas (verified present 8e16305+cert).
2. coeff_littleO_of_deriv_coeff_littleO: p'.coeff n = (n+1)•p.coeff(n+1) ∧ ‖p'.coeff‖=o(n^α)
   ⟹ ‖p.coeff‖ = o(n^{α-1}).

## Then: α<1 transfer theorem + an application (e.g. (1-z)^{-1/2} class ~ n^{-1/2}/Γ(1/2)).
ChatGPT recommends derivative route over Hankel: smaller, reuses committed β>1, matches file arch.
