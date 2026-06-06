# M₂ reg3 (0,1] bound — degree-8 cancellation certificate

## Goal
`reg3_bdd_near_zero {z} (0<z) (z≤1) : |boseKernel3 z − 6/z⁴| ≤ C₃` (C₃ ≈ 3500 OK; constant irrelevant, only feeds keystone Cf).

This is the ONLY missing input for M₂ weak asymptotics. Once done:
`sigmaMoment_two_asymp_weak : |M₂ t − 6(π²/6)/t⁴| ≤ K/t³` via
`weighted_decay_sum_bound 2 (fun z => boseKernel3 z − 6/z⁴) C₃ B₃ 6 ...` (j=2, p=4)
+ main term Σ k²·6/(tk)⁴ = 6Z/t⁴ (tsum_if_inv_sq scaled).

## reg3 structure (verified, sympy)
- reg3 = boseKernel3 − 6/z⁴ = N₃/(z⁴ w⁴), w := 1−e^{−z}, w ≥ z/2 (one_sub_exp_neg_ge_half).
- N₃ = z⁴(6 − 12w + 7w² − w³) − 6w⁴   [= z⁴(1−w)(6−6w+w²) − 6w⁴].
- denominator z⁴w⁴ ≥ z⁸/16, so |reg3| ≤ 16|N₃|/z⁸.
- reg3 near 0 = 1/120 − z²/504 + O(z⁴)  (bounded — cancellation real).

## Certificate (degree-8)
- P := z − z²/2 + z³/6 − z⁴/24 + z⁵/120 − z⁶/720 + z⁷/5040  (order-7 Taylor of w).
- δ := w − P,  |δ| ≤ z⁸  (need order-8 exp bound: |1−e^{−z} − P| ≤ z⁸ on [0,1], via Real.exp_bound n=8, mirror of #100 exp_sub_one_order4_bound).
- ring identity (w=P+δ): N₃ = A0 + δ·A1 + δ²·A2 + δ³·A3 − 6·δ⁴, where A0 = z⁸·Q.
  - Q: deg 20, Σ|coeff| = 0.0589
  - A1: lowdeg 3, deg 21, Σ|coeff| = 76.84
  - A2: lowdeg 2, deg 14, Σ|coeff| = 94.13
  - A3: lowdeg 1, deg 7,  Σ|coeff| = 40.24
- bound: |N₃| ≤ z⁸(Σ|Q|+Σ|A1|+Σ|A2|+Σ|A3|+6) = 217.27 z⁸ (each |δ|^p ≤ z⁸ since |δ|≤z⁸≤1; each |Aᵢ(z)| ≤ Σ|coeff| since zⁱ≤1 on (0,1]).
- ⟹ |reg3| ≤ 16·217.27 ≈ 3477.  Use C₃ = 3500.

## tail (easy, no certificate)
`reg3_tail {z} (1<z) : |boseKernel3 z − 6/z⁴| ≤ B₃·e^{−z/2} + 6/z⁴`
via boseKernel3_le (a=1): boseKernel3 z ≤ 6e^{−z}/(1−e^{−1})⁴ ≤ B₃ e^{−z/2} (e^{−z}≤e^{−z/2}), B₃=6/(1−e^{−1})⁴; |reg3|≤boseKernel3+6/z⁴ (triangle).

## Lean encoding note
The painful part is |Aᵢ(z)| ≤ Σ|coeff| for degree-20 polys (manual triangle, ~21 abs_add steps each) — sympy can EMIT the explicit A0..A3 Lean exprs + calc chains. The `ring` for the N₃ identity is degree-28, needs high maxHeartbeats. Good codex candidate (long mechanical) when it returns 6/10; or grind solo via sympy-emitted Lean.
