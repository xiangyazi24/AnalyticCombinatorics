# R7 convergence: renewal / harmonic-Markov-chain route (ChatGPT b0f6ab89, 06-06)

Records are abandoned (1/μ amplification proven intrinsic, see r7-amplification-obstruction.md).
New route: u as approximately harmonic for a decreasing Markov chain on the √n scale. DETERMINISTIC
Lean (no probability measures) via Hit/Pot potentials.

## Layer 1 — kernel normalization
  S n      := ∑' m, erdosWeight n m          (= kernelMass n; have kernelMass_sub_one_rate |S−1|≤K/n)
  P n k    := if k < n then erdosWeight n (n−k) / S n else 0     (prob kernel on predecessors k<n)
  d n      := u n − ∑' k, P n k · u k                            (residual)
  d_bound:   |d n| ≤ |b n| + M·|S n − 1|         (the (1−w) near-complement cancels against u·S; NOT in d)
  d_block_summable: ∃ e≥0 Summable, ∀ᶠ n |d n| ≤ e(rank n), rank n = Nat.sqrt n.
             e(j) = O(1/j²)+exp-small  ⟸ DefectSummable (summable_defect_scale), BANKED clean-3.

## Layer 2 — abstract deterministic potentials (well-founded on n, P n k=0 unless k<n)
  Hit J φ n := if rank n < J then φ n else ∑' k, P n k · Hit J φ k
  Pot J e n := if rank n < J then 0   else e (rank n) + ∑' k, P n k · Pot J e k
  rec_iter_bound:  |d n| ≤ e(rank n)  ⟹  |u n − Hit J u n| ≤ Pot J e n   (strong induction on n)

## Layer 3 — occupation ⟹ potential tail  [HARD ANALYTIC FACT A, isolate]
  ExpectedVisitsBeforeCutoff P rank J n ℓ ≤ B  (uniform renewal-density bound)
  ⟹ Pot J e n ≤ B · ∑' r, e (J+r)   (= B·tail_e J → 0 since Summable e)

## Layer 4 — hitting/overshoot convergence  [HARD ANALYTIC FACT B, isolate]
  ∀ J, ∀ bounded φ on {rank<J},  Hit J φ n  → L_J  as n→∞   (non-lattice renewal overshoot)

## Layer 5 — convergence (abstract spine, takes A,B as hypotheses)
  For fixed J: |u n − Hit J u n| ≤ B·tail_e J; Hit J u n → L_J ⟹ limsup u − liminf u ≤ 2B·tail_e J.
  J→∞ (tail_e→0) ⟹ limsup u = liminf u ⟹ ∃L Tendsto u atTop (𝓝 L).
  Positivity from u_liminf_positive (BANKED). ⟹ erdos_partition_limit_exists.

## Kernel analytic facts (Facts A,B from the Gamma(2,C) limit law)
  √n-decrement Y_n=√n−√(n−m), m=y√n ⟹ Y_n=y/2+O(y²/√n); limit density g(s)=(2π²/3)s e^{−Cs}
  (Gamma shape 2 rate C, mean 2/C, NON-LATTICE — continuous density). Required: P normalized;
  uniform exp tail P_n(Y≥R)≤Ae^{−λR}; no tiny jumps P_n(Y≤ρ)≤Aρ²+o(1); local-limit to g;
  ⟹ A (occupation) and B (overshoot). These are the renewal-theory analytic core (hardest).

## Build order
  1. Abstract spine: Layers 2+5 as a standalone theorem `triangular_renewal_convergence`
     taking (hrec, herr_block summable, hoccupation, hhitting) as hypotheses → ∃L Tendsto.
     DESIGN-INDEPENDENT, verifiable clean-3 NOW. (Layer-2 Hit/Pot recursion + Layer-5 osc collapse.)
  2. Layer 1 (normalization, d_bound, d_block_summable via DefectSummable) — concrete.
  3. Facts A,B (renewal kernel theorem) — hard analytic, separate file, from Gamma(2,C) limit.
  4. erdos_partition_limit_exists := spine applied to the partition kernel.
Banked clean-3 already reusable: DefectSummable, u_limsup_finite, u_liminf_positive, kernelMass_sub_one_rate.
