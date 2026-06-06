# Stage I.5 design — u boundedness (order-sharp polynomial factor)

Targets (route R2 step 5):
- `u_limsup_finite : ∃ M > 0, ∀ᶠ n in atTop, u n ≤ M`
- `u_liminf_positive : ∃ m > 0, ∀ᶠ n in atTop, m ≤ u n`
- corollary `partition_order_sharp`.

Banked inputs: `u_recurrence` (u n = Σ erdosWeight·u(n−m) + boundaryTerm),
`boundaryTerm_negligible`, `erdos_kernel_tail`, `erdos_kernel_window` (R5, pending),
`erdos_kernel_total` (drafted, pending R5), monotonicity `part` nondecreasing
(Partitions.part_mono if banked — CHECK), `sigmaR_le_square`, σ(m) ≤ m(1+log m) elementary
(NOT yet banked — useful lemma: sigmaR m = Σ_{d∣m} d = m·Σ_{d∣m} 1/d ≤ m·H_m ≤ m(1+log m)).

## Upper bound (limsup finite)

Classical Erdős induction does NOT close from kernel mass → 1 alone (mass 1+o(1) allows slow
growth). Standard repairs, in promise order:

(a) **Comparison/supersolution induction**: prove directly p(n) ≤ K·e^{C√n}/n for explicit K by
strong induction. Inductive step: n·p(n) = Σ_{m≤n} σ(m)·p(n−m) ≤ K·Σ σ(m) e^{C√(n−m)}/(n−m)
(+ boundary). Need the SHARP inequality Σ_{m} σ(m) e^{C√(n−m)}/(n−m) ≤ e^{C√n}·(1 − δ_n) with
δ_n ≥ 0 — equivalently kernel mass at the supersolution ≤ 1 EXACTLY (not just in the limit).
The slack comes from second-order terms: √(n−m) ≤ √n − m/(2√n) − m²/(8n^{3/2}) for m ≤ n/2
(concavity, exact: √(n−m) ≤ √n − m/(2√n) always since √ concave at n... sign: √n − √(n−m) =
m/(√n+√(n−m)) ≥ m/(2√n) ✓ — gives e^{−C(√n−√(n−m))} ≤ e^{−(C/2)m/√n} for free!). So kernel mass
≤ (1/(n−m))-weighted geometric-type sum; compare against ∫ with the SAME inequality direction.
Check whether Σ_{m=1}^{n−1} σ(m) e^{−(C/2)m/√n}/(n−m) ≤ 1 + error with explicit error and
whether the induction tolerates 1 + O(n^{−1/4})-type error by taking u n ≤ M·(1 + Σ ε_k)-style
telescoping product (Π (1+ε_k) converges iff Σ ε_k < ∞ — need error summable: O(1/n^{5/4})?
The window analysis gives mass = 1 + O(n^{−1/2}·log n)? NOT summable. Need care: use
m-monotonicity trick (Erdős): induct on u over blocks of length √n, M_j = max over block j;
recurrence gives M_{j+1} ≤ M_j(1+ε_j) with ε_j summable over BLOCKS (j ~ √n blocks, ε_j ~ 2^{-j}?
no...). FLAG: this needs the genuine Erdős bookkeeping; treat as the hard core, single
coherent deep-dive (no parallel codex).

(b) **Crude two-sided first** (weaker but immediate): from banked log-asymptotic
log p(n)/√n → C we get p(n) ≤ e^{(C+ε)√n} eventually — NOT enough for u ≤ M (needs the
polynomial factor). Skip.

The honest status: I.5 upper is genuinely hard; Erdős's own paper proves upper+lower
simultaneously via the block-propagation machinery of I.6. Likely correct plan: do I.5+I.6
together in the renewal-theorem framework (one campaign), not piecemeal.

## Lower bound (liminf positive)

From recurrence + window: u n ≥ Σ_{window} W(n,m)·u(n−m) ≥ (window mass ≥ μ > 0 eventually) ·
min_{block} u. Propagation forward via u_local_lower_from_monotone (route step 6 lemma; needs
part monotone — elementary: p nondecreasing since every partition of n extends... p(n) ≤ p(n+1)
by adding a part 1; CHECK banked). Block min recursion m_{j+1} ≥ μ'·m_j has geometric decay —
not enough alone; need mass-concentration argument again. Same conclusion: I.5/I.6 one campaign.

## Action

Next ChatGPT round (R6, after R5 lands & banks): ask for the FULL I.5+I.6 renewal/block plan as
one route map with Lean-statement granularity (not code), then brick it.

## 2026-06-06 budget check (Opus): the mass-rate brick is unavoidable and hard

Superharmonic needs |kernelMass n − 1| ≲ slack = 1/(√n log²(n+E)).
- Abel summation of erdosWeight against S(t) = Σ_{m≤t}σ(m) with the BANKED error O(t log t)
  gives only |mass − 1| = O(log n/√n)  (∫|φ'|·t log t ~ (1/n√n)·n log n).
- No barrier shape can absorb O(log n/√n): per-block error ~ log j/j, Σ log j/j diverges;
  any bounded barrier has finite total drift budget. Checked for 1−A/log^j, 1−A/n^α.
- Hence R6 lemma 1's cancellation claim is the real content: need
  (i) σ-summatory SECOND-order: S(x) = π²x²/12 − x/2·(?) + O(x^{2/3}·polylog) (hyperbola refinement),
  (ii) kernel second-order expansion (exponent m²-correction + 1/(n−m) expansion),
  (iii) the 1/√n contributions cancel pairwise, leaving O(log n/n).
  Multi-brick campaign; dispatch as R8 with this budget analysis attached.
