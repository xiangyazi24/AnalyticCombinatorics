# Ch2 SET construction (labelled) — design (three rounds)

Goal (F&S Theorem II.2, labelled): for a class `C` with `C₀=∅` (`C.counts 0 = 0`),

  **`SET(C)(z) = exp(C(z)) = ∑_{k≥0} C(z)^k / k!`** (EGF; the exponential formula).

`SET(C)` = sets (unordered collections) of labelled C-objects, i.e. a set partition
of the `n` labels with each block carrying a C-structure. Generalizes the set class
(`C` = single atom of each size? no): for `C = Z` (one atom), `SET(Z)(z) = e^z`
(our `setClass` flagship, already proved as `egf_setClass`).

## Key reduction

`SET(C)ₙ = ∑_{π : set partition of [n]} ∏_{B∈π} C_{|B|}` (the exponential / set-partition
formula). The EGF is `exp(C(z))`. Two candidate routes to the OGF identity:

- **(R1) blocks-as-powers:** `SET(C) = ⊎_k SET_{=k}(C)`, `SET_{=k}(C) = C^{⋆k}/k!`
  (k unordered blocks), so `SET(C)(z) = ∑_k C(z)^k/k! = exp(C(z))`. Needs the k!
  unordering and the tsum `∑_k C.egf^k/k!`, then `= subst C.egf (exp ℚ)` (substitute
  X ↦ C.egf in `e^X`).
- **(R2) direct exponential formula:** bijection set-partition-decorated ↔
  `coeff` of `exp(C(z))`. Likely via Mathlib's set-partition / Bell machinery if any.

## Round 1 — atoms (unknowns for codex/grep)

| # | atom | question |
|---|---|---|
| A1 | set-partition type with Fintype | Mathlib `Finpartition (univ : Finset (Fin n))`? `Setoid.IsPartition`? Fintype, `parts`, block sizes, `card`. |
| A2 | `SET(C).Obj n` model | `Σ π, Π B∈π.parts, C.Obj |B|` — Fintype? (Finpartition Fintype + Pi over parts) |
| A3 | `counts_set = ∑_π ∏_B C_{|B|}` | card_sigma/card_pi over Finpartition.parts |
| A4 | exp-substitution `exp(C(z))` | `PowerSeries.subst C.egf (PowerSeries.exp ℚ)`; `HasSubst` needs `constantCoeff C.egf = 0` (✓ from C₀=0); `coeff_subst` / `coeff (subst …)` API |
| A5 | the exponential formula | does Mathlib have a set-partition GF / exponential-formula result? (Bell numbers `exp(e^z-1)`?) Or build via R1's tsum of powers? |
| A6 | tsum `∑'_k C.egf^k/k!` (if R1) | summability (order→∞ since C₀=0 ⇒ order C.egf ≥1 ⇒ order C.egf^k ≥ k); `= subst C.egf exp` |

Hardest: **A5/A6** — connecting the set-partition count to `exp` (the genuine new
content; comparable to MSET-2's `genFun` connection but for labelled/exp).

## Round 3 — DECISION (codex/gpt-5.5 verdict + verified Mathlib lemmas)

codex (second model) verdict: model faithful (use subtype `(B : π.parts) → C.Obj B.1.card`,
NOT `Π B in π.parts` — avoids outside-support trivial factors). **Use the differential
route R3, not R1/R2** (avoids `log`, the `∑ C^k/k!` tsum, and Bell polynomials):

**R3 plan (`SET(C).egf = (exp ℚ).subst C.egf`):**
1. counts layer DONE (`LabelledSet.lean`, `counts_set`).
2. `subst_exp_ode` (GENERAL, easy): `d⁄dX ℚ ((exp ℚ).subst C.egf) = d⁄dX ℚ C.egf * (exp ℚ).subst C.egf`,
   via `derivative_subst hsub` + `derivative_exp`. `hsub : HasSubst C.egf` from
   `HasSubst.of_constantCoeff_zero'` (constantCoeff C.egf = C₀/0! = 0).
3. `ode_unique` (GENERAL, easy): `d⁄dX ℚ H = G*H ∧ constantCoeff H = 0 → H = 0`
   by `Nat.strong_induction_on` on `coeff n H` (`coeff_derivative` + `coeff_mul` + `mul_eq_zero`).
4. **`SET(C).egf' = C.egf' * SET(C).egf` (HARD combinatorial ODE)**: the pointing
   bijection on `Finpartition` — the block containing the last label `n` has size i+1
   (a C-structure), the rest is `SET(C)` on the other `n-i` labels (relabel via
   `Finpartition` transport). Counts recurrence `SET_{n+1} = ∑_i C(n,i)·C_{i+1}·SET_{n-i}`.
   THIS is the remaining hard work (Finpartition pointing + relabel; ~MSET-2 scale).
5. constantCoeff SET.egf = 1 (empty partition); apply `ode_unique` to `SET.egf - subst exp`.

**Verified Mathlib (uisai1):** `Finpartition s` Fintype; `PowerSeries.subst`/`substAlgHom`
(AlgHom: `subst_mul`/`subst_add`/`subst_pow`); `HasSubst.of_constantCoeff_zero'`;
`constantCoeff_subst`; `derivative_subst {f g}(hg:HasSubst g): d⁄dX A (f.subst g) =
(d⁄dX A f).subst g * d⁄dX A g`; `derivative_exp : d⁄dX A (exp A) = exp A`;
`coeff_derivative (f)(n): coeff n (d⁄dX f) = coeff(n+1) f * (n+1)`;
`exp_unique_of_derivative_eq_self` (for f'=f). NO Bell / exponential formula in Mathlib.
