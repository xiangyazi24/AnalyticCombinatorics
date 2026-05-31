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

## Round 2/3 — decide after API survey + codex review

Decide: A1 model; R1 (powers/tsum) vs R2 (direct/Mathlib); stage (counts layer first,
EGF/exp second). Flagship corollary: `SET(Z) = e^z` (already have via setClass);
later Bell `SET(SET_{≥1})`, etc. Anchor on `Fintype.card`; no banking.
