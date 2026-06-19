# Quantitative singularity-analysis + saddle-point campaign — remaining checklist

Watch these clear one-by-one. Legend: [ ] open · [◐] in progress · [x] done (commit) · [⊘] skip.

## Already done (committed, clean-3) — reference
general-α 2nd-order transfer; √-family 2nd-order (Motzkin/Catalan/Schröder/Riordan/ternary/Cayley);
√-family 3rd-order (Motzkin/Catalan/Schröder/Riordan/ternary); 2nd & 3rd-order √-meta-applicators;
3rd-order model expansion; abstract 2nd-order saddle theorem; saddle instances involutions/Bell/Blocks3.
(~21 theorems, 11 commits.)

## REMAINING
- [ ] T1. Cayley THIRD-order count. (Cayley has 2nd-order via Stirling; extend to 3rd.) FEASIBLE.
- [ ] T2. Fragmented-perm finite-radius SECOND-order. WIP: 1 sorry = the finite-radius 2nd-order tail
       estimate (ρ=1, saddle r→1⁻). HARD (the design flagged finite-radius as the hardest regime).
- [ ] T3. Fuss-Catalan-general UNCONDITIONAL. Discharge the two-term Puiseux of B=1+zB^p at the branch
       point — needs a ramified/Puiseux analytic-inverse theorem, currently ABSENT from Mathlib. HARD/gap.
- [ ] T4. THIRD-order saddle-point layer. Extend the abstract 2nd-order saddle theorem to 3rd order
       (next Hermite-moment term), + one instance. SUBSTANTIAL (optional).
- [⊘] Exp 2nd-order: SKIP — [zⁿ]e^z = 1/n! exact, no asymptotic content.

## Plan
Clear T1 first (feasible). Then T2 (finite-radius 2nd-order, attack the tail). T3 needs the ramified-inverse
(Mathlib-level; attempt or document as a true gap). T4 optional after T1-T3.
